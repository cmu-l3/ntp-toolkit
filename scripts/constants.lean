import Mathlib.Lean.CoreM
import Mathlib.Control.Basic
import Mathlib.Lean.Expr.Basic
import Batteries.Lean.HashMap
import Batteries.Lean.Util.Path
import DocGen4.Process

/-!
Generate constant names and types.
-/

open Lean Meta DocGen4.Process

def argToString (arg : Arg) : String :=
  let (l, r) := match arg.binderInfo with
  | BinderInfo.default => ("(", ")")
  | BinderInfo.implicit => ("{", "}")
  | BinderInfo.strictImplicit => ("⦃", "⦄")
  | BinderInfo.instImplicit => ("[", "]")
  let n := match arg.name with
    | some name => s!"{name.toString} : "
    | none => ""
  s!"{l}{n}{arg.type.stripTags}{r}"

/--
Wrapper around `Lean.findDeclarationRanges?` that tries harder to find a range
-/
def findDeclarationRanges! [Monad m] [MonadEnv m] [MonadLiftT BaseIO m]
    (name : Name) : m DeclarationRanges := do
  match ← findDeclarationRanges? name with
  | some range => pure range
  | none =>
    match name with
    | .str p _ | .num p _ =>
      -- If declaration range of e.g. `Nat.noConfusionType` could not be found, try prefix `Nat` instead.
      findDeclarationRanges! p
    | .anonymous =>
      -- If a declaration range could not be found with recursion above, use the default range (all 0)
      pure default

namespace DocGen4.Process

open DocGen4 DocGen4.Process DocGen4.Process.DocInfo

/--
Modified version of `prettyPrintTerm` (changed width to 1000000000)
-/
def prettyPrintTerm' (expr : Expr) : MetaM Widget.CodeWithInfos := do
  let ⟨fmt, infos⟩ ← PrettyPrinter.ppExprWithInfos expr
  let tt := Widget.TaggedText.prettyTagged fmt (w := 1000000000)
  let ctx := {
    env := ← getEnv
    mctx := ← getMCtx
    options := ← getOptions
    currNamespace := ← getCurrNamespace
    openDecls := ← getOpenDecls
    fileMap := default,
    ngen := ← getNGen
  }
  return Widget.tagCodeInfos ctx infos tt

/-- Modified version of `NameInfo.ofTypedName` (changed pretty printing) -/
def NameInfo.ofTypedName' (n : Name) (t : Expr) : MetaM NameInfo := do
  let env ← getEnv
  return { name := n, type := ← prettyPrintTerm' t, doc := ← findDocString? env n}

/--
Modified version of `Info.ofConstantVal`:
* Changed rendering width to 1000000000
* Suppressed error when declaration range is none
* Changed findDeclarationRanges? to findDeclarationRanges!
-/
def Info.ofConstantVal' (v : ConstantVal) : MetaM Info := do
  argTypeTelescope v.type fun args type => do
    let args ← args.mapM (fun (n, e, b) => do return Arg.mk n (← prettyPrintTerm' e) b)
    let nameInfo ← NameInfo.ofTypedName' v.name type
    let range ← findDeclarationRanges! v.name
    return {
      toNameInfo := nameInfo,
      args,
      declarationRange := range.range,
      attrs := ← getAllAttributes v.name
    }

/--
Returns kind (string) and Info given constant.
Simplified version of `DocInfo.getKind`, `DocInfo.ofConstant`.
-/
def infoOfConstant (cinfo : ConstantInfo) : MetaM (String × Info) := do
  let env ← getEnv
  let kind : String :=
    match cinfo with
    | .axiomInfo _ => "axiom"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .defnInfo i =>
      if isInstanceCore env i.name then
        "instance"
      else
        "def"
    | .inductInfo i =>
      if isClass env i.name then
        "class"
      else if isStructure env i.name then
        "structure"
      else
        "inductive"
    | .ctorInfo _ => "def"
    | .recInfo _ => "def"
    | .quotInfo _ => "def"
  -- TODO: record if it is e.g. ctor, opaque, induct etc (not accepted by duper)
  return (kind, ← Info.ofConstantVal' cinfo.toConstantVal)

end DocGen4.Process

/-- Pretty-prints a constant to JSON -/
def constantInfoToJson (cinfo : ConstantInfo) : MetaM Json := do
  let (kind, info) ← infoOfConstant cinfo
  let name := cinfo.name.toString
  let args := info.args.map argToString
  let type := info.type.stripTags
  let doc? := info.doc

  -- format declaration into `decl`
  let mut decl := ""
  if let some doc := doc? then
    decl := decl ++ "/-- " ++ doc.stripSuffix " " ++ " -/\n"
  decl := decl ++ kind ++ " "
  decl := decl ++ name ++ " "
  for arg in args do
    decl := decl ++ arg ++ " "
  decl := decl ++ ": " ++ type

  return Json.mkObj [
    ("name", Json.str name),
    ("kind", Json.str kind),
    ("args", Json.arr (args.map .str)),
    ("type", Json.str type),
    ("doc", match doc? with
      | some doc => Json.str doc
      | none => Json.null),
    ("decl", Json.str decl),
    ("line", Json.num info.declarationRange.pos.line),
    ("column", Json.num info.declarationRange.pos.column),
  ]

/-- If a constant should not be included. -/
def isBlackListedName (name : Name) : Bool :=
  -- We should do this during postprocessing?
  -- match name.components with
  -- | `Lean :: _ => true
  -- | `Lake :: _ => true
  -- | `Qq :: _ => true
  -- | `Aesop :: _ => true
  -- | `Cli :: _ => true
  -- | _ =>
  name.isInternalDetail

/--
Traverse all constants from modules, collecting prettified declarations
Calls callback on each extracted constant.
(Should convert to MLList instead of callback?)
-/
def allConstants (moduleNames : Array Name) (callback : Nat → Nat → Name → Json → MetaM Unit) :
    MetaM Unit := do
  let env ← getEnv
  let constantsMap := env.constants.map₁
  let total := constantsMap.size
  let mut i := 0
  for (name, cinfo) in constantsMap do
    if !isBlackListedName name then
      if let some moduleIdx := env.getModuleIdxFor? name then
        if let some moduleName := env.header.moduleNames[moduleIdx.toNat]? then
          if moduleNames.contains moduleName then
            try
              let json ← constantInfoToJson cinfo
              callback i total name json
            catch _ =>
              -- Extremely rare cases (e.g. Fin.eq_of_val_eq, Qq.Quoted.unsafeMk)
              IO.eprintln s!"warning: failed to extract constant {name}"
              continue
    i := i + 1

def main (args : List String) : IO UInt32 := do
  let options := Options.empty.insert `maxHeartbeats (0 : Nat)
  let modules := match args with
  | [] => #[`Mathlib]
  | args => args.toArray.map fun s => s.toName
  searchPathRef.set compile_time_search_path%
  -- Proper delaborators need also be loaded for better printing of results
  -- (e.g., if the module is Init.Prelude which does not have delaborator for Eq yet)
  let delaboratorModules := #[
    `Mathlib.Lean.PrettyPrinter.Delaborator,
    `Lean.PrettyPrinter
  ]
  let importModules := modules ++ delaboratorModules
  CoreM.withImportModules importModules (options := options) do
    MetaM.run' <| allConstants modules fun _ _ _ json ↦ do
      -- IO.eprint s!"\x1B[2K\rProcessing [{i}/{total}] {name.toString.take 60}"
      IO.println json.compress
    -- IO.eprintln ""
  return 0
