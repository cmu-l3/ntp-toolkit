import Mathlib.Lean.CoreM
import Mathlib.Control.Basic
import Mathlib.Lean.Expr.Basic
import Batteries.Lean.HashMap
import Batteries.Lean.Util.Path
import DocGen4.Process
import Qq

/-!
Generate declaration names and types.
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
-/
def Info.ofConstantVal' (v : ConstantVal) : MetaM Info := do
  argTypeTelescope v.type fun args type => do
    let args ← args.mapM (fun (n, e, b) => do return Arg.mk n (← prettyPrintTerm' e) b)
    let nameInfo ← NameInfo.ofTypedName' v.name type
    let range := (← findDeclarationRanges? v.name).getD default
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
def constantInfoToJson (cinfo : ConstantInfo) (moduleName : Name) : MetaM Json := do
  let (kind, info) ← infoOfConstant cinfo
  return Json.mkObj [
    ("name", Json.str cinfo.name.toString),
    ("kind", Json.str kind),
    ("args", Json.arr <| info.args.map argToString |>.map Json.str),
    ("type", Json.str info.type.stripTags),
    ("doc", match info.doc with
      | some doc => Json.str doc
      | none => Json.null),
    ("line", match info.declarationRange.pos.line with
      -- if 0, probably generated from the getD default in Info.ofConstantVal'
      -- so we don't know the position
      | 0 => Json.null
      | l => l),
    ("module", Json.str moduleName.toString)
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

/-- If a constant from this module should not be included. -/
def isBlacklistedModule (moduleName : Name) : Bool :=
  -- We should do this during postprocessing?
  -- match moduleName.components with
  -- | `Lean :: _ => true
  -- | `Lake :: _ => true
  -- | `Qq :: _ => true
  -- | `Aesop :: _ => true
  -- | `Cli :: _ => true
  -- | `ImportGraph :: _ => true
  -- | `DocGen4 :: _ => true
  -- | `ProofWidgets :: _ => true
  -- | `UnicodeBasic :: _ => true
  -- | `MD4Lean :: _ => true
  -- | _ =>
  false

/--
Traverse all constants from imported files,
collecting prettified declarations
-/
def allConstants (callback : Name → Json → MetaM Unit) :
    MetaM Unit := do
  let env ← getEnv
  let constantsMap := env.constants.map₁
  for (name, cinfo) in constantsMap do
    -- We omit all internal details (Name.isInternalDetail)
    -- We restrict to declarations in the module
    if !isBlackListedName name then
      if let some moduleIdx := env.getModuleIdxFor? name then
        if let some moduleName := env.header.moduleNames[moduleIdx.toNat]? then
          if !isBlacklistedModule moduleName then
            try
              let json ← constantInfoToJson cinfo moduleName
              callback name json
            catch _ =>
              -- Extremely rare cases (e.g. Qq.Quoted.unsafeMk)
              IO.eprintln s!"\nFailed to extract {name}"
              continue

def main (args : List String) : IO UInt32 := do
  let options := Options.empty.insert `maxHeartbeats (0 : Nat)
  let modules := match args with
  | [] => #[`Mathlib]
  | args => args.toArray.map fun s => s.toName
  searchPathRef.set compile_time_search_path%
  CoreM.withImportModules modules (options := options) do
    MetaM.run' <| allConstants fun name json ↦ do
      IO.eprint s!"\x1B[2K\rProcessing {name.toString.take 60}"
      IO.println json.compress
    IO.eprintln ""
  return 0
