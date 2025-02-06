import Mathlib.Lean.CoreM
import Mathlib.Control.Basic
import Mathlib.Lean.Expr.Basic
import Batteries
import TrainingData.Utils.TheoremPrettyPrinting

/-!
Generate name, type, docstring, and pretty-printed information for each declaration in a module.

This uses doc-gen4 and outputs approximately the same format as doc-gen4.

The extracted declarations are usually used as potential premises to select from for a premise retriever.
-/

open Lean Meta DocGen4.Process

namespace DocGen4.Process

open DocGen4 DocGen4.Process DocGen4.Process.DocInfo TheoremPrettyPrinting

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
  let info ← withOptions (fun o => (o.set `pp.notation false).set `pp.fullNames true) <|
    Info.ofConstantVal' cinfo.toConstantVal
  return (kind, info)

end DocGen4.Process

def Lean.Name.isTheorem (name : Name) : CoreM Bool := do
  let .some ci := (← getEnv).find? name
    | throwError "Name.isTheorem :: Cannot find name {name}"
  let .thmInfo _ := ci
    | return false
  return true

/--
  A constant is a human theorem iff it is a theorem and has a
  declaration range. Roughly speaking, a constant have a declaration
  range iff it is defined (presumably by a human) in a `.lean` file
-/
def Lean.Name.isHumanTheorem (name : Name) : CoreM Bool := do
  let hasDeclRange := (← Lean.findDeclarationRanges? name).isSome
  let isTheorem ← Name.isTheorem name
  let notProjFn := !(← Lean.isProjectionFn name)
  return hasDeclRange && isTheorem && notProjFn

/-- Pretty-prints a constant to JSON -/
def constantInfoToJson (cinfo : ConstantInfo) : MetaM Json := do
  let (kind, info) ← infoOfConstant cinfo
  let name := cinfo.name.toString
  let args := info.args.map (fun arg => arg.binder.stripTags)
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
    ("isProp", Json.bool (← isProp cinfo.type)),
    -- Only certain declarations can be in the eval/test set
    ("isHumanTheorem", Json.bool (← Name.isHumanTheorem cinfo.name)),
  ]

/-- If a constant should not be included (more permissive than Name.isBlackListed). -/
def isBlackListedName (name : Name) : Bool :=
  name == ``sorryAx || name.isInternalDetail

/--
Traverse all declarations from modules, collecting prettified declarations
Calls callback on each extracted declaration.
(Should convert to MLList instead of callback?)
-/
def allDeclarations (moduleNames : Array Name) (callback : Nat → Nat → Name → Json → MetaM Unit) :
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
    MetaM.run' <| allDeclarations modules fun _ _ _ json ↦ do
      -- IO.eprint s!"\x1B[2K\rProcessing [{i}/{total}] {name.toString.take 60}"
      IO.println json.compress
    -- IO.eprintln ""
  return 0
