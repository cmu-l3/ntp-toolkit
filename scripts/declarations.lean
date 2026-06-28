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

open Lean Core Meta DocGen4.Process

namespace DocGen4.Process

open DocGen4 DocGen4.Process DocGen4.Process.DocInfo TheoremPrettyPrinting

/-- A variable that, when set to true, disables some of the changes that were made to improve performance. -/
def useNaiveDataExtraction := false

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
  let info ←
    if useNaiveDataExtraction then
      Info.ofConstantVal' cinfo.toConstantVal
    else
      withHammerPPOptions <|
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


/-- This is copied from a portion of `Lean.findSimpleDocString?` -/
def toMarkdown : VersoDocString → String
  | .mk bs ps => Doc.MarkdownM.run' do
      for b in bs do
        Doc.ToMarkdown.toMarkdown b
      for p in ps do
        Doc.ToMarkdown.toMarkdown p

/-- Whether `name`'s defining module (`moduleIdx`) opted into Lean's module system,
    and whether `name` is exposed (its body is in the public scope).

    `isExposed` is only meaningful inside the module system; outside it (and for the
    non-module import pass, where `setExporting` is a no-op) it is `false`. -/
def moduleVisibilityFlags (env : Environment) (name : Name) (moduleIdx : ModuleIdx) : Bool × Bool :=
  let inModuleSystem := (env.header.moduleData[moduleIdx.toNat]?).any (·.isModule)
  let isExposed :=
    inModuleSystem &&
      (match (env.setExporting true).find? name with
        | some (.defnInfo _) => true
        | _ => false)
  (inModuleSystem, isExposed)

/-- Pretty-prints a constant to JSON -/
def constantInfoToJson (cinfo : ConstantInfo) (moduleIdx : ModuleIdx) : MetaM Json := do
  if Lean.isPrivateName cinfo.name then
    throwError "constantInfoToJson: unexpected private declaration {cinfo.name}"
  let env ← getEnv
  let (inModuleSystem, isExposed) := moduleVisibilityFlags env cinfo.name moduleIdx
  let (kind, info) ← infoOfConstant cinfo
  let name := cinfo.name.toString
  let args := info.args.map (fun arg => arg.binder.stripTags)
  let type := info.type.stripTags
  let doc? := info.doc

  -- format declaration into `decl`
  let mut decl := ""
  if let some doc := doc? then
    match doc with
    | .inl doc => decl := decl ++ "/-- " ++ doc.dropSuffix " " ++ " -/\n"
    | .inr verso => decl := decl ++ "/-- " ++ (toMarkdown verso).dropSuffix " " ++ " -/\n"
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
      | some (.inl doc) => Json.str doc
      | some (.inr verso) => Json.str (toMarkdown verso)
      | none => Json.null),
    ("decl", Json.str decl),
    ("line", Json.num info.declarationRange.pos.line),
    ("column", Json.num info.declarationRange.pos.column),
    ("isProp", Json.bool (← isProp cinfo.type)),
    -- Only certain declarations can be in the eval/test set
    ("isHumanTheorem", Json.bool (← Name.isHumanTheorem cinfo.name)),
    ("inModuleSystem", Json.bool inModuleSystem),
    ("isExposed", Json.bool isExposed),
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
              let json ← constantInfoToJson cinfo moduleIdx
              callback i total name json
            catch _ =>
              -- Extremely rare cases (e.g. Fin.eq_of_val_eq, Qq.Quoted.unsafeMk)
              IO.eprintln s!"warning: failed to extract constant {name}"
              continue
    i := i + 1

/--
Import `modules` at the given `OLeanLevel` (with `importAll := true`) and run
`run` in a `CoreM` over the resulting environment. Mirrors
`CoreM.withImportModules`, but lets us choose the import level: at `.exported` the
environment is module-aware (`env.header.isModule = true`), so the public view is
queryable via `setExporting` (needed for `isExposed`)
-/
def runImportModulesAtLevel {α : Type} (modules : Array Name) (level : OLeanLevel)
    (options : Options := {}) (run : CoreM α) : IO α := unsafe do
  let imports := modules.map fun m => ({ module := m, importAll := true } : Import)
  let env ← importModules imports options (level := level)
  try
    let ctx := { fileName := "", options, fileMap := default }
    let state := { env }
    Prod.fst <$> (CoreM.toIO · ctx state) run
  finally
    env.freeRegions

def main (args : List String) : IO UInt32 := do
  let options := Options.empty.insert `maxHeartbeats (0 : Nat)
  let modules := match args with
  | [] => #[`Mathlib]
  | args => args.toArray.map fun s => s.toName
  unsafe enableInitializersExecution
  initSearchPath (← findSysroot)
  let printJson : Nat → Nat → Name → Json → MetaM Unit := fun _ _ _ json ↦ do
    IO.println json.compress
  -- Pass 1: Identify `moduleSystemTargets`, the set of files that opt into the
  -- module system, and extract declarations from all other files (by running
  -- `printJson` on them). For files that don't opt into the module system,
  -- this pass is identical to the previous behavior which ignored the module
  -- system entirely.
  let moduleSystemTargets ← CoreM.withImportModules modules (options := options) do
    let env ← getEnv
    let isModuleSystem (m : Name) : Bool :=
      match env.header.moduleNames.findIdx? (· == m) with
      | some idx => (env.header.moduleData[idx]?).any (·.isModule)
      | none => false
    let moduleSystemTargets := modules.filter isModuleSystem
    let nonModuleTargets := modules.filter (fun m => !isModuleSystem m)
    MetaM.run' <| allDeclarations nonModuleTargets printJson
    return moduleSystemTargets
  -- Pass 2: Extract declarations of `moduleSystemTargets` at the `.exported` level.
  unless moduleSystemTargets.isEmpty do
    runImportModulesAtLevel moduleSystemTargets .exported options do
      MetaM.run' <| allDeclarations moduleSystemTargets printJson
  return 0
