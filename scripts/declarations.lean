import Mathlib.Lean.CoreM
import Mathlib.Control.Basic
import Mathlib.Lean.Expr.Basic
import Batteries
import TrainingData.Utils.TheoremPrettyPrinting
import TrainingData.Frontend

/-!
Generate name, type, docstring, and pretty-printed information for each declaration in a module.

This uses doc-gen4 and outputs approximately the same format as doc-gen4.

The extracted declarations are usually used as potential premises to select from for a premise retriever.
-/

open Lean Elab IO Meta DocGen4.Process TheoremPrettyPrinting

namespace DocGen4.Process

open DocInfo

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
  let info ← Info.ofConstantVal' cinfo.toConstantVal
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
def constantInfoToJson (cinfo : ConstantInfo) (step : CompilationStep) : MetaM Json := do
  let (kind, info) ← infoOfConstant cinfo
  let name := cinfo.name.toString
  let args := info.args.map (fun arg => arg.binder.stripTags)
  let typeBody := info.type.stripTags
  let doc? := info.doc

  -- format declaration into `signature`
  let mut signature := ""
  if let some doc := doc? then
    signature := signature ++ "/-- " ++ doc.stripSuffix " " ++ " -/\n"
  signature := signature ++ kind ++ " "
  signature := signature ++ name ++ " "
  for arg in args do
    signature := signature ++ arg ++ " "
  signature := signature ++ ": " ++ typeBody

  let type ← ppExpr cinfo.type
  let type := type.pretty 100000000000000

  return Json.mkObj [
    ("name", Json.str name),
    ("kind", Json.str kind),
    ("type", Json.str type),
    ("typeArgs", Json.arr (args.map .str)),
    ("typeBody", Json.str typeBody),
    ("doc", match doc? with
      | some doc => Json.str doc
      | none => Json.null),
    ("signature", Json.str signature),
    ("line", Json.num info.declarationRange.pos.line),
    ("column", Json.num info.declarationRange.pos.column),
    ("isProp", Json.bool (← isProp cinfo.type)),
    ("src", Json.str step.src.toString),
    -- Only certain declarations can be in the eval/test set
    ("isHumanTheorem", Json.bool (← Name.isHumanTheorem cinfo.name)),
  ]

open Core in
/-- Delaborates the current scope using `#where`. -/
def frontendStateToJson (state : Frontend.State) : CoreM Json := do
  let imports := state.commandState.env.header.imports.toList
  let mut importsStr := ""
  if imports.all (·.module != `Init) then importsStr := importsStr ++ "prelude\n"
  for imp in imports do
    unless imp.module == `Init do
      importsStr := importsStr ++ s!"import {imp.module}\n"

  let savedState ← saveState
  resetMessageLog
  liftCommandElabM do
    set state.commandState
    Command.elabWhere (← `(command| #where))
  let messages ← getAndEmptyMessageLog
  let scopeStr? ← messages.toArray.findSomeRevM? fun msg => do
    if msg.severity == MessageSeverity.information then
      return some <| (← msg.toString).replace "-- In root namespace with initial scope" "" |>.trim
    else
      return none
  savedState.restore

  let scopeStr := (importsStr.trim ++ "\n\n" ++ (scopeStr?.getD "").trim).trim
  return Json.mkObj [
    ("scope", Json.str scopeStr),
  ]

/-- If a constant should not be included (more permissive than Name.isBlackListed). -/
def isBlackListedName (name : Name) : Bool :=
  name == ``sorryAx || name.isInternalDetail

/-- Export module name and file name to JSON -/
def moduleNameToJson (moduleName : Name) : IO Json := do
  return Json.mkObj [
    ("module", Json.str moduleName.toString),
    -- ("fileName", Json.str (← findLean moduleName).toString),
  ]

/--
Process all declarations from compilation steps, collecting prettified declarations.
Calls callback on each extracted declaration.
-/
def allDeclarationsFromSteps (moduleName : Name) (compilationSteps : List CompilationStep) (callback : Nat → Name → Json → MetaM Unit) :
    IO Unit := do
  let mut processed := 0
  for step in compilationSteps do
    for cinfo in step.diff do
      if isBlackListedName cinfo.name then continue
      let ctxCore : Core.Context := { fileName := "<ntp-toolkit>", fileMap := default, maxHeartbeats := 0 }
      let sCore : Core.State := { env := step.after }
      let _ ← MetaM.toIO (ctxCore := ctxCore) (sCore := sCore) (ctx := {}) (s := {}) do
        try
          let json ← withNtpToolkitPPOptions <| constantInfoToJson cinfo step
          let json := json.mergeObj (← frontendStateToJson step.state)
          let json := json.mergeObj (← moduleNameToJson moduleName)
          callback processed cinfo.name json
        catch _ =>
          -- Extremely rare cases (e.g. Fin.eq_of_val_eq, Qq.Quoted.unsafeMk)
          IO.eprintln s!"warning: failed to extract constant {cinfo.name}"
      processed := processed + 1

def main (args : List String) : IO UInt32 := do
  unsafe enableInitializersExecution
  initSearchPath (← findSysroot)

  let modules := match args with
  | [] => #[`Mathlib]
  | args => args.toArray.map fun s : String => s.toName

  -- Process each module using compilation steps
  for module in modules do
    let compilationSteps ← compileModule module
    allDeclarationsFromSteps module compilationSteps fun _ _ json ↦ do
      IO.println json.compress
  return 0
