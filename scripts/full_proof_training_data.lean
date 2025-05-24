import TrainingData.Frontend
import TrainingData.InfoTree.ToJson
import TrainingData.InfoTree.TacticInvocation.Basic
import Batteries
import Lean
import TrainingData.Utils.Range
import Cli

open Lean Elab IO Meta
open Cli System

def findCommandInfo (t : InfoTree) : List (CommandInfo × ContextInfo) :=
  let infos := t.findAllInfo none fun i => match i with
    | .ofCommandInfo _ => true
    | _ => false
  infos.filterMap fun p => match p with
  | (.ofCommandInfo i, some ctx, _) => (i, ctx)
  | _ => none


structure ElabDeclInfo where
  range : Range
  cmdInfo : CommandInfo
  currNamespace : Name

def getElabDeclInfo (trees : List InfoTree) : IO (List ElabDeclInfo) := do
    let mut out  := []
    for tree in trees do
      let infos := findCommandInfo tree
      for ⟨cmdInfo, ctxInfo⟩ in infos do
        out := ⟨FileMap.stxRange ctxInfo.fileMap cmdInfo.stx, cmdInfo, ctxInfo.currNamespace⟩ :: out
    return out

-- def ppCommandInfo (module: ModuleName) (info : CommandInfo) : IO String :=
--    return (Substring.mk (← moduleSource module)
--    (info.stx.getPos?.getD 0)
--    (info.stx.getTailPos?.getD 0)).toString

def ppDeclAndProof (module: ModuleName) (info: CommandInfo) : IO (Option (String × String)) := do
    -- let ppDecl ← ppCommandInfo module info
    -- (magic value) if this command is a declaration like theorem/def T := proof/definition
    -- then the := syntax occurs at `stx[1][3][0]`
    if info.stx[1][3][0].getAtomVal == ":=" then
      let declStart := info.stx.getPos?.getD 0
      let proofStart := info.stx[1][3].getPos?.getD 0
      let proofEnd := info.stx.getTailPos?.getD 0
      let moduleSource ← moduleSource module
      let decl := (Substring.mk moduleSource declStart proofStart).toString
      let proof := (Substring.mk moduleSource proofStart proofEnd).toString
      return (decl, proof)
    else
      return none

def validateDecl (_decl : String) : IO Bool := do
  return true

def validateProof (proof : String) : IO Bool := do
  return proof.trim != ""
    -- we allow "sorry" in proof (for extracting miniCTX data)

def fullName (elabDeclInfo : ElabDeclInfo) : Option Name :=
  let cmdInfo := elabDeclInfo.cmdInfo
  -- (magic value) if this command is a declaration (theorem, lemma, def, etc), then
  -- `stx[1][1][0]` should contain the identifier
  if cmdInfo.stx[1][1][0].isIdent then
    let name := cmdInfo.stx[1][1][0].getId
    let isRootName := (`_root_).isPrefixOf name
    let declName := if isRootName then name.replacePrefix `_root_ Name.anonymous else elabDeclInfo.currNamespace ++ name
    some declName
  else
    none

def trainingData' (elabDeclInfo: ElabDeclInfo) (module : ModuleName) : IO (Option (Name × Json)) := do
  let cmdInfo := elabDeclInfo.cmdInfo
  let sourceUpToDecl := Substring.mk (← moduleSource module) 0 (cmdInfo.stx.getPos?.getD 0)

  let declAndProof? ← ppDeclAndProof module cmdInfo
  let declName? := fullName elabDeclInfo

  if let some (decl, proof) := declAndProof? then
    if let some declName := declName? then

      if declName.isInternal then return none
      unless ← validateDecl decl do return none
      unless ← validateProof proof do return none

      let json : Json :=
        Json.mkObj [
          -- ("declId", Json.str declId),
          ("file", Json.str <| (← findLean module).toString.stripPrefix "./.lake/packages/"),
          ("module", Json.str module.toString),
          ("declName", Json.str declName.toString),
          ("decl", Json.str decl),
          ("proof", Json.str proof),
          ("srcUpToDecl", Json.str sourceUpToDecl.toString)
        ]

      return (declName, json)

  return none

def trainingData (args : Cli.Parsed) : IO UInt32 := do
    searchPathRef.set compile_time_search_path%

    let module := args.positionalArg! "module" |>.as! ModuleName
    let infos ← getElabDeclInfo (← moduleInfoTrees module)

    let mut visited : NameSet := ∅
    let mut jsons : List Json := []
    for elabDeclInfo in infos do
      if let some (name, json) ← trainingData' elabDeclInfo module then
        unless visited.contains name do
          jsons := json :: jsons
          visited := visited.insert name

    let out := jsons

    for item in out do
      IO.println item.compress
    return 0


/-- Setting up command line options and help text for `lake exe full_proof_training_data`. -/
def full_proof_training_data : Cmd := `[Cli|
  full_proof_training_data VIA trainingData; ["0.0.1"]
"Export training data from the given file."

  ARGS:
    module : ModuleName; "Lean module to compile and export training data."
]

/-- `lake exe training_data` -/
def main (args : List String) : IO UInt32 :=
  full_proof_training_data.validate args
