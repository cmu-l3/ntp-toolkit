import TrainingData.Frontend
import TrainingData.InfoTree.ToJson
import TrainingData.InfoTree.TacticInvocation.Basic
import TrainingData.Utils.Range
import Mathlib.Data.String.Defs
import Mathlib.Lean.CoreM
import Std.Lean.Util.Path
import Std.Data.String.Basic
import Mathlib.Tactic.Change
import Cli

import Mathlib.Data.Option.Basic

open Lean Elab IO Meta
open Cli System

def DeclIdMap := HashMap String (List Json)

def addToMap (map : DeclIdMap) (declId : String) (jsonObj : Json) : DeclIdMap :=
  match map.find? declId with
  | some jsonList => map.insert declId (jsonObj :: jsonList)
  | none => map.insert declId [jsonObj]

def groupByDecl (idJsons : List (String × Json)) : IO DeclIdMap := do
  let mut map : DeclIdMap := HashMap.empty
  for ⟨declId, json⟩ in idJsons do
    map := addToMap map declId json
  return map

def mapToJson (map : DeclIdMap) : List Json :=
  let entries := map.toList
  let jsonEntries : List Json := entries.map fun (declId, jsonList) =>
    Json.mkObj [
      ("declId", declId),
      ("tacticExamples", Json.arr jsonList.toArray)
    ]
  jsonEntries

def generateRandomHash (length : Nat := 15): IO String := do
  let chars := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789".toList
  let mut hash := ""
  for _ in List.range length do
    hash := hash ++ (chars.get! (← IO.rand 1 (chars.length-1))).toString
  return hash

def findCommandInfo (t : InfoTree) : List (CommandInfo × ContextInfo) :=
  let infos := t.findAllInfo none fun i => match i with
    | .ofCommandInfo _ => true
    | _ => false
  infos.filterMap fun p => match p with
  | (.ofCommandInfo i, some ctx, _) => (i, ctx)
  | _ => none

def ElabDeclInfo := (Range × CommandInfo)

def getElabDeclInfo (trees : List InfoTree) : IO (List ElabDeclInfo) := do
    let mut out  := []
    for tree in trees do
      let infos := findCommandInfo tree
      for ⟨cmdInfo, ctxInfo⟩ in infos do
        out := (FileMap.stxRange ctxInfo.fileMap cmdInfo.stx, cmdInfo) :: out
    return out

def ppCommandInfo (info : CommandInfo) : String :=
  info.stx.prettyPrint.pretty

def getElabDeclOfTacticInvocation (elabDeclInfo : List ElabDeclInfo) (ti: TacticInvocation) :
  Option ElabDeclInfo := do
    let ⟨s, e⟩ := FileMap.stxRange ti.ctx.fileMap ti.info.stx
    elabDeclInfo.find? fun ⟨⟨s', e'⟩, _⟩ => s' <= s && e <= e'

def makeElabDeclId (info: ElabDeclInfo) (module: Name) (hash: String) : String :=
  let ⟨x, y⟩ := info.fst.fst
  let declId := s!"{module}.{x}_{y}.{hash}"
  declId

def getInvocationTrees (module: ModuleName) : IO (List InfoTree) := do
    let mut trees ← moduleInfoTrees module
    trees := trees.bind InfoTree.retainTacticInfo
    trees := trees.bind InfoTree.retainOriginal
    trees := trees.bind InfoTree.retainSubstantive
    return trees


namespace Lean.Elab.TacticInvocation

def tacticPP (module : ModuleName) (i: TacticInvocation) : IO String := do
   return (Substring.mk (← moduleSource module)
   (i.info.stx.getPos?.getD 0)
   (i.info.stx.getTailPos?.getD 0)).toString

def ppCommandInfo (module: ModuleName) (info : CommandInfo) : IO String :=
   return (Substring.mk (← moduleSource module)
   (info.stx.getPos?.getD 0)
   (info.stx.getTailPos?.getD 0)).toString

def ppDeclWithoutProof (module: ModuleName) (info: CommandInfo) : IO String := do
    let ppDecl ← ppCommandInfo module info
    let decl := (ppDecl.splitOn ":=").headD ""
    return decl

def trainingData' (elabDeclInfo: ElabDeclInfo) (module : ModuleName) (hash : String) (i : TacticInvocation) : IO (String × Json) := do
  let declId := makeElabDeclId elabDeclInfo module hash
  let sourceUpToTactic := Substring.mk (← moduleSource module) 0 (i.info.stx.getPos?.getD 0)
  let declUpToTactic := Substring.mk (← moduleSource module)
    (elabDeclInfo.snd.stx.getPos?.getD 0) (i.info.stx.getPos?.getD 0)

  let state := (Format.joinSep (← i.goalState) "\n").pretty
  let nextTactic ← tacticPP module i
  let decl ← ppDeclWithoutProof module elabDeclInfo.snd

  let json : Json :=
    Json.mkObj [
      ("declId", Json.str declId),
      ("decl", Json.str decl),
      ("srcUpToTactic", Json.str sourceUpToTactic.toString),
      ("declUpToTactic", Json.str declUpToTactic.toString),
      ("state", Json.str state),
      ("nextTactic", Json.str nextTactic)
    ]
  return (declId, json)

end Lean.Elab.TacticInvocation

def trainingData (args : Cli.Parsed) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%

  let module := args.positionalArg! "module" |>.as! ModuleName
  let infos ← getElabDeclInfo (← moduleInfoTrees module)
  let trees ← getInvocationTrees module
  let hash ← generateRandomHash

  let mut idJsons : List (String × Json) := []
  for t in trees do
    for t in t.tactics do

      match getElabDeclOfTacticInvocation infos t with
      | some elabDeclInfo => do
        let json ← t.trainingData' elabDeclInfo module hash
        idJsons := json :: idJsons
      | none => pure ()

  let out := idJsons.reverse.map fun (_, j) => j

  for item in out do
    IO.println item.compress

  return 0

/-- Setting up command line options and help text for `lake exe training_data`. -/
def training_data : Cmd := `[Cli|
  training_data VIA trainingData; ["0.0.1"]
"Export training data from the given file."

  ARGS:
    module : ModuleName; "Lean module to compile and export training data."
]

/-- `lake exe training_data` -/
def main (args : List String) : IO UInt32 :=
  training_data.validate args

namespace Lean.Elab.TacticInvocation

/-- Gather all premises that appear in a syntax `s` and return two namesets of names. The first nameset
    contains all hypotheses in the given `lctx` that appear in `s`, and the second nameset contains all
    global constants that appear in `s`.

    For each ident syntax `i` that appears in `s`, if `i` appears as a hypothesis in the given `lctx`,
    then regardless of whether `i` can be interpreted as a global name, `i` is interpreted as that
    hypothesis and returned in the first nameset.

    For each ident syntax `i` that appears in `s` that does NOT appear as a hypothesis in the given `lctx`,
    `i` is resolved into a fully disambiguated global name which is then returned in the second nameset.

    As long as the source code does not contain any "ambiguous, possible interpretations" errors, all
    idents that appear in `s` should either:
    - Appear in the given `lctx` (in which case, it is added to the first NameSet)
    - Be resolvable into fully disambiguated global names (in which case, it is added to the second NameSet)
    - Be a new name supplied by the user that does not correspond to any existing hypotheses or constants
      (e.g. as in `intro h`). These names can be safely disregarded -/
partial def syntaxPremises (lctx : LocalContext) (s : Syntax) : MetaM (NameSet × NameSet) := do
  match s with
  | .missing => return (∅, ∅)
  | .node _ _ args => return (← args.mapM (syntaxPremises lctx)).foldl (fun acc arg => (acc.1.append arg.1, acc.2.append arg.2)) (∅, ∅)
  | .atom _ _ => return (∅, ∅)
  | .ident _ _ n _ =>
    if lctx.usesUserName n then
      return ((∅ : NameSet).insert n, ∅)
    else
      try
        return (∅, (∅ : NameSet).insert (← Lean.resolveGlobalConstNoOverload s))
      catch _ => -- This case covers syntax like `intro h` where `h` is neither a local hypothesis nor a global constant
        return (∅, ∅)

-- **TODO** Figure out bug where some terms used by `simp` don't appear in `nextTacticTermPremises`
def trainingDataGivenModule' (elabDeclInfo: ElabDeclInfo) (module : ModuleName) (hash : String) (i : TacticInvocation) : IO (String × Json) := do
  let declId := makeElabDeclId elabDeclInfo module hash
  let sourceUpToTactic := Substring.mk (← moduleSource module) 0 (i.info.stx.getPos?.getD 0)
  let declUpToTactic := Substring.mk (← moduleSource module)
    (elabDeclInfo.snd.stx.getPos?.getD 0) (i.info.stx.getPos?.getD 0)

  let state := (Format.joinSep (← i.goalState) "\n").pretty

  let nextTactic ← tacticPP module i
  let decl ← ppDeclWithoutProof module elabDeclInfo.snd

  let mainGoalBeforeTactic ← i.runMetaM (fun mvarId => pure mvarId)
  let (lctxBeforeTactic, localInstancesBeforeTactic) ← do
    match i.info.mctxBefore.findDecl? mainGoalBeforeTactic with
    | none => throw $ IO.userError s!"trainingDataGivenModule' :: Unable to find tactic's main goal"
    | some mvarDecl => pure (mvarDecl.lctx, mvarDecl.localInstances)

  /- **TODO** Modify `usedLemmas` so that simp aux lemmas are converted to the constants they actually correspond to
      (see `Lean.Elab.Tactic.mkSimpOnly` which takes in `UsedSimps` and determines which global constants they refer to) -/
  let (usedLemmas, explicitUsedLctxHypotheses, explicitUsedConstants, explicitUsedLemmas) ← i.runMetaMGoalsAfter
    (fun _ => do
      -- Gather all constants that appear in the proof term generated by the current tactic
      -- let usedConstantNames := (← instantiateMVars (mkMVar mainGoalBeforeTactic)).headBeta.getUsedConstants
      let usedConstantNames := (← instantiateMVars (mkMVar mainGoalBeforeTactic)).getUsedConstants
      -- Gather the types corresponding to all of the constants that appear in `usedConstantNames`
      let usedConstantsWithTypes ← usedConstantNames.mapM (fun n => return (n, (← Lean.getConstInfo n).type))
      -- Filter `usedConstantsWithTypes` to only include constants that are lemmas (i.e. filter out constants like `Nat.add`)
      let usedLemmas ← usedConstantsWithTypes.filterMapM (fun (n, t) => return if (← inferType t).isProp then some n else none)
      -- Gather all names that appear explicitly in the source code of the current tactic
      let (explicitUsedLctxNames, explicitUsedConstants) ← syntaxPremises lctxBeforeTactic i.info.stx
      let explicitUsedLctxNames := explicitUsedLctxNames.toArray
      let explicitUsedConstants := explicitUsedConstants.toArray
      -- Filter `explicitUsedLctxNames` to only include names that correspond to hypotheses in the local context (i.e. filter out non-Props)
      let explicitUsedLctxHypotheses ← explicitUsedLctxNames.filterM
        (fun n =>
          match lctxBeforeTactic.findFromUserName? n with
          | some decl =>
            withLCtx lctxBeforeTactic localInstancesBeforeTactic do
              return (← inferType decl.type).isProp
          | none => return false -- This should never happen since `syntaxPremises` found that `lctx.usesUserName n` returns true
        )
      -- Filter `explicitUsedConstants` to only include names that correspond to constants that are lemmas
      let explicitUsedLemmas ← explicitUsedConstants.filterM (fun n => return (← inferType (← Lean.getConstInfo n).type).isProp)
      return (usedLemmas, explicitUsedLctxHypotheses, explicitUsedConstants, explicitUsedLemmas))

  let json : Json :=
    Json.mkObj [
      -- ("declId", Json.str declId),
      -- ("decl", Json.str decl),
      -- ("srcUpToTactic", Json.str sourceUpToTactic.toString),
      -- ("declUpToTactic", Json.str declUpToTactic.toString),
      -- ("state", Json.str state),
      ("nextTactic", Json.str nextTactic),
      ("nextTacticTermPremises", Json.str s!"{usedLemmas}"), -- Premises that appear in the proof term generated by the tactic
      ("nextTacticExplicitConstants", Json.str s!"{explicitUsedConstants}"), -- Constants that appear in tactic syntax
      ("nextTacticExplicitPremises", Json.str s!"{explicitUsedLemmas}"), -- Prop-typed constants that appear in tactic syntax
      ("nextTacticExplicitLocalHypotheses", Json.str s!"{explicitUsedLctxHypotheses}") -- Local context hyppotheses that appear in tactic syntax
    ]
  return (declId, json)

end Lean.Elab.TacticInvocation

def trainingDataGivenModule (module : ModuleName) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%

  let infos ← getElabDeclInfo (← moduleInfoTrees module)
  let trees ← getInvocationTrees module
  let hash ← generateRandomHash

  let mut idJsons : List (String × Json) := []
  for t in trees do
    for t in t.tactics do

      match getElabDeclOfTacticInvocation infos t with
      | some elabDeclInfo => do
        let json ← t.trainingDataGivenModule' elabDeclInfo module hash
        idJsons := json :: idJsons
      | none => pure ()

  let out := idJsons.reverse.map fun (_, j) => j

  for item in out do
    IO.println item.compress

  return 0

-- #eval trainingDataGivenModule `Mathlib.Data.Int.Defs
#eval trainingDataGivenModule `Mathlib.Data.Option.Basic

namespace Option

-- NOTE: `show_term rw [← map_some', ← map_some']` gives a different answer
-- than `show_term simp only [← map_some']` even though they do the same thing
-- (the answer given for the latter is NOT correct as it turns out)
theorem map_injective'2 : Function.Injective (@Option.map α β) := fun f g h ↦
  funext fun x ↦ some_injective _ $ by
    -- rw [← map_some', ← map_some']
    simp only [← map_some']
    simp only [h]
    -- show_term simp only [← map_some', h]
