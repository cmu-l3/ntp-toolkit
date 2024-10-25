import TrainingData.Frontend
import TrainingData.InfoTree.ToJson
import TrainingData.InfoTree.TacticInvocation.Basic
import TrainingData.Utils.Range
import Mathlib.Data.String.Defs
import Mathlib.Lean.CoreM
import Batteries.Lean.Util.Path
import Batteries.Data.String.Basic
import Mathlib.Tactic.Change
import Cli

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

def ppCommandInfo (info : CommandInfo) : String :=
  info.stx.prettyPrint.pretty

def getElabDeclOfTacticInvocation (elabDeclInfo : List ElabDeclInfo) (ti: TacticInvocation) :
  Option ElabDeclInfo := do
    let ⟨s, e⟩ := FileMap.stxRange ti.ctx.fileMap ti.info.stx
    elabDeclInfo.find? fun ⟨⟨s', e'⟩, _, _⟩ => s' <= s && e <= e'

def makeElabDeclId (info: ElabDeclInfo) (module: Name) (hash: String) : String :=
  let ⟨x, y⟩ := info.range.fst
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

def ppDeclWithoutProof (module: ModuleName) (info: CommandInfo) : IO (Option String) := do
    -- let ppDecl ← ppCommandInfo module info
    -- (magic value) if this command is a declaration like theorem/def T := proof/definition
    -- then the := syntax occurs at `stx[1][3][0]`
    if info.stx[1][3][0].getAtomVal == ":=" then
      let declStart := info.stx.getPos?.getD 0
      let proofStart := info.stx[1][3].getPos?.getD 0
      -- let proofEnd := info.stx.getTailPos?.getD 0
      let moduleSource ← moduleSource module
      let decl := (Substring.mk moduleSource declStart proofStart).toString
      -- let proof := (Substring.mk moduleSource proofStart proofEnd).toString
      return decl
    else
      return none

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
  | .atom _ _ => return (∅, ∅)
  | .node _ _ args =>
    return (← args.mapM (syntaxPremises lctx)).foldl (fun acc arg => (acc.1.append arg.1, acc.2.append arg.2)) (∅, ∅)
  | .ident _ _ n _ =>
    if lctx.usesUserName n then
      return ((∅ : NameSet).insert n, ∅)
    else
      try
        return (∅, (∅ : NameSet).insert (← Lean.resolveGlobalConstNoOverload s))
      catch _ => -- This case covers syntax like `intro h` where `h` is neither a local hypothesis nor a global constant
        return (∅, ∅)

def isAuxLemma : Name → Bool
| .num (.str _ "_auxLemma") _ => true
| _ => false

/-- Takes in a constant name and checks whether it should be unfolded using `shouldUnfold`. If the constant should be unfolded,
    then returns all of the constants that appear in the unfolded result as a nameset. Otherwise, returns a set just containing
    the constant name. `unfoldConstantName` should never return any names that are supposed to be unfolded, so if a name is
    supposed to be unfolded as indicated by `shouldUnfold`, then even if its constant can't actually be unfolded, we do not
    return the name itself. -/
def unfoldConstantName (constName : Name) (constantsMap : HashMap Name ConstantInfo) (shouldUnfold : Name → Bool) : NameSet := Id.run do
  if shouldUnfold constName then
    let some constInfo := constantsMap.find? constName
      | return ∅ -- If `n` cannot be unfolded, then return the empty set because `n` shouldn't appear in the output`
    return constInfo.getUsedConstantsAsSet
  else
    return (∅ : NameSet).insert constName

def simpVariants : List String := [
  "simp",
  "simp?",
  "simp!?",
  "simp?!",
  "simp_all",
  "simp_all?",
  "simp_all!",
  "simp_all?!",
  "simp_arith",
  "simp_arith!",
  "simp_wf",
  "simpa",
  "simpa?",
  "simpa!",
  "simpa?!"
]

def rewriteVariants : List String := [
  "rw",
  "rw?",
  "rwa",
  "rewrite",
  "rw_mod_cast",
  "erw"
]

def nextTacticIsSimpOrRwVariant (t : String) : Bool :=
  simpVariants.any (fun p => (p ++ " ").isPrefixOf t) ||
  simpVariants.any (fun p => (p ++ "[").isPrefixOf t) ||
  rewriteVariants.any (fun p => (p ++ " ").isPrefixOf t) ||
  rewriteVariants.any (fun p => (p ++ "[").isPrefixOf t)

/-- This structure stores all of the data that can easily be obtained from a single tactic information. It contains a subset of the total
    data output by `trainingDataGivenModule` and `trainingData` (because these also provide fields containing information that spans across
    multiple tactics) -/
structure FirstPassTrainingData where
  declId : String
  decl? : Option String
  declName? : Option Name
  srcUpToTactic : String
  declUpToTactic : String
  state : String
  nextTactic : String
  nextTacticIsSimpOrRwVariant : Bool
  numNewGoalsOpened : Int -- Counts the number of ` by `s in `nextTactic` to determine the number of new goals created not captured by `numGoalsAfterTactic`
  nextTacticTermPremises : Array Name
  nextTacticExplicitConstants : Array Name
  nextTacticExplicitPremises : Array Name
  nextTacticExplicitLocalHypotheses : Array Name
  nextTacticAllPremises : Array Name
  nextTacticHammerRecommendation : Array Name
  goalDelta : Int -- `goalDelta` = `numNewGoalsOpened + numGoalsAfterTactic` - `numGoalsBeforeTactic`.
                  -- This is used to help determine when the scope of a goal ends.
deriving Inhabited

/-- This structure stores all of the data to eventually be output in the final JSON file. It contains all of the data in `FirstPassTrainingData`
    along with some fields containing containing information that span across multiple tactics. -/
structure SecondPassTrainingData extends FirstPassTrainingData where
  declTermPremises : Array Name
  declExplicitConstants : Array Name
  declExplicitPremises : Array Name
  declAllPremises : Array Name
  declHammerRecommendation : Array Name
  termPremisesToEndOfGoal : Array Name
  explicitConstantsToEndOfGoal : Array Name
  explicitPremisesToEndOfGoal : Array Name
  allPremisesToEndOfGoal : Array Name
  hammerRecommendationToEndOfGoal : Array Name
  curGoalCount := 1 -- This is the only field that is not output in the final JSON file. It is used internally to track whether the tactic's goal
                    -- is "currently" open during the loop that builds `SecondPassTrainingData`. If `curGoalCount` is 0, then the goal is not
                    -- currently open. If `curGoalCount > 0`, then `curGoalCount` is the number of goals that need to be closed before the current
                    -- tactic's goal should be considered closed. A tactic with `curGoalCount` = 1 and `goalDelta` = -1 is both opened and closed
                    -- by the same tactic (e.g. when a goal is proven in just one tactic)
deriving Inhabited

def trainingDataGivenTactic (elabDeclInfo: ElabDeclInfo) (module : ModuleName) (hash : String) (i : TacticInvocation) : IO FirstPassTrainingData := do
  let declId := makeElabDeclId elabDeclInfo module hash
  let sourceUpToTactic := Substring.mk (← moduleSource module) 0 (i.info.stx.getPos?.getD 0)
  let declUpToTactic := Substring.mk (← moduleSource module)
    (elabDeclInfo.cmdInfo.stx.getPos?.getD 0) (i.info.stx.getPos?.getD 0)

  let state := (Format.joinSep (← i.goalState) "\n").pretty
  let numGoalsBefore : Int := i.info.goalsBefore.length
  let numGoalsAfter : Int := i.info.goalsAfter.length

  let nextTactic ← tacticPP module i
  let decl? ← ppDeclWithoutProof module elabDeclInfo.cmdInfo
  let declName? := i.ctx.parentDecl?

  let nextTacticIsSimpOrRwVariant := nextTacticIsSimpOrRwVariant nextTactic
  let numNewGoalsOpened : Int := (nextTactic.findAllSubstr " by ").size + (nextTactic.findAllSubstr ":=by ").size + (nextTactic.findAllSubstr "\nby ").size

  let goalDelta := numNewGoalsOpened + numGoalsAfter - numGoalsBefore

  let mainGoalBeforeTactic ← i.runMetaM (fun mvarId => pure mvarId)
  let (lctxBeforeTactic, localInstancesBeforeTactic) ← do
    match i.info.mctxBefore.findDecl? mainGoalBeforeTactic with
    | none => throw $ IO.userError s!"trainingDataGivenTactic :: Unable to find tactic's main goal"
    | some mvarDecl => pure (mvarDecl.lctx, mvarDecl.localInstances)

  let (termLemmas, explicitUsedLctxHypotheses, explicitUsedConstants, explicitUsedLemmas, allLemmas) ← i.runMetaMGoalsAfter
    (fun _ => do
      -- Gather all constants that appear in the proof term generated by the current tactic
      let constantsMap := (← getEnv).constants.map₁
      let termConstantNamesNoUnfolding := (← instantiateMVars (mkMVar mainGoalBeforeTactic)).headBeta.getUsedConstantsAsSet
      -- Replace all auxiliary lemmas in `termConstantNamesNoUnfolding` with the constants that appear in their unfolded definitions
      let mut termConstantsNameSet : NameSet := ∅
      for constName in termConstantNamesNoUnfolding do
        termConstantsNameSet := termConstantsNameSet.append $ unfoldConstantName constName constantsMap isAuxLemma
      let termConstants := termConstantsNameSet.toArray
      -- Filter ``usedConstants` to only included constants that are lemmas (i.e. Prop-typed)
      let termConstantsWithTypes ← termConstants.mapM (fun n => return (n, (← Lean.getConstInfo n).type))
      let termLemmas ← termConstantsWithTypes.filterMapM (fun (n, t) => return if (← inferType t).isProp then some n else none)
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
      /- It is possible for `simp only` calls to require certain lemmas in order to succeed but not use those lemmas in the final proof
         term. To reflect the fact that these lemmas are still important, we include them along all term lemmas in in `allLemmas` -/
      let allLemmas := explicitUsedLemmas.foldl (fun acc l => if !acc.contains l then acc.push l else acc) termLemmas
      return (termLemmas, explicitUsedLctxHypotheses, explicitUsedConstants, explicitUsedLemmas, allLemmas))

  let nextTacticHammerRecommendation :=
    if nextTacticIsSimpOrRwVariant then
      explicitUsedConstants.foldl (fun acc c => if acc.contains c then acc else acc.push c) allLemmas
    else
      allLemmas

  let data := {
      declId := declId,
      decl? := decl?,
      declName? := declName?,
      srcUpToTactic := sourceUpToTactic.toString,
      declUpToTactic := declUpToTactic.toString,
      state := state,
      nextTactic := nextTactic,
      nextTacticTermPremises := termLemmas,
      nextTacticExplicitConstants := explicitUsedConstants,
      nextTacticExplicitPremises := explicitUsedLemmas,
      nextTacticExplicitLocalHypotheses := explicitUsedLctxHypotheses,
      nextTacticAllPremises := allLemmas,
      goalDelta := goalDelta
      nextTacticIsSimpOrRwVariant := nextTacticIsSimpOrRwVariant,
      numNewGoalsOpened := numNewGoalsOpened,
      nextTacticHammerRecommendation := nextTacticHammerRecommendation
    }
  return data

end Lean.Elab.TacticInvocation

open TacticInvocation

def trainingDataGivenModule (module : ModuleName) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  let infos ← getElabDeclInfo (← moduleInfoTrees module)
  let trees ← getInvocationTrees module
  let hash ← generateRandomHash
  let mut firstPassData : Array FirstPassTrainingData := #[]
  for t in trees do
    for t in t.tactics do
      match getElabDeclOfTacticInvocation infos t with
      | some elabDeclInfo => do
        let data ← t.trainingDataGivenTactic elabDeclInfo module hash
        firstPassData := firstPassData.push data
      | none => pure ()
  if firstPassData.isEmpty then
    return 0
  let mut activeDeclId : String := firstPassData[0]!.declId
  let mut activeDeclTermPremises : Array Name := #[]
  let mut activeDeclExplicitConstants : Array Name := #[]
  let mut activeDeclExplicitPremises : Array Name := #[]
  let mut activeDeclAllPremises : Array Name := #[]
  let mut activeDeclHammerRecommendation : Array Name := #[]
  let mut activeGoalTermPremises : Array Name := #[]
  let mut activeGoalExplicitConstants : Array Name := #[]
  let mut activeGoalExplicitPremises : Array Name := #[]
  let mut activeGoalAllPremises : Array Name := #[]
  let mut activeGoalHammerRecommendation : Array Name := #[]
  let mut secondPassData : Array SecondPassTrainingData :=
    firstPassData.map
      (fun data =>
        {data with
          declTermPremises := #[]
          declExplicitConstants := #[]
          declExplicitPremises := #[]
          declAllPremises := #[]
          declHammerRecommendation := #[]
          termPremisesToEndOfGoal := #[]
          explicitConstantsToEndOfGoal := #[]
          explicitPremisesToEndOfGoal := #[]
          allPremisesToEndOfGoal := #[]
          hammerRecommendationToEndOfGoal := #[]
        }
      )
  for i in [:firstPassData.size] do
    let curTacticData := firstPassData[i]!
    if curTacticData.declId != activeDeclId then -- We've changed declarations
      -- Update all `activeDecl` information to remove duplicates
      activeDeclTermPremises := (RBTree.fromArray activeDeclTermPremises Name.quickCmp : NameSet).toArray
      activeDeclExplicitConstants := (RBTree.fromArray activeDeclExplicitConstants Name.quickCmp : NameSet).toArray
      activeDeclExplicitPremises := (RBTree.fromArray activeDeclExplicitPremises Name.quickCmp : NameSet).toArray
      activeDeclAllPremises := (RBTree.fromArray activeDeclAllPremises Name.quickCmp : NameSet).toArray
      activeDeclHammerRecommendation := (RBTree.fromArray activeDeclHammerRecommendation Name.quickCmp : NameSet).toArray
      -- Update each `secondPassData` entry with `activeDeclId` with all `activeDecl` information
      for j in [:i] do
        -- `idx` starts at the tactic just before `curTacticData` and decrements we find a declId that doesn't match the activeDeclId
        let idx := i - j - 1
        let idxTacticData := secondPassData[idx]!
        if idxTacticData.declId != activeDeclId then
          break -- Once we find one tactic that doesn't match the activeDeclId, no previous tactic will match the activeDeclId
        secondPassData := secondPassData.set! idx
          {idxTacticData with
            declTermPremises := activeDeclTermPremises
            declExplicitConstants := activeDeclExplicitConstants
            declExplicitPremises := activeDeclExplicitPremises
            declAllPremises := activeDeclAllPremises
            declHammerRecommendation := activeDeclHammerRecommendation
          }
      -- Update `activeDeclId` to `curTacticData.declId` and reset all `activeDecl` information
      activeDeclId := curTacticData.declId
      activeDeclTermPremises := #[]
      activeDeclExplicitConstants := #[]
      activeDeclExplicitPremises := #[]
      activeDeclAllPremises := #[]
      activeDeclHammerRecommendation := #[]
    -- Regardless of whether `activeDeclId` changed, update all `activeDecl` information to add information from `curTacticData`
    activeDeclTermPremises := activeDeclTermPremises ++ curTacticData.nextTacticTermPremises
    activeDeclExplicitConstants := activeDeclExplicitConstants ++ curTacticData.nextTacticExplicitConstants
    activeDeclExplicitPremises := activeDeclExplicitPremises ++ curTacticData.nextTacticExplicitPremises
    activeDeclAllPremises := activeDeclAllPremises ++ curTacticData.nextTacticAllPremises
    activeDeclHammerRecommendation := activeDeclHammerRecommendation ++ curTacticData.nextTacticHammerRecommendation
    -- Check `curTacticData.goalDelta` to determine whether any `ToEndOfGoal` or `curGoalCount` fields need to be updated
    if curTacticData.goalDelta != 0 then -- This tactic either created or closed goals, so `curGoalCounts` will need to be updated
      /- Iterate backwards from current tactic through all tactics in the active decl. For each state with a `curGoalCount` > 0, update
         `curGoalCount` by `curTacticData.goalDelta.natAbs`, and if the result is zero, then populate `ToEndOfGoal` fields. -/
      activeGoalTermPremises := #[]
      activeGoalExplicitConstants := #[]
      activeGoalExplicitPremises := #[]
      activeGoalAllPremises := #[]
      activeGoalHammerRecommendation := #[]
      for j in [:i+1] do
        -- `idx` starts at `curTacticData` and decrements we find a declId that doesn't match the activeDeclId
        let idx := i - j
        let idxTacticData := secondPassData[idx]!
        -- Update `activeGoal` fields
        activeGoalTermPremises := activeGoalTermPremises ++ idxTacticData.nextTacticTermPremises
        activeGoalExplicitConstants := activeGoalExplicitConstants ++ idxTacticData.nextTacticExplicitConstants
        activeGoalExplicitPremises := activeGoalExplicitPremises ++ idxTacticData.nextTacticExplicitPremises
        activeGoalAllPremises := activeGoalAllPremises ++ idxTacticData.nextTacticAllPremises
        activeGoalHammerRecommendation := activeGoalHammerRecommendation ++ idxTacticData.nextTacticHammerRecommendation
        if idxTacticData.declId != activeDeclId then
          break -- Once we find one tactic that doesn't match the activeDeclId, no previous tactic will match the activeDeclIds
        else if idxTacticData.curGoalCount == 0 then
          continue -- The goal that `idxTacticData` operates on has already been closed
        else
          let newIdxTacticDataCurGoalCount :=
            if curTacticData.goalDelta < 0 then idxTacticData.curGoalCount - curTacticData.goalDelta.natAbs
            else idxTacticData.curGoalCount + curTacticData.goalDelta.natAbs
          if newIdxTacticDataCurGoalCount == 0 then
            -- Update all `activeGoal` information to remove duplicates
            activeGoalTermPremises := (RBTree.fromArray activeGoalTermPremises Name.quickCmp : NameSet).toArray
            activeGoalExplicitConstants := (RBTree.fromArray activeGoalExplicitConstants Name.quickCmp : NameSet).toArray
            activeGoalExplicitPremises := (RBTree.fromArray activeGoalExplicitPremises Name.quickCmp : NameSet).toArray
            activeGoalAllPremises := (RBTree.fromArray activeGoalAllPremises Name.quickCmp : NameSet).toArray
            activeGoalHammerRecommendation := (RBTree.fromArray activeGoalHammerRecommendation Name.quickCmp : NameSet).toArray
            -- Update `secondPassData` with `activeGoal` information
            secondPassData := secondPassData.set! idx
              {idxTacticData with
                curGoalCount := 0
                termPremisesToEndOfGoal := activeGoalTermPremises
                explicitConstantsToEndOfGoal := activeGoalExplicitConstants
                explicitPremisesToEndOfGoal := activeGoalExplicitPremises
                allPremisesToEndOfGoal := activeGoalAllPremises
                hammerRecommendationToEndOfGoal := activeGoalHammerRecommendation
              }
          else
            secondPassData := secondPassData.set! idx {idxTacticData with curGoalCount := newIdxTacticDataCurGoalCount}
  -- Update decl information for final declaration
  -- Update all `activeDecl` information to remove duplicates
  activeDeclTermPremises := (RBTree.fromArray activeDeclTermPremises Name.quickCmp : NameSet).toArray
  activeDeclExplicitConstants := (RBTree.fromArray activeDeclExplicitConstants Name.quickCmp : NameSet).toArray
  activeDeclExplicitPremises := (RBTree.fromArray activeDeclExplicitPremises Name.quickCmp : NameSet).toArray
  activeDeclAllPremises := (RBTree.fromArray activeDeclAllPremises Name.quickCmp : NameSet).toArray
  activeDeclHammerRecommendation := (RBTree.fromArray activeDeclHammerRecommendation Name.quickCmp : NameSet).toArray
  -- Update each `secondPassData` entry with `activeDeclId` with all `activeDecl` information
  for j in [:firstPassData.size] do
    -- `idx` starts at the last tactic and decrements we find a declId that doesn't match the activeDeclId
    let idx := firstPassData.size - j - 1
    let idxTacticData := secondPassData[idx]!
    if idxTacticData.declId != activeDeclId then
      break -- Once we find one tactic that doesn't match the activeDeclId, no previous tactic will match the activeDeclId
    secondPassData := secondPassData.set! idx
      {idxTacticData with
        declTermPremises := activeDeclTermPremises
        declExplicitConstants := activeDeclExplicitConstants
        declExplicitPremises := activeDeclExplicitPremises
        declAllPremises := activeDeclAllPremises
        declHammerRecommendation := activeDeclHammerRecommendation
      }
  -- Convert `secondPassData` to Json
  let jsonRes : Array Json := secondPassData.map
    (fun d =>
      Json.mkObj [
        -- ("declId", Json.str d.declId), -- Used internally
        ("decl", match d.decl? with | some d => Json.str d | none => Json.null),
        ("declName", match d.declName? with | some n => Json.str s!"{n}" | none => Json.null),
        -- ("goalDelta", Json.num d.goalDelta), -- Used internally but not output to JSON
        ("srcUpToTactic", Json.str d.srcUpToTactic),
        ("declUpToTactic", Json.str d.declUpToTactic),
        ("state", Json.str d.state),
        ("nextTactic", Json.str d.nextTactic),
        ("nextTacticIsSimpOrRwVariant", Json.bool d.nextTacticIsSimpOrRwVariant),
        -- ("numNewGoalsOpened", Json.num d.numNewGoalsOpened), -- Only for testing and to compute goalDelta
        ("nextTacticTermPremises", Json.arr (d.nextTacticTermPremises.map (fun n => s!"{n}"))),
        ("nextTacticExplicitConstants", Json.arr (d.nextTacticExplicitConstants.map (fun n => s!"{n}"))),
        ("nextTacticExplicitPremises", Json.arr (d.nextTacticExplicitPremises.map (fun n => s!"{n}"))),
        ("nextTacticExplicitLocalHypotheses", Json.arr (d.nextTacticExplicitLocalHypotheses.map (fun n => s!"{n}"))),
        ("nextTacticAllPremises", Json.arr (d.nextTacticAllPremises.map (fun n => s!"{n}"))),
        ("nextTacticHammerRecommendation", Json.arr (d.nextTacticHammerRecommendation.map (fun n => s!"{n}"))),
        ("declTermPremises", Json.arr (d.declTermPremises.map (fun n => s!"{n}"))),
        ("declExplicitConstants", Json.arr (d.declExplicitConstants.map (fun n => s!"{n}"))),
        ("declExplicitPremises", Json.arr (d.declExplicitPremises.map (fun n => s!"{n}"))),
        ("declAllPremises", Json.arr (d.declAllPremises.map (fun n => s!"{n}"))),
        ("declHammerRecommendation", Json.arr (d.declHammerRecommendation.map (fun n => s!"{n}"))),
        ("termPremisesToEndOfGoal", Json.arr (d.termPremisesToEndOfGoal.map (fun n => s!"{n}"))),
        ("explicitConstantsToEndOfGoal", Json.arr (d.explicitConstantsToEndOfGoal.map (fun n => s!"{n}"))),
        ("explicitPremisesToEndOfGoal", Json.arr (d.explicitPremisesToEndOfGoal.map (fun n => s!"{n}"))),
        ("allPremisesToEndOfGoal", Json.arr (d.allPremisesToEndOfGoal.map (fun n => s!"{n}"))),
        ("hammerRecommendationToEndOfGoal", Json.arr (d.hammerRecommendationToEndOfGoal.map (fun n => s!"{n}")))
        -- ("curGoalCount", Json.num d.curGoalCount) -- Only for testing
      ]
    )
  for jsonObj in jsonRes do
    IO.println jsonObj.compress
  return 0

def trainingData (args : Cli.Parsed) : IO UInt32 :=
  let module := args.positionalArg! "module" |>.as! ModuleName
  trainingDataGivenModule module

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

-- Testing:
-- #eval trainingDataGivenModule `temp
-- #eval trainingDataGivenModule `Mathlib.Data.Prod.Basic
-- #eval trainingDataGivenModule `Mathlib.Data.Int.Defs
-- #eval trainingDataGivenModule `Mathlib.Data.Option.Basic
