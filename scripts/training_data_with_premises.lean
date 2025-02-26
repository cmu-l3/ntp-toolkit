import TrainingData.Frontend
import TrainingData.InfoTree.ToJson
import TrainingData.InfoTree.TacticInvocation.Basic
import TrainingData.Utils.Range
import TrainingData.Utils.HammerBlacklist
import TrainingData.Utils.SimpAllHint
import TrainingData.Utils.TheoremPrettyPrinting
import Mathlib.Data.String.Defs
import Mathlib.Lean.CoreM
import Batteries.Data.String.Basic
import Batteries.Data.String.Matcher
import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.Change
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.SimpRw
import Cli

open Lean Elab IO Meta Cli System DocGen4.Process SimpAllHint TheoremPrettyPrinting

def DeclIdMap := Std.HashMap String (List Json)

def addToMap (map : DeclIdMap) (declId : String) (jsonObj : Json) : DeclIdMap :=
  match map.get? declId with
  | some jsonList => map.insert declId (jsonObj :: jsonList)
  | none => map.insert declId [jsonObj]

def groupByDecl (idJsons : List (String × Json)) : IO DeclIdMap := do
  let mut map : DeclIdMap := Std.HashMap.empty
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

def getElabDeclOfTacticInvocation (elabDeclInfo : List ElabDeclInfo) (ti : TacticInvocation)
  : Option ElabDeclInfo := do
    let ⟨s, e⟩ := FileMap.stxRange ti.ctx.fileMap ti.info.stx
    elabDeclInfo.find? fun ⟨⟨s', e'⟩, _⟩ => s' <= s && e <= e'

def getElabDeclOfCompilationStep (elabDeclInfo : List ElabDeclInfo) (cmd : CompilationStep)
  : Option ElabDeclInfo := elabDeclInfo.find? (fun ⟨_, cmd'⟩ => cmd'.stx == cmd.stx)

def makeElabDeclId (info: ElabDeclInfo) (module: Name) (hash: String) : String :=
  let ⟨x, y⟩ := info.fst.fst
  let declId := s!"{module}.{x}_{y}.{hash}"
  declId

def getInvocationTrees (trees : List InfoTree) : IO (List InfoTree) := do
  let trees := trees.flatMap InfoTree.retainTacticInfo
  let trees := trees.flatMap InfoTree.retainOriginal
  let trees := trees.flatMap InfoTree.retainSubstantive
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
    -- (magic value) if this command is a declaration like theorem/def T := proof/definition
    -- then the := syntax occurs at `stx[1][3][0]`
    if info.stx[1][3][0].getAtomVal == ":=" then
      let declStart := info.stx.getPos?.getD 0
      let proofStart := info.stx[1][3].getPos?.getD 0
      let proofEnd := info.stx.getTailPos?.getD 0
      let moduleSource ← moduleSource module
      let decl := (Substring.mk moduleSource declStart proofStart).toString
      let proof := (Substring.mk moduleSource proofStart proofEnd).toString
      return decl
    else
      return ""

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

def Name.isTheoremOrAxiom (name : Name) : CoreM Bool := do
  let .some ci := (← getEnv).find? name
    | throwError "Name.isTheorem :: Cannot find name {name}"
  match ci with
  | .thmInfo _ => return true
  | .axiomInfo _ => return true
  | _ => return false

def Name.isAuxLemma : Name → Bool
| .num (.str _ "_auxLemma") _ => true
| _ => false

/-- Takes in a constant name and checks whether it should be unfolded using `shouldUnfold`. If the constant should be unfolded,
    then returns all of the constants that appear in the unfolded result as a nameset. Otherwise, returns a set just containing
    the constant name. `unfoldConstantName` should never return any names that are supposed to be unfolded, so if a name is
    supposed to be unfolded as indicated by `shouldUnfold`, then even if its constant can't actually be unfolded, we do not
    return the name itself. -/
def unfoldConstantName (constName : Name) (constantsMap : Std.HashMap Name ConstantInfo) (shouldUnfold : Name → Bool) : NameSet := Id.run do
  if shouldUnfold constName then
    let some constInfo := constantsMap.get? constName
      | return ∅ -- If `n` cannot be unfolded, then return the empty set because `n` shouldn't appear in the output`
    return constInfo.getUsedConstantsAsSet
  else
    return (∅ : NameSet).insert constName

structure TrainingData where
  declId : String
  declName : String
  srcUpToTactic : String
  declUpToTactic : String
  state : String
  nextTactic : Option String -- `none` if the proof is completed in term mode
  nextTacticHammerRecommendation : Std.HashMap Name SimpAllHint
  declHammerRecommendation : Std.HashMap Name SimpAllHint
deriving Inhabited

/-- If the same name appears in assigned multiple distinct hints over the course of the data extraction, `mergeSimpAllHints` determines what its
    final hint should be. The priority structure `mergeSimpAllHints` applies to hints is as follows:
    - `simpErase` > `unmodified` > `backwardOnly` > `simpPreOnly` > `simpPostOnly` > `simpPreAndBackward` > `simpPostAndBackward` > `notInSimpAll`

    Most of these choices are arbitrary. The main thing is that `simpErase` is always preferred and `notInSimpAll` is never preferred over something else -/
def mergeSimpAllHints (h1 h2 : SimpAllHint) : SimpAllHint :=
  match h1, h2 with
  | simpErase, _ | _, simpErase => simpErase
  | unmodified, _ | _, unmodified => unmodified
  | backwardOnly, _ | _, backwardOnly => backwardOnly
  | simpPreOnly, _ | _, simpPreOnly => simpPreOnly
  | simpPostOnly, _ | _, simpPostOnly => simpPostOnly
  | simpPreAndBackward, _ | _, simpPreAndBackward => simpPreAndBackward
  | simpPostAndBackward, _ | _, simpPostAndBackward => simpPostAndBackward
  | notInSimpAll, notInSimpAll => notInSimpAll

def updateHammerRecommendation (hammerRecommendation : Std.HashMap Name SimpAllHint) (name : Name) (hint : SimpAllHint) : Std.HashMap Name SimpAllHint :=
  match hammerRecommendation.get? name with
  | some h => hammerRecommendation.insert name $ mergeSimpAllHints h hint
  | none => hammerRecommendation.insert name hint

def mergeHammerRecommendations (hammerRecommendation1 hammerRecommendation2 : Std.HashMap Name SimpAllHint) : Std.HashMap Name SimpAllHint :=
  if hammerRecommendation1.size ≥ hammerRecommendation2.size then
    hammerRecommendation2.toArray.foldl (fun acc (n, h) => updateHammerRecommendation acc n h) hammerRecommendation1
  else
    hammerRecommendation1.toArray.foldl (fun acc (n, h) => updateHammerRecommendation acc n h) hammerRecommendation2

/-- This function uses `Lean.Elab.Tactic.elabSimpArgs` and `Lean.Elab.Tactic.mkSimpOnly` as references. Currently, the nature of the output ignores
    simprocs, though it may make sense to update this to include output pertaining to simprocs in the future. `simpLemmasFromTacticStx` ignores all
    lemmas that appear in the hammer blacklist. -/
def simpLemmasFromTacticStx (s : Syntax) : MetaM (Std.HashMap Name SimpAllHint) := do
  match s with
  | `(tactic| simp [$simpLemmas,*])
  | `(tactic| simp? [$simpLemmas,*])
  | `(tactic| simp?! [$simpLemmas,*])
  | `(tactic| simp_all [$simpLemmas,*])
  | `(tactic| simp_all? [$simpLemmas,*])
  | `(tactic| simp_all! [$simpLemmas,*])
  | `(tactic| simp_all?! [$simpLemmas,*])
  | `(tactic| simp_arith [$simpLemmas,*])
  | `(tactic| simp_arith! [$simpLemmas,*])
  | `(tactic| simpa [$simpLemmas,*])
  | `(tactic| simpa? [$simpLemmas,*])
  | `(tactic| simpa! [$simpLemmas,*])
  | `(tactic| simpa?! [$simpLemmas,*])
  | `(tactic| dsimp [$simpLemmas,*])
  | `(tactic| dsimp? [$simpLemmas,*])
  | `(tactic| dsimp?! [$simpLemmas,*])
  | `(tactic| simp only [$simpLemmas,*])
  | `(tactic| simp? only [$simpLemmas,*])
  | `(tactic| simp?! only [$simpLemmas,*])
  | `(tactic| simp_all only [$simpLemmas,*])
  | `(tactic| simp_all? only [$simpLemmas,*])
  | `(tactic| simp_all! only [$simpLemmas,*])
  | `(tactic| simp_all?! only [$simpLemmas,*])
  | `(tactic| simp_arith only [$simpLemmas,*])
  | `(tactic| simp_arith! only [$simpLemmas,*])
  | `(tactic| simpa only [$simpLemmas,*])
  | `(tactic| simpa? only [$simpLemmas,*])
  | `(tactic| simpa! only [$simpLemmas,*])
  | `(tactic| simpa?! only [$simpLemmas,*])
  | `(tactic| dsimp only [$simpLemmas,*])
  | `(tactic| dsimp? only [$simpLemmas,*])
  | `(tactic| dsimp?! only [$simpLemmas,*]) =>
    let simpLemmas := simpLemmas.getElems
    let mut res : Std.HashMap Name SimpAllHint := Std.HashMap.empty
    for simpLemma in simpLemmas do
      let simpLemma := simpLemma.raw
      if simpLemma.getKind == ``Lean.Parser.Tactic.simpErase then
        let id := simpLemma[1]
        match ← observing (realizeGlobalConstNoOverloadWithInfo id) with
        | .ok declName =>
          if (← Simp.isSimproc declName) then continue -- Ignore `declName` if it is a simproc
          else if isBlackListed s!"{declName}" then continue -- Ignore `declName` if it appears in `hammerRecommendationBlackList`
          res := updateHammerRecommendation res declName simpErase
        | _ => -- If `realizeGlobalConstNoOverloadWithInfo id` failed, `id` is a local fvar or builtin simproc. We ignore it in either case.
          continue
      else if simpLemma.getKind == ``Lean.Parser.Tactic.simpLemma then
        let hasLeftArrow := !simpLemma[1].isNone -- `simpLemma` contains either `←` or `<-`
        let simpAllHint ←
          if simpLemma[0].isNone then
            if hasLeftArrow then pure backwardOnly
            else pure unmodified
          else if simpLemma[0][0].getKind == ``Parser.Tactic.simpPost then -- simpPost corresponds to `↑`
            if hasLeftArrow then pure simpPostAndBackward
            else pure simpPostOnly
          else if simpLemma[0][0].getKind == ``Parser.Tactic.simpPre then -- simpPre corresponds to `↓`
            if hasLeftArrow then pure simpPreAndBackward
            else pure simpPreOnly
          else
            throwError "simpAllRecommendationFromTacticStx :: Unable to parse simpLemma syntax {simpLemma}"
        let term := simpLemma[2]
        match ← observing (realizeGlobalConstNoOverloadWithInfo term) with
        | .ok declName =>
          if (← Simp.isSimproc declName) then continue -- Ignore `declName` if it is a simproc
          else if isBlackListed s!"{declName}" then continue -- Ignore `declName` if it appears in `hammerRecommendationBlackList`
          res := updateHammerRecommendation res declName simpAllHint
        | _ => -- `term` could be a local fvar, a builtin simproc, or non-identifer expression. In any of these cases, we ignore it
          continue
      else if simpLemma.getKind == ``Lean.Parser.Tactic.simpStar then
        continue
      else
        throwUnsupportedSyntax
    return res
  | _ => return Std.HashMap.empty

/-- It is possible for some tactics such as `simp_rw` to invoke rewrite lemmas that do not appear in the final proof term (for instance, to direct unfolding).
    This function returns the set of rewrite lemmas that appear in the tactic syntax (and annotates them with `unmodified`, `backwardOnly`, or `notInSimpAll`),
    starting for the initial hashmap `hammerRecommendation` -/
def rwLemmasFromTacticStx (s : Syntax) (hammerRecommendation : Std.HashMap Name SimpAllHint) : MetaM (Std.HashMap Name SimpAllHint) := do
  match s with
  | `(tactic| simp_rw $rws:rwRuleSeq) =>
    -- Code for iterating through `rws` adapted from `Mathlib.Tactic.withSimpRWRulesSeq`
    let rules := rws.raw[1].getArgs
    let numRules := (rules.size + 1) / 2
    let mut hammerRecommendation := hammerRecommendation
    for i in [:numRules] do
      let rule := rules[i * 2]!
      let hasLeftArrow := !rule[0].isNone
      let simpAllHint := if hasLeftArrow then backwardOnly else unmodified
      let term := rule[1]
      match ← observing (realizeGlobalConstNoOverloadWithInfo term) with
      | .ok declName =>
        if (← Simp.isSimproc declName) then continue -- Ignore `declName` if it is a simproc
        else if isBlackListed s!"{declName}" then continue -- Ignore `declName` if it appears in `hammerRecommendationBlackList`
        hammerRecommendation := updateHammerRecommendation hammerRecommendation declName simpAllHint
      | _ => -- `term` could be a local fvar, a builtin simproc, or non-identifer expression. In any of these cases, we ignore it
        continue
    return hammerRecommendation
  | `(tactic| rw $rws:rwRuleSeq) =>
    -- Code for iterating through `rws` adapted from `Mathlib.Tactic.withSimpRWRulesSeq`
    let rules := rws.raw[1].getArgs
    let numRules := (rules.size + 1) / 2
    let mut hammerRecommendation := hammerRecommendation
    for i in [:numRules] do
      let rule := rules[i * 2]!
      let term := rule[1]
      match ← observing (realizeGlobalConstNoOverloadWithInfo term) with
      | .ok declName =>
        if (← Simp.isSimproc declName) then continue -- Ignore `declName` if it is a simproc
        else if isBlackListed s!"{declName}" then continue -- Ignore `declName` if it appears in `hammerRecommendationBlackList`
        hammerRecommendation := updateHammerRecommendation hammerRecommendation declName notInSimpAll
      | _ => -- `term` could be a local fvar, a builtin simproc, or non-identifer expression. In any of these cases, we ignore it
        continue
    return hammerRecommendation
  | _ => return hammerRecommendation

/-- Creates a `TrainingData` object based on the provided tactic invocation. The `declHammerRecommendation` field of the created is provisional
    because there may be more than one tactic that must be taken into account to populate this field. -/
def trainingDataGivenTactic (elabDeclInfo : ElabDeclInfo) (module : ModuleName) (hash : String) (i : TacticInvocation) (declName : String) : IO TrainingData := do
  let declId := makeElabDeclId elabDeclInfo module hash
  let sourceUpToTactic := Substring.mk (← moduleSource module) 0 (i.info.stx.getPos?.getD 0)
  let declUpToTactic := Substring.mk (← moduleSource module)
    (elabDeclInfo.snd.stx.getPos?.getD 0) (i.info.stx.getPos?.getD 0)

  let state := (Format.joinSep (← i.goalState) "\n").pretty

  let nextTactic ← tacticPP module i

  let mainGoalBeforeTactic ← i.runMetaM (fun mvarId => pure mvarId)

  let hammerRecommendation ← i.runMetaMGoalsAfter
    (fun _ => do
      -- Gather all constants that appear in the proof term generated by the current tactic
      let constantsMap := (← getEnv).constants.map₁
      let termConstantNamesNoUnfolding := (← instantiateMVars (mkMVar mainGoalBeforeTactic)).headBeta.getUsedConstantsAsSet
      -- Unfold all auxiliary lemmas in `termConstantNamesNoUnfolding`
      let mut termConstantsNameSet : NameSet := ∅
      for constName in termConstantNamesNoUnfolding do
        termConstantsNameSet := termConstantsNameSet.append $ unfoldConstantName constName constantsMap Name.isAuxLemma
      let termConstants := termConstantsNameSet.toArray
      -- Filter `termConstants` to only included constants that are lemmas (i.e. Prop-typed) and not blacklisted
      let termPremises ← termConstants.filterM (fun n => do pure ((← Name.isTheoremOrAxiom n) && !isBlackListed s!"{n}"))
      -- Build `hammerRecommendation` starting with any `simp` lemmas that appear in the tactic stx (not including blacklisted lemmas)
      let mut hammerRecommendation ← simpLemmasFromTacticStx i.info.stx
      hammerRecommendation ← rwLemmasFromTacticStx i.info.stx hammerRecommendation
      -- Add all of the theorems in `nextTacticAllPremises` that don't appear in `simpLemmasFromTacticStx i.info.stx`
      for thm in termPremises do
        hammerRecommendation := updateHammerRecommendation hammerRecommendation thm notInSimpAll
      pure hammerRecommendation
    )

  let data := {
      declId := declId,
      declName := declName,
      srcUpToTactic := sourceUpToTactic.toString,
      declUpToTactic := declUpToTactic.toString,
      state := state,
      nextTactic := nextTactic,
      nextTacticHammerRecommendation := hammerRecommendation
      declHammerRecommendation := hammerRecommendation -- This field will be updated in `trainingDataGivenModule`
    }
  return data

end Lean.Elab.TacticInvocation

open TacticInvocation

def trainingDataToJson (d : TrainingData) : Json :=
  Json.mkObj [
    ("declName", Json.str d.declName),
    ("srcUpToTactic", Json.str d.srcUpToTactic),
    ("declUpToTactic", Json.str d.declUpToTactic),
    ("state", Json.str d.state),
    ("nextTactic", match d.nextTactic with | some nextTactic => Json.str nextTactic | none => Json.null),
    ("nextTacticHammerRecommendation", Json.arr (d.nextTacticHammerRecommendation.toArray.map (fun x => s!"{x}"))),
    ("declHammerRecommendation", Json.arr (d.declHammerRecommendation.toArray.map (fun x => s!"{x}")))
  ]

/-- Given a theorem `v`, creates a `TrainingData` object related to `v`, prints it in JSON format to stdout, and returns the final
    `declHammerRecommendation` fiedl which may be needed to update other `TrainingData` objects in `trainingDataGivenModule`. If
    other `TrainingData` objects related to this theorem have previous been produced, then `declHammerRecommendation` is passed
    in as well so that the information from there can be included. -/
def printTrainingDataGivenTheoremVal (elabDeclInfo : ElabDeclInfo) (module : ModuleName) (hash : String) (cmd : CompilationStep) (v : TheoremVal)
  (declHammerRecommendation : Option (Std.HashMap Name SimpAllHint)) : MetaM (Std.HashMap Name SimpAllHint) := do
  let thmInfo ← Info.ofConstantVal' v.toConstantVal
  let sourceUpToTactic := Substring.mk (← moduleSource module) 0 (cmd.stx.getTailPos?.getD 0)
  let declUpToTactic := Substring.mk (← moduleSource module) (cmd.stx.getPos?.getD 0) (cmd.stx.getTailPos?.getD 0)

  let vType := v.type
  let Expr.mvar m ← mkFreshExprMVar vType
    | throwError "trainingDataGivenTheoremVal :: Failed to build an mvar of type {vType}"
  let (_, m) ← m.introNP thmInfo.args.size
  let state := (← withOptions (fun o => (o.set `pp.notation false).set `pp.fullNames true) $ Meta.ppGoal m).pretty

  let hammerRecommendation ← m.withContext do
    -- Gather all constants that appear in the proof term generated by the current tactic
    let constantsMap := (← getEnv).constants.map₁
    let termConstantNamesNoUnfolding := v.value.getUsedConstantsAsSet
    -- Unfold all auxiliary lemmas in `termConstantNamesNoUnfolding`
    let mut termConstantsNameSet : NameSet := ∅
    for constName in termConstantNamesNoUnfolding do
      termConstantsNameSet := termConstantsNameSet.append $ unfoldConstantName constName constantsMap Name.isAuxLemma
    let termConstants := termConstantsNameSet.toArray
    -- Filter `termConstants` to only included constants that are lemmas (i.e. Prop-typed) and not blacklisted
    let termPremises ← termConstants.filterM (fun n => do pure ((← Name.isTheoremOrAxiom n) && !isBlackListed s!"{n}"))
    -- Every `SimpAllHint` should be `notInSimpAll` for term proofs
    let hammerRecommendation := Std.HashMap.ofList $ termPremises.toList.map (fun thm => (thm, SimpAllHint.notInSimpAll))
    match declHammerRecommendation with
    | none => pure hammerRecommendation
    | some declHammerRecommendation => pure $ mergeHammerRecommendations hammerRecommendation declHammerRecommendation

  let data : TrainingData := {
      declId := makeElabDeclId elabDeclInfo module hash,
      declName := v.name.toString,
      srcUpToTactic := sourceUpToTactic.toString,
      declUpToTactic := declUpToTactic.toString,
      state := state,
      nextTactic := none,
      nextTacticHammerRecommendation := hammerRecommendation,
      declHammerRecommendation := hammerRecommendation,
    }
  IO.println s!"{(trainingDataToJson data).compress}"
  return data.declHammerRecommendation

def trainingDataGivenModule (module : ModuleName) (includeDebugMessages : Bool) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  let infos ← getElabDeclInfo (← moduleInfoTrees module)
  let compilationSteps ← compileModule module
  let trees ← getInvocationTrees $ compilationSteps.flatMap (fun c => c.trees)
  let hash ← generateRandomHash
  let mut dataArr : Array TrainingData := #[]
  -- Extract data from tactics
  for t in trees do
    for t in t.tactics do
      match getElabDeclOfTacticInvocation infos t with
      | some elabDeclInfo => do
        if includeDebugMessages then
          IO.println s!"Processing tactic {← t.tacticPP module}"
        let tDeclName ←
          match t.ctx.parentDecl? with
          | some n => pure s!"{n}"
          | none =>
            if includeDebugMessages then
              IO.println s!"No parent declaration found for tactic {← t.tacticPP module}"
            pure ""
        let data ←
          try t.trainingDataGivenTactic elabDeclInfo module hash tDeclName
          catch e =>
            if includeDebugMessages then
              IO.println s!"Error processing tactic {← t.tacticPP module}: {e.toString}"
            continue
        if includeDebugMessages then
          IO.println s!"{← t.tacticPP module} successfully processed (declName: {tDeclName})"
        dataArr := dataArr.push data
      | none => pure ()
  -- Perform a second pass to gather data that potentially spans multiple tactics
  let mut activeDeclId : String := (dataArr.getD 0 default).declId
  let mut declHammerRecommendations : Std.HashMap String (Std.HashMap Name SimpAllHint) := Std.HashMap.empty
  let mut activeDeclName : String := (dataArr.getD 0 default).declName
  let mut activeDeclHammerRecommendation : Std.HashMap Name SimpAllHint := (dataArr.getD 0 default).nextTacticHammerRecommendation
  for i in [:dataArr.size] do
    let curTacticData := dataArr[i]!
    if curTacticData.declId != activeDeclId then -- We've changed declarations
      -- For each `data` in `dataArr` such that `data.declId == activeDeclId`, update the `declHammerRecommendation` field
      for j in [:i] do -- Decrement `idx = i - j - 1` until we find a `declId` that doesn't match `activeDeclId`
        let idx := i - j - 1
        let data := dataArr[idx]!
        if data.declId != activeDeclId then
          break -- Once we find one tactic that doesn't match the activeDeclId, no previous tactic will match the activeDeclId
        dataArr := dataArr.set! idx { data with declHammerRecommendation := activeDeclHammerRecommendation }
      -- Since we've started a new `declId`, add `activeDeclHammerRecommendation` to `declHammerRecommendations`
      declHammerRecommendations := declHammerRecommendations.insert activeDeclName activeDeclHammerRecommendation
      -- Reset `activeDeclName` and `activeDeclHammerRecommendation`
      activeDeclId := curTacticData.declId
      activeDeclName := curTacticData.declName
      activeDeclHammerRecommendation := curTacticData.nextTacticHammerRecommendation
    else -- `curTacticData.declId == activeDeclId`
      activeDeclHammerRecommendation := mergeHammerRecommendations activeDeclHammerRecommendation curTacticData.nextTacticHammerRecommendation
  -- Update `declHammerRecommendation` field for the final declaration
  for j in [:dataArr.size] do -- Decrement `idx = firstPassData.size - j - 1` until we find a `declId` that doesn't match `activeDeclId`
    let idx := dataArr.size - j - 1
    let data := dataArr[idx]!
    if data.declId != activeDeclId then
      break -- Once we find one tactic that doesn't match the activeDeclId, no previous tactic will match the activeDeclId
    dataArr := dataArr.set! idx { data with declHammerRecommendation := activeDeclHammerRecommendation }
    declHammerRecommendations := declHammerRecommendations.insert activeDeclName activeDeclHammerRecommendation
  -- Extract and print data from from overall declarations (including information in proof terms that do not appear in any tactic)
  for c in compilationSteps do
    for (cmd, ci) in c.diff.map (fun i => (c, i)) do
      match ci with
      | .thmInfo v =>
        if !Name.isAuxLemma v.name then
          match getElabDeclOfCompilationStep infos cmd with
          | some elabDeclInfo =>
            match declHammerRecommendations.get? v.name.toString with
            | some vDeclHammerRecommendation =>
              let vDeclHammerRecommendation ← CoreM.withImportModules #[`Mathlib.Lean.PrettyPrinter.Delaborator, `Lean.PrettyPrinter, module]
                (printTrainingDataGivenTheoremVal elabDeclInfo module hash cmd v (some vDeclHammerRecommendation)).run'
              /- In addition to printing the JSON entry corresponding to `v` as a whole (which `printTrainingDataGivenTheoremVal` already does),
                 we can now print the JSON entry for each of `v`'s tactic states with a fully updated decl hammer recommendation -/
              let mut encounteredDecl := false
              for data in dataArr do
                if data.declName == v.name.toString then
                  let mergedRecommendation := mergeHammerRecommendations data.declHammerRecommendation vDeclHammerRecommendation
                  IO.println (trainingDataToJson {data with declHammerRecommendation := mergedRecommendation}).compress
                  encounteredDecl := true
                else if encounteredDecl then -- All entries of the same decl are contiguous in `dataArr` so if we reach this we've fixed all necessary entries
                  break
            | none => -- No need to update `dataArr` since the current theorem does not appear in `dataArr`
              let _ ← CoreM.withImportModules #[`Mathlib.Lean.PrettyPrinter.Delaborator, `Lean.PrettyPrinter, module]
                (printTrainingDataGivenTheoremVal elabDeclInfo module hash cmd v none).run'
          | none => continue
      | _ => continue
  return 0

def trainingData (args : Cli.Parsed) : IO UInt32 :=
  let module := args.positionalArg! "module" |>.as! ModuleName
  let includeDebugMessages := args.flag! "includeDebugMessages" |>.as! Bool
  trainingDataGivenModule module includeDebugMessages

/-- Setting up command line options and help text for `lake exe training_data_with_premises`. -/
def training_data : Cmd := `[Cli|
  training_data VIA trainingData; ["0.0.1"]
"Export training data from the given file."

  FLAGS:
    includeDebugMessages : Bool; "Include debug messages in the output."

  ARGS:
    module : ModuleName; "Lean module to compile and export training data."

  EXTENSIONS:
    defaultValues! #[
      ("includeDebugMessages", "false")
    ]
]

/-- `lake exe training_data_with_premises` -/
def main (args : List String) : IO UInt32 :=
  training_data.validate args

-- Testing:
-- #eval Command.liftTermElabM $ trainingDataGivenModule `temp
-- #eval Command.liftTermElabM $ trainingDataGivenModule `Mathlib.Data.Prod.Basic
-- #eval Command.liftTermElabM $ trainingDataGivenModule `Mathlib.Data.Int.Defs
-- #eval Command.liftTermElabM $ trainingDataGivenModule `Mathlib.Data.Option.Basic
-- #eval Command.liftTermElabM $ trainingDataGivenModule `Mathlib.Data.Set.Basic
