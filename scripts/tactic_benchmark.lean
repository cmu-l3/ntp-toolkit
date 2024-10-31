import TrainingData.Frontend
import Mathlib.Control.Basic
import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.ToExpr
import Aesop
import Lean.Util.Trace
import Duper
import QuerySMT
import Hammer
import Cli

open Lean Core Elab IO Meta Term Tactic -- All the monads!

set_option autoImplicit true

def useAesop : TacticM Unit := do evalTactic (← `(tactic| aesop))
def useExact? : TacticM Unit := do evalTactic (← `(tactic| exact?))
def useRfl : TacticM Unit := do evalTactic (← `(tactic| intros; rfl))
def useSimpAll : TacticM Unit := do evalTactic (← `(tactic| intros; simp_all))
def useOmega : TacticM Unit := do evalTactic (← `(tactic| intros; omega))
def useDuper : TacticM Unit := do evalTactic (← `(tactic| duper [*]))
def useQuerySMT : TacticM Unit := do evalTactic (← `(tactic| querySMT))
def useHammer (hammerRecommendation : Array String) : TacticM Unit := do
  let hammerRecommendation : Array Name := hammerRecommendation.map String.toName
  let hammerRecommendation : Array Ident := hammerRecommendation.map mkIdent
  let hammerRecommendation : Array Term := hammerRecommendation.map (fun i => ⟨i.raw⟩)
  evalTactic (← `(tactic| hammer [*, $(hammerRecommendation),*])) -- **TODO** Check that this syntax includes `*` so that local hypotheses will be available

/--
Compile the designated module, and run a monadic function with each new `ConstantInfo`,
with the `Environment` as it was *before* the command which created that declaration.

(Internal declarations according to `Name.isBlackListed` are skipped.)

If `withImportsDir` is provided, then `runAtDecls` uses the version of the file contained in the `WithImports` directory
-/
def runAtDecls (mod : Name) (withImportsDir : Option String := none) (tac : ConstantInfo → MetaM (Option α)) : MLList IO (ConstantInfo × α) := do
  let fileName ←
    match withImportsDir with
    | none => pure (← findLean mod).toString
    | some withImportsDir => pure (← findLeanWithImports mod "mathlib" withImportsDir).toString
  let steps :=
    match withImportsDir with
    | none => compileModule' mod
    | some withImportsDir => compileModuleWithImports' mod "mathlib" withImportsDir
  let targets := steps.bind fun c => (MLList.ofList c.diff).map fun i => (c, i)

  targets.filterMapM fun (cmd, ci) => do
    for m in cmd.msgs do IO.eprintln (bombEmoji ++ (← m.data.toString))
    unless cmd.msgs.isEmpty do
      throw <| IO.userError s!"Unexpected messages in: {mod} during elaboration of {cmd.stx}"

    let options := ({} : KVMap).insert `maxHeartbeats (.ofNat 20000)
    let ctx := { fileName, options, fileMap := default }
    let state := { env := cmd.before }
    -- From `IO` to `CoreM`:
    Prod.fst <$> (CoreM.toIO · ctx state) do
      if ← ci.name.isBlackListed then
        pure none
      else
        -- From `CoreM` to `MetaM`:
        MetaM.run' (ctx := {}) (s := {}) do
          match ← tac ci with
          | some r => pure (ci, r)
          | none => pure none

/-- Like `runAtDecls` but only returns the output for a single declaration. If the declaration cannot be found or if the tactic fails, `none` is returned. -/
def runAtDecl (mod : Name) (declName : Name) (withImportsDir : Option String := none) (tac : ConstantInfo → MetaM (Option α)) : IO (Option (ConstantInfo × α)) := do
  let fileName ←
    match withImportsDir with
    | none => pure (← findLean mod).toString
    | some withImportsDir => pure (← findLeanWithImports mod "mathlib" withImportsDir).toString
  let steps :=
    match withImportsDir with
    | none => compileModule' mod
    | some withImportsDir => compileModuleWithImports' mod "mathlib" withImportsDir
  let targets := steps.bind fun c => (MLList.ofList c.diff).map fun i => (c, i)
  for (cmd, ci) in targets do
    if ci.name == declName then
      let options := ({} : KVMap).insert `maxHeartbeats (.ofNat 20000)
      let ctx := { fileName, options, fileMap := default }
      let state := { env := cmd.before }
      -- From `IO` to `CoreM`:
      let res ← Prod.fst <$> (CoreM.toIO · ctx state) do
        if ← ci.name.isBlackListed then
          IO.eprintln s!"runAtDecl :: {ci.name} is blacklisted and is therefore not an eligible declaration for runAtDecl"
          return none
        else
          -- From `CoreM` to `MetaM`:
          MetaM.run' (ctx := {}) (s := {}) do
            match ← tac ci with
            | some r => pure $ some (ci, r)
            | none => pure none
      return res
  IO.eprintln s!"Unable to find declaration {declName} in module {mod}"
  return none

inductive GeneralResultType
| success
| failure
| subgoals
| notDefEq
deriving Repr, BEq

instance : ToString GeneralResultType where
  toString := fun
  | .success => "success"
  | .failure => "failure"
  | .subgoals => "subgoals"
  | .notDefEq => "notDefEq"

inductive HammerResultType
| success
| noJSON -- For declarations that the JSON file doesn't have data for (currently, these are declarations that are proven without entering tactic mode)
| simpPreprocessingFailure -- For declarations where `hammer` encounters an error during the simp preprocessing stage
| tptpTranslationFailure -- For declarations that cannot be translated to the external prover's format (currently TPTP's higher-order logic format)
| externalProverFailure -- For declarations that can be successfully translated but cannot be proven by the external prover (currently Zipperposition)
| duperFailure -- For declarations successfully translated and proven by the external prover but return proofs that Duper can't reconstruct
| proofFitFailure -- For declarations successfully proven by Duper's proof reconstruction, but returns proofs that yield some sort of error when applied
| miscFailure -- For hammer failures that don't fall into one of the previous five categories
| subgoals -- For declarations that are partially proven but have remaining subgoals even after the tactic is run
| notDefEq -- For declarations for which a proof is found but the proof is not definitionally equal to the expected proof
deriving Repr, BEq

instance : ToString HammerResultType where
  toString := fun
  | .success => "success"
  | .noJSON => "noJSON"
  | .simpPreprocessingFailure => "simpPreprocessingFailure"
  | .tptpTranslationFailure => "tptpTranslationFailure"
  | .externalProverFailure => "externalProverFailure"
  | .duperFailure => "duperFailure"
  | .proofFitFailure => "proofFitFailure"
  | .miscFailure => "miscFailure"
  | .subgoals => "subgoals"
  | .notDefEq => "notDefEq"

inductive QuerySMTResultType
| success
| noJSON -- For declarations that the JSON file doesn't have data for (currently, this is never thrown because the current querySMT evaluation doesn't search for premises)
| skolemizationFailure -- For declarations where `querySMT` encounters an error during the initial skolemization
| smtTranslationFailure -- For declarations where `querySMT` throws a translation error
| externalProverFailure -- For declarations that can be successfully translated but cannot be proven by the external prover (currently cvc5)
| hintParsingFailure -- For declarations where `querySMT` encounters an error parsing the external prover's hints
| selectorConstructionFailure -- For declarations where `querySMT` encounters an error constructing a datatype's selectors
| duperFailure -- For declarations successfully translated and proven by the external prover but return proofs that Duper can't reconstruct
| proofFitFailure -- For declarations successfully proven by Duper's proof reconstruction, but returns proofs that yield some sort of error when applied
| miscFailure -- For `querySMT` failures that don't fall into one of the previous categories
| subgoals -- For declarations that are partially proven but have remaining subgoals even after the tactic is run
| notDefEq -- For declarations for which a proof is found but the proof is not definitionally equal to the expected proof
deriving Repr, BEq

instance : ToString QuerySMTResultType where
  toString := fun
  | .success => "success"
  | .noJSON => "noJSON"
  | .skolemizationFailure => "skolemizationFailure"
  | .smtTranslationFailure => "smtTranslationFailure"
  | .externalProverFailure => "externalProverFailure"
  | .hintParsingFailure => "hintParsingFailure"
  | .selectorConstructionFailure => "selectorConstructionFailure"
  | .duperFailure => "duperFailure"
  | .proofFitFailure => "proofFitFailure"
  | .miscFailure => "miscFailure"
  | .subgoals => "subgoals"
  | .notDefEq => "notDefEq"

structure GeneralResult where
  type : GeneralResultType
  seconds : Float
  heartbeats : Nat

structure HammerResult where
  type : HammerResultType
  seconds : Float
  heartbeats : Nat

structure QuerySMTResult where
  type : QuerySMTResultType
  seconds : Float
  heartbeats : Nat

def withSeconds [Monad m] [MonadLiftT BaseIO m] (act : m α) : m (α × Float) := do
  let start ← IO.monoNanosNow
  let a ← act
  let stop ← IO.monoNanosNow
  return (a, (stop - start).toFloat / 1000000000)

/--
Compile the designated module, select declarations satisfying a predicate,
and run a tactic on the type of each declaration.
-/
def runTacticAtDecls (mod : Name) (decls : ConstantInfo → CoreM Bool) (tac : TacticM Unit) :
  MLList IO (ConstantInfo × GeneralResult) := do
  runAtDecls mod none fun ci => do
    if ! (← decls ci) then return none
    let g ← mkFreshExprMVar ci.type
    let ((gs, heartbeats), seconds) ← withSeconds <| withHeartbeats <|
      try? <| TermElabM.run' (do
        Tactic.run g.mvarId! tac)
        (ctx := {declName? := `fakeDecl, errToSorry := false})
    let type : GeneralResultType ← match gs with
    | none => pure .failure
    | some (_ :: _) => pure .subgoals
    | some [] =>
      match ci.value? with
      | none => pure .success
      | some v =>
        if ← isProp ci.type then
          pure .success
        else
        match ← try? (isDefEq g v) with
        | none
          -- In this case we should perhaps return an "uncertain" value.
          -- The problem is that `v` may contain constants generated by the simplifier
          -- during elaboration of the original proof,
          -- and which aren't in the current environment, so we can't really compare `g` and `v`
        | some false => pure .notDefEq
        | some true => pure .success
    return some ⟨type, seconds, heartbeats⟩

def runHammerAtDecls (mod : Name) (decls : ConstantInfo → MetaM Bool) (withImportsPath : String) (jsonDir : String) :
  MLList IO (ConstantInfo × HammerResult) := do
  runAtDecls mod (some withImportsPath) fun ci => do
    if ! (← decls ci) then return none
    let g ← mkFreshExprMVar ci.type
    -- Find JSON file corresponding to current `mod`
    let fileName := (← findJSONFile mod "mathlib" jsonDir).toString
    let jsonObjects ← IO.FS.lines fileName
    let json ← IO.ofExcept $ jsonObjects.mapM Json.parse
    -- Find `declHammerRecommendation` corresponding to current `ci`
    let mut ciEntry := Json.null
    for jsonEntry in json do
      let jsonDeclName ← IO.ofExcept $ jsonEntry.getObjVal? "declName"
      let curDeclName ← IO.ofExcept $ jsonDeclName.getStr?
      if curDeclName == s!"{ci.name}" then
        ciEntry := jsonEntry
        break
    if ciEntry.isNull then
      return some ⟨.noJSON, 0.0, 0⟩
    let hammerRecommendation ← IO.ofExcept $ ciEntry.getObjVal? "declHammerRecommendation"
    let hammerRecommendation ← IO.ofExcept $ hammerRecommendation.getArr?
    let hammerRecommendation ← IO.ofExcept $ hammerRecommendation.mapM Json.getStr?
    let ((res, heartbeats), seconds) ← withSeconds <| withHeartbeats <|
      try
        TermElabM.run' (do
          dbg_trace "About to use hammer for {ci.name} (recommendation: {hammerRecommendation})"
          let gs ← Tactic.run g.mvarId! $ useHammer hammerRecommendation
          match gs with
          | [] => pure .success -- Don't need to case on whether `ci.type` is a Prop because we only evaluate the hammer on Prop declarations
          | _ :: _ => pure .subgoals)
          (ctx := {declName? := `fakeDecl, errToSorry := false})
      catch e =>
        if ← Hammer.errorIsSimpPreprocessingError e then pure .simpPreprocessingFailure
        else if ← Hammer.errorIsTranslationError e then pure .tptpTranslationFailure
        else if ← Hammer.errorIsExternalSolverError e then pure .externalProverFailure
        else if ← Hammer.errorIsDuperSolverError e then pure .duperFailure
        else if ← Hammer.errorIsProofFitError e then pure .proofFitFailure
        else if "tactic 'simp' failed".isPrefixOf (← e.toMessageData.toString) then pure .simpPreprocessingFailure
        else if "tactic 'simp_all' failed".isPrefixOf (← e.toMessageData.toString) then pure .simpPreprocessingFailure
        else pure .miscFailure
    return some ⟨res, seconds, heartbeats⟩

/-- Like `runHammerAtDecls` but only tests a single declaration (indicated by `declName`). -/
def runHammerAtDecl (mod : Name) (declName : Name) (decls : ConstantInfo → MetaM Bool) (withImportsPath : String) (jsonDir : String) :
  IO (Option (ConstantInfo × HammerResult)) := do
  runAtDecl mod declName (some withImportsPath) fun ci => do
    if ! (← decls ci) then return none
    let g ← mkFreshExprMVar ci.type
    -- Find JSON file corresponding to current `mod`
    let fileName := (← findJSONFile mod "mathlib" jsonDir).toString
    let jsonObjects ← IO.FS.lines fileName
    let json ← IO.ofExcept $ jsonObjects.mapM Json.parse
    -- Find `declHammerRecommendation` corresponding to current `ci`
    let mut ciEntry := Json.null
    for jsonEntry in json do
      let jsonDeclName ← IO.ofExcept $ jsonEntry.getObjVal? "declName"
      let curDeclName ← IO.ofExcept $ jsonDeclName.getStr?
      if curDeclName == s!"{ci.name}" then
        ciEntry := jsonEntry
        break
    if ciEntry.isNull then
      return some ⟨.noJSON, 0.0, 0⟩
    let hammerRecommendation ← IO.ofExcept $ ciEntry.getObjVal? "declHammerRecommendation"
    let hammerRecommendation ← IO.ofExcept $ hammerRecommendation.getArr?
    let hammerRecommendation ← IO.ofExcept $ hammerRecommendation.mapM Json.getStr?
    let ((res, heartbeats), seconds) ← withSeconds <| withHeartbeats <|
      try
        TermElabM.run' (do
          dbg_trace "About to use hammer for {ci.name} (recommendation: {hammerRecommendation})"
          let gs ← Tactic.run g.mvarId! $ useHammer hammerRecommendation
          match gs with
          | [] => pure .success -- Don't need to case on whether `ci.type` is a Prop because we only evaluate the hammer on Prop declarations
          | _ :: _ => pure .subgoals)
          (ctx := {declName? := `fakeDecl, errToSorry := false})
      catch e =>
        if ← Hammer.errorIsSimpPreprocessingError e then pure .simpPreprocessingFailure
        else if ← Hammer.errorIsTranslationError e then pure .tptpTranslationFailure
        else if ← Hammer.errorIsExternalSolverError e then pure .externalProverFailure
        else if ← Hammer.errorIsDuperSolverError e then pure .duperFailure
        else if ← Hammer.errorIsProofFitError e then pure .proofFitFailure
        else if "tactic 'simp' failed".isPrefixOf (← e.toMessageData.toString) then pure .simpPreprocessingFailure
        else if "tactic 'simp_all' failed".isPrefixOf (← e.toMessageData.toString) then pure .simpPreprocessingFailure
        else pure .miscFailure
    return some ⟨res, seconds, heartbeats⟩

/-- **TODO** Add optional `jsonDir` String to add premises -/
def runQuerySMTAtDecls (mod : Name) (decls : ConstantInfo → MetaM Bool) :
  MLList IO (ConstantInfo × QuerySMTResult) := do
  runAtDecls mod none fun ci => do
    if ! (← decls ci) then return none
    let g ← mkFreshExprMVar ci.type
    let ((res, heartbeats), seconds) ← withSeconds <| withHeartbeats <|
      try
        TermElabM.run' (do
          let gs ← Tactic.run g.mvarId! $ useQuerySMT
          match gs with
          | [] => pure .success -- Don't need to case on whether `ci.type` is a Prop because we only evaluate the hammer on Prop declarations
          | _ :: _ => pure .subgoals)
          (ctx := {declName? := `fakeDecl, errToSorry := false})
      catch e =>
        if ← QuerySMT.errorIsSkolemizationError e then pure .skolemizationFailure
        else if ← QuerySMT.errorIsTranslationError e then pure .smtTranslationFailure
        else if ← QuerySMT.errorIsSolverError e then pure .externalProverFailure
        else if ← QuerySMT.errorIsHintParsingError e then pure .hintParsingFailure
        else if ← QuerySMT.errorIsSelectorConstructionError e then pure .selectorConstructionFailure
        else if ← QuerySMT.errorIsDuperError e then pure .duperFailure
        else if ← QuerySMT.errorIsProofFitError e then pure .proofFitFailure
        else pure .miscFailure
    return some ⟨res, seconds, heartbeats⟩

open Cli System

/-- Gives a string of 6 emojis indicating the success of the following `hammer` stages:
    - Finding premises relating to the current declaration (this can currently fail when the original declaration
      is proven without entering tactic mode)
    - Successfully performing simp preprocessing without encountering any errors (errors that could arise from `simp_all` not changing
      the tactic state are suppressed)
    - Translating the goal (and all of the premises needed to prove it) to TPTP
    - Receiving a proof from an external prover
    - Reconstructing the external proof with Duper
    - Applying Duper's proof to the goal state -/
def hammerResultTypeToEmojiString (res : HammerResultType) : String :=
  match res with
  | .success => checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji
  | .noJSON => bombEmoji ++ crossEmoji ++ crossEmoji ++ crossEmoji ++ crossEmoji ++ crossEmoji
  | .simpPreprocessingFailure => checkEmoji ++ bombEmoji ++ crossEmoji ++ crossEmoji ++ crossEmoji ++ crossEmoji
  | .tptpTranslationFailure => checkEmoji ++ checkEmoji ++ bombEmoji ++ crossEmoji ++ crossEmoji ++ crossEmoji
  | .externalProverFailure => checkEmoji ++ checkEmoji ++ checkEmoji ++ bombEmoji ++ crossEmoji ++ crossEmoji
  | .duperFailure => checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ bombEmoji ++ crossEmoji
  | .proofFitFailure => checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ bombEmoji
  | .miscFailure => bombEmoji ++ bombEmoji ++ bombEmoji ++ bombEmoji ++ bombEmoji ++ bombEmoji
  | .subgoals => checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ bombEmoji
  | .notDefEq => checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ bombEmoji

/-- Gives a string of 7 emojis indicating the success of the following `querySMT` stages:
    - Successfully performing skolemization
    - Successfully translating the goal to the SMT format
    - Receiving a proof from the external solver
    - Successfully parsing the hints returned by the external solver
    - Successfully constructing the selectors corresponding to the datatypes that appear in the problem
    - Successfully reconstructing the external proof with Duper
    - Applying Duper's proof to the goal state -/
def querySMTResultTypeToEmojiString (res : QuerySMTResultType) : String :=
  match res with
  | .success => checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji
  | .noJSON => bombEmoji -- `querySMTBenchmarkFromModule` doesn't yet look for additional premises
  | .skolemizationFailure => bombEmoji ++ crossEmoji ++ crossEmoji ++ crossEmoji ++ crossEmoji ++ crossEmoji ++ crossEmoji
  | .smtTranslationFailure => checkEmoji ++ bombEmoji ++ crossEmoji ++ crossEmoji ++ crossEmoji ++ crossEmoji ++ crossEmoji
  | .externalProverFailure => checkEmoji ++ checkEmoji ++ bombEmoji ++ crossEmoji ++ crossEmoji ++ crossEmoji ++ crossEmoji
  | .hintParsingFailure => checkEmoji ++ checkEmoji ++ checkEmoji ++ bombEmoji ++ crossEmoji ++ crossEmoji ++ crossEmoji
  | .selectorConstructionFailure => checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ bombEmoji ++ crossEmoji ++ crossEmoji
  | .duperFailure => checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ bombEmoji ++ crossEmoji
  | .proofFitFailure => checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ bombEmoji
  | .miscFailure => bombEmoji ++ bombEmoji ++ bombEmoji ++ bombEmoji ++ bombEmoji ++ bombEmoji ++ bombEmoji
  | .subgoals => -- First bombEmoji because subgoal likely came from `skolemizeAll`
    bombEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ bombEmoji
  | .notDefEq => checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ checkEmoji ++ bombEmoji

def tacticBenchmarkFromModule (module : ModuleName) (tac : TacticM Unit) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  let result := runTacticAtDecls module (fun _ => pure true) tac
  IO.println s!"{module}"
  for (ci, ⟨type, seconds, heartbeats⟩) in result do
    IO.println <| (if type == .success then checkEmoji else crossEmoji) ++ " " ++ ci.name.toString ++
      s!" ({seconds}s) ({heartbeats} heartbeats)"
  return 0

def hammerBenchmarkFromModule (module : ModuleName) (withImportsDir : String) (jsonDir : String) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  let result := runHammerAtDecls module (fun ci => try isProp ci.type catch _ => pure false) withImportsDir jsonDir
  IO.println s!"{module}"
  for (ci, ⟨type, seconds, heartbeats⟩) in result do
    IO.println <| (hammerResultTypeToEmojiString type) ++ " " ++ ci.name.toString ++
      s!" ({seconds}s) ({heartbeats} heartbeats)"
  return 0

def hammerBenchmarkAtDecl (module : ModuleName) (declName : Name) (withImportsDir : String) (jsonDir : String) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  let result ← runHammerAtDecl module declName (fun ci => try isProp ci.type catch _ => pure false) withImportsDir jsonDir
  match result with
  | some (ci, ⟨type, seconds, heartbeats⟩) =>
    IO.println $ (hammerResultTypeToEmojiString type) ++ " " ++ ci.name.toString ++ s!" ({seconds}s) ({heartbeats} heartbeats)"
    return 0
  | none =>
    IO.println s!"Encountered an issue attempting to run hammer benchmark at {declName} in module {module}"
    return 0

def querySMTBenchmarkFromModule (module : ModuleName) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  let result := runQuerySMTAtDecls module (fun ci => try isProp ci.type catch _ => pure false)
  IO.println s!"{module}"
  for (ci, ⟨type, seconds, heartbeats⟩) in result do
    IO.println <| (querySMTResultTypeToEmojiString type) ++ " " ++ ci.name.toString ++
      s!" ({seconds}s) ({heartbeats} heartbeats)"
  return 0

def tacticBenchmarkMain (args : Cli.Parsed) : IO UInt32 := do
  let module := args.positionalArg! "module" |>.as! ModuleName
  let tac ←
    if args.hasFlag "duper" then pure useDuper else
    if args.hasFlag "querySMT" then pure useQuerySMT else
    if args.hasFlag "aesop" then pure useAesop else
    if args.hasFlag "exact" then pure useExact? else
    if args.hasFlag "rfl" then pure useRfl else
    if args.hasFlag "simp_all" then pure useSimpAll else
    if args.hasFlag "omega" then pure useOmega else
    throw <| IO.userError "Specify a tactic, e.g. `--aesop`"
  tacticBenchmarkFromModule module tac

/-- Setting up command line options and help text for `lake exe tactic_benchmark`. -/
def tactic_benchmark : Cmd := `[Cli|
  tactic_benchmark VIA tacticBenchmarkMain; ["0.0.1"]
  "Run a customisable tactic at all declarations in a file."

  FLAGS:
    "aesop";       "Use `aesop`."
    "exact";       "Use `exact?`."
    "rfl";         "Use `intros; rfl`."
    "simp_all";    "Use `intros; simp_all`."
    "omega";       "Use `intros; omega`."
    "duper";       "Use `duper [*]`."
    "querySMT";    "Use `querySMT`."

  ARGS:
    module : ModuleName; "Lean module to compile and export InfoTrees."
]

/-- `lake exe tactic_benchmark` -/
def main (args : List String) : IO UInt32 :=
  tactic_benchmark.validate args

-- See `scripts/tactic_benchmark.sh` for a script to run this on all of Mathlib.

-- #eval tacticBenchmarkFromModule `temp useDuper
-- #eval tacticBenchmarkFromModule `temp useQuerySMT

-- Note: `tacticBenchmarkFromModule` requires that the tactic we want be imported in the module
