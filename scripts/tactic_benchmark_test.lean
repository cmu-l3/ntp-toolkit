import Scripts.Tactic_benchmark

/-
#eval tacticBenchmarkFromModule `temp useRfl
#eval tacticBenchmarkFromModule `temp useDuper
#eval tacticBenchmarkFromModule `temp useQuerySMT
#eval tacticBenchmarkFromModule `temp useAesop
-/
-- #eval tacticBenchmarkFromModule `temp useQuerySMT

------------------------------------------------------------------------------------------------------------------------
-- Hammer testing
open Lean Core Elab IO Meta Term Tactic -- All the monads!

def withImportsDir := "Examples/Mathlib/WithImports"
def jsonDir := "Examples/Mathlib/TrainingDataWithPremises"

/- Note: Some there still seem to be some discrepancies between `hammerBenchmarkFromModule`'s performance
   and the actual hammer's performance. One example is `Set.disjoint_right` which `hammer` handles fine
   when you actually run it but appears to have Duper's proof reconstruction fail for in
   `hammerBenchmarkFromModule` -/
-- #eval hammerBenchmarkFromModule `Mathlib.Data.Set.Basic withImportsDir jsonDir
-- #eval tacticBenchmarkFromModule `Mathlib.Data.Set.Basic useDuper

/- Note: `subset_insert_diff_singleton` is an example where the evaluation faithfully represents what the hammer
   does, but the hammer's behavior requires investigation. The external prover can solve this example, and Duper
   itself can solve this example, but Duper's reconstruction in the hammer can't solve the example -/

------------------------------------------------------------------------------------------------------------------------
-- QuerySMT testing

-- #eval querySMTBenchmarkFromModule `temp

------------------------------------------------------------------------------------------------------------------------
-- For testing in general
/-
def testRunTacticAtSpecificDecl (tac : TacticM Unit) (t : Expr) : MetaM Bool := do
  let g ← mkFreshExprMVar t
  let ((gs, heartbeats), seconds) ← withSeconds <| withHeartbeats <|
    try
      TermElabM.run' do
        return some $ ← Tactic.run g.mvarId! tac
    catch e =>
      dbg_trace "Error in trying to solve specific decl (type: {t}) {← e.toMessageData.format}"
      return none
  return gs.isSome

theorem test (p q : Prop) : True := by
  have ⟨h1, h2⟩ : ∃ x : p, q := sorry
  sorry

theorem test2 (p q : Prop) : True := by
  have h : ∃ x : p, q := sorry
  rcases h with ⟨h, h2⟩
  sorry

------------------------------------------------------------------------------------------------------------------------
-- For testing `useQuerySMT` (and specifically debugging the error caused by the anonymous constructors used to build selectors)
def myExpr1 : Expr :=
  Expr.forallE `α (Expr.sort 1)
    (Expr.forallE `x (Expr.bvar 0)
      (Expr.app (Expr.app (Expr.app (Expr.const `Eq [1]) (Expr.bvar 1)) (Expr.bvar 0)) (Expr.bvar 0))
      .default)
    .default

-- list_eq_self1 and list_eq_self2
def myExpr2 : Expr :=
  Expr.forallE `α (Expr.sort 1)
    (Expr.forallE `l
      (Expr.app (Expr.const ``List [0]) (Expr.bvar 0))
      (Expr.app
        (Expr.app
          (Expr.app
            (Expr.const ``Eq [1])
            (Expr.app (Expr.const ``List [0]) (Expr.bvar 1))
          )
          (Expr.bvar 0)
        )
        (Expr.bvar 0)
      )
      .default)
    .implicit

syntax (name := myTestTactic) "myTestTactic" : tactic

open Auto QuerySMT Duper

@[tactic myTestTactic]
def evalMyTestTactic : Tactic
| `(myTestTactic | myTestTactic) => withMainContext do
  let lctxBeforeIntros ← getLCtx
  let originalMainGoal ← getMainGoal
  let goalType ← originalMainGoal.getType
  let goalType ← instantiateMVars goalType
  -- If `goalType` has the form `∀ x1 : t1, … ∀ xn : tn, b`, first apply `intros` to put `x1 … xn` in the local context
  let numBinders := getIntrosSize goalType
  let mut introNCoreNames : Array Name := #[]
  let mut numGoalHyps := 0
  let goalHypPrefix := "h"
  /- Assuming `goal` has the form `∀ x1 : t1, ∀ x2 : t2, … ∀ xn : tn, b`, `goalPropHyps` is
     an array of size `n` where the mth element in `goalPropHyps` indicates whether the mth forall
     binder has a `Prop` type. This is used to help create `introNCoreNames` which should use existing
     binder names for nonProp arguments and newly created names (based on `goalHypPrefix`) for Prop arguments -/
  let goalPropHyps ← forallTelescope goalType fun xs _ => do xs.mapM (fun x => do pure (← inferType (← inferType x)).isProp)
  for b in goalPropHyps do
    if b then
      introNCoreNames := introNCoreNames.push (.str .anonymous (goalHypPrefix ++ numGoalHyps.repr))
      numGoalHyps := numGoalHyps + 1
    else -- If fvarId corresponds to a non-sort type, then introduce it using the userName
      introNCoreNames := introNCoreNames.push `_ -- `introNCore` will overwrite this with the existing binder name
  let (goalBinders, newGoal) ← introNCore originalMainGoal numBinders introNCoreNames.toList true true
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "querySMT :: Unexpected result after applying Classical.byContradiction"
  let negGoalLemmaName := "negGoal"
  let (_, absurd) ← MVarId.intro nngoal (.str .anonymous negGoalLemmaName)
  replaceMainGoal [absurd]
  withMainContext do
    let lctxAfterIntros ← getLCtx
    -- **TODO**: Figure out how to properly propagate `goalDecls` in getDuperCoreSMTLemmas
    let goalDecls := getGoalDecls lctxBeforeIntros lctxAfterIntros
    let goalsBeforeSkolemization ← getGoals
    evalTactic (← `(tactic| skolemizeAll))
    let goalsAfterSkolemization ← getGoals
    withMainContext do -- Use updated main context so that `collectAllLemmas` collects from the appropriate context
      let lctxAfterSkolemization ← getLCtx
      let (lemmas, inhFacts) ← collectAllLemmas (← `(hints| [*])) #[] #[]
      let SMTHints ← withAutoOptions $ runAutoGetHints lemmas inhFacts
      let (unsatCoreDerivLeafStrings, selectorInfos, allSMTLemmas) := SMTHints
      let (preprocessFacts, theoryLemmas, instantiations, computationLemmas, polynomialLemmas, rewriteFacts) := allSMTLemmas
      let smtLemmas := preprocessFacts ++ theoryLemmas ++ computationLemmas ++ polynomialLemmas ++ -- instantiations are intentionally ignored
        (rewriteFacts.foldl (fun acc rwFacts => acc ++ rwFacts) [])
      for (selName, selCtor, argIdx, selType) in selectorInfos do
        let selFactName := selName ++ "Fact"
        let selector ← buildSelector selCtor argIdx
        let selectorStx ← withOptions ppOptionsSetting $ PrettyPrinter.delab selector
        let selectorFact ← buildSelectorFact selName selCtor selType argIdx
        let selectorFactStx ← withOptions ppOptionsSetting $ PrettyPrinter.delab selectorFact
        let existsIntroStx ← withOptions ppOptionsSetting $ PrettyPrinter.delab (mkConst ``Exists.intro)
        -- **TODO** Bug is arising here specifically due to
        -- `⟨$(mkIdent (.str .anonymous selName)), $(mkIdent (.str .anonymous selFactName))⟩` part of have statement
        dbg_trace "selectorFact: {selectorFact}"
        dbg_trace "selectorFactStx: {selectorFactStx}"
        evalTactic $ -- Eval to add selector and its corresponding fact to lctx
          ← `(tactic|
              have ⟨$(mkIdent (.str .anonymous selName)), $(mkIdent (.str .anonymous selFactName))⟩ : $selectorFactStx:term := by
                apply $existsIntroStx:term $selectorStx:term
                intros
                rfl
            )
      pure ()
| _ => throwUnsupportedSyntax

def useMyTestTactic : TacticM Unit := do evalTactic (← `(tactic| myTestTactic))

#eval testRunTacticAtSpecificDecl useMyTestTactic myExpr2

theorem list_eq_self1 (l : List α) : l = l := by
  myTestTactic
  sorry
-/
