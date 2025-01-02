import Scripts.Tactic_benchmark

open Lean Core Elab IO Meta Term Tactic -- All the monads!

/-
#eval Command.liftTermElabM $ tacticBenchmarkFromModule `temp useRfl
#eval Command.liftTermElabM $ tacticBenchmarkFromModule `temp useDuper
#eval Command.liftTermElabM $ tacticBenchmarkFromModule `temp useQuerySMT
#eval Command.liftTermElabM $ tacticBenchmarkFromModule `temp useAesop
-/
-- #eval Command.liftTermElabM $ querySMTBenchmarkFromModule `temp2
-- #eval Command.liftTermElabM $ querySMTBenchmarkFromModule `temp

------------------------------------------------------------------------------------------------------------------------
-- Hammer testing

def withImportsDir := "Examples/Mathlib/WithImports"
def jsonDir := "Examples/Mathlib/TrainingDataWithPremises"

/- Note: Some there still seem to be some discrepancies between `hammerBenchmarkFromModule`'s performance
   and the actual hammer's performance. One example is `Set.disjoint_right` which `hammer` handles fine
   when you actually run it but appears to have Duper's proof reconstruction fail for in
   `hammerBenchmarkFromModule` -/
-- #eval Command.liftTermElabM $ hammerBenchmarkFromModule `Mathlib.Data.Set.Basic withImportsDir jsonDir 10
-- #eval Command.liftTermElabM $ tacticBenchmarkFromModule `Mathlib.Data.Set.Basic useDuper

-- #eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Data.Int.Defs `Int.natCast_dvd withImportsDir jsonDir 10

-- #eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Data.Set.Basic `Set.subset_insert_diff_singleton withImportsDir jsonDir 10

/- Note: `subset_insert_diff_singleton` is an example where the evaluation faithfully represents what the hammer
   does, but the hammer's behavior requires investigation. The external prover can solve this example, and Duper
   itself can solve this example, but Duper's reconstruction in the hammer can't solve the example -/

-- #eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Analysis.Analytic.Composition `Composition.length_gather withImportsDir jsonDir

------------------------------------------------------------------------------------------------------------------------
-- Simp_all testing

--**NOTE** Set.not_subset has the wrong recommendation for simp_all (because we are currently using hammerRecommendation
-- which blacklists some theorems that simp_all would otherwise benefit from)
-- #eval Command.liftTermElabM $ simpAllBenchmarkAtDecl `Mathlib.Data.Set.Basic `Set.not_subset withImportsDir jsonDir

-- #eval Command.liftTermElabM $ simpAllBenchmarkAtDecl `Mathlib.Data.Set.Basic `Set.ite_inter_self withImportsDir jsonDir

-- #eval Command.liftTermElabM $ tacticBenchmarkAtDecl `Mathlib.Data.Set.Basic `Set.inclusion_mk useSimpAll

------------------------------------------------------------------------------------------------------------------------
-- QuerySMT testing

-- #eval querySMTBenchmarkFromModule `temp

------------------------------------------------------------------------------------------------------------------------
-- Comparing against lean-auto evaluation

/- **NOTE**
When I test `auto`, I set the following options first:
set_option auto.native true
set_option auto.smt false
set_option auto.tptp false
-/

/- Succeeds in lean-auto's evaluation, both of the following tests succeed
#eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Order.Heyting.Basic `hnot_le_iff_codisjoint_left withImportsDir jsonDir 10
#eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Order.Heyting.Basic `hnot_le_iff_codisjoint_left withImportsDir jsonDir 10 false
-/

/- Succeeds in lean-auto's evaluation, both of the following tests succeed
#eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv `deriv_sinh withImportsDir jsonDir 10
#eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv `deriv_sinh withImportsDir jsonDir 10 false
-/

/- `Asymptotics.IsBigO.comp_tendsto` succeeds in lean-auto's evaluation, but I am not able to test on myself because the data extraction script encounters
an error processing Mathlib.Analysis.Asymptotics.Asymptotics.lean

**TODO** Fix the error that comes with processing Mathlib.Analysis.Asymptotics.Asymptotics.lean

#eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Analysis.Asymptotics.Asymptotics `Asymptotics.IsBigO.comp_tendsto withImportsDir jsonDir 10
#eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Analysis.Asymptotics.Asymptotics `Asymptotics.IsBigO.comp_tendsto withImportsDir jsonDir 10 false
-/

/- Succeeds in lean-auto's evaluation, both of the following tests succeed
#eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Topology.Algebra.InfiniteSum.Group `HasProd.div withImportsDir jsonDir 10
#eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Topology.Algebra.InfiniteSum.Group `HasProd.div withImportsDir jsonDir 10 false
-/

/- Succeeds in lean-auto's evaluation, both of the following tests succeed
#eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Algebra.BigOperators.RingEquiv `RingEquiv.map_prod withImportsDir jsonDir 10
#eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Algebra.BigOperators.RingEquiv `RingEquiv.map_prod withImportsDir jsonDir 10 false
-/

/- Succeeds in lean-auto's evaluation, both of the following tests succeed
#eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Topology.MetricSpace.IsometricSMul `dist_smul withImportsDir jsonDir 10
#eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Topology.MetricSpace.IsometricSMul `dist_smul withImportsDir jsonDir 10 false
-/

/- This test succceeds in lean-auto's evaluation (and running `auto` by hand succeeds)

This test can be handled by `hammer`'s `simp_all` preprocessing, so it succeeds when `simp_all` preprocessing is enabled.
When `hammer`'s `simp_all` preprocessing is disabled, returns the following:
  About to use hammer for Mathlib.Vector.mem_cons_of_mem in module Mathlib.Data.Vector.Mem
    (recommendation: #[(Mathlib.Vector.mem_cons_iff, notInSimpAll)])
    ✅️✅️✅️💥️❌️❌️ Mathlib.Vector.mem_cons_of_mem (2.697926s) (13650348 heartbeats)

This corresponds to successfully translating to TPTP but having the external prover fail. This outcome does not technically contradict
lean-auto's result, but it merits investigation as I don't see why the external prover should fail when Duper can succeed (and Duper does
succeed when we test by hand, even with portfolioInstance set to 1) **TODO** Investigate what's going on here

#eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Data.Vector.Mem `Mathlib.Vector.mem_cons_of_mem withImportsDir jsonDir 10
#eval Command.liftTermElabM $ hammerBenchmarkAtDecl `Mathlib.Data.Vector.Mem `Mathlib.Vector.mem_cons_of_mem withImportsDir jsonDir 10 false
-/
