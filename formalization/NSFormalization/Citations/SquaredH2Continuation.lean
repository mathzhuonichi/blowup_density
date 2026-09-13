import Mathlib
/-! Exact squared-H² continuation contracts. Status: OPEN/sorry. -/
namespace NSFormalization.Citations
structure PeriodicClassicalSolution where
  h2 : ℝ → ℝ
  extendable : ℝ → Prop
structure WholeSpaceClassicalSolution where
  h2 : ℝ → ℝ
  extendable : ℝ → Prop
axiom squared_H2_continuation_periodic (U : PeriodicClassicalSolution) (S : ℝ) (hS : 0 < S)
    (hfin : (∫ t in Set.Ioc 0 S, U.h2 t) < ∞) : ∃ T : ℝ, S < T ∧ U.extendable T
axiom squared_H2_continuation_whole_space (U : WholeSpaceClassicalSolution) (S : ℝ) (hS : 0 < S)
    (hfin : (∫ t in Set.Ioc 0 S, U.h2 t) < ∞) : ∃ T : ℝ, S < T ∧ U.extendable T
end NSFormalization.Citations
