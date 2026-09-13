import Mathlib
/-! Forced whole-space local theory contract. Status: OPEN/sorry, not a citation theorem.
Pressure is represented only through its gradient; no L² pressure assertion is made. -/
namespace NSFormalization.Citations
structure HInfinitySigmaData where
  field : Type
  smooth_all_orders : Prop
  square_integrable : Prop
  divergence_free : Prop
structure WholeSpaceAdmissibleForce where
  field : Type
  all_integer_sobolev_time_integrability : Prop
structure WholeSpaceClassicalSolution (ν : ℝ) (a : HInfinitySigmaData)
    (f : WholeSpaceAdmissibleForce) (T : ℝ≥0∞) where
  velocity : ℝ → Type
  pressure_gradient : ℝ → Type
  pressure_modulo_time_function : Prop
  equation : Prop
  initial_data : Prop
  maximal : Prop
  unique : Prop
  smooth_before_endpoint : Prop
  h2_squared_integral : ℝ → ℝ
  extendable : ℝ → Prop
axiom whole_space_forced_local_and_continuation
  (ν : ℝ) (hν : 0 < ν) (a : HInfinitySigmaData)
  (f : WholeSpaceAdmissibleForce) :
  ∃ Tstar : ℝ≥0∞, ∃ U : WholeSpaceClassicalSolution ν a f Tstar,
    U.maximal ∧ U.unique ∧
    (∀ S : ℝ, 0 < S → ENNReal.ofReal S < Tstar → U.smooth_before_endpoint) ∧
    (∀ S : ℝ, 0 < S → ENNReal.ofReal S < Tstar →
      (∫ t in Set.Ioc 0 S, U.h2_squared_integral t) < ∞ →
      ∃ T : ℝ, S < T ∧ U.extendable T)
end NSFormalization.Citations
