import NSFormalization.Paper1.PeriodicLocalLifespan
import NSFormalization.Paper1.PeriodicPressureFlowBridge

/-! Conditional common-interval uniqueness wrappers for actual periodic flows. -/
noncomputable section
namespace NSFormalization.Paper1.PeriodicCommonIntervalBridge

open Set
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicLocalLifespan
open NSFormalization.Paper1.PeriodicUniqueness

/-- The common-interval conclusion for two normalized `Flow` witnesses.
The existence and normalization hypotheses are explicit inputs. -/
theorem normalized_flow_common_interval
    {ν S T : ℝ} (hν : 0 < ν) {a : Space → Space} {f : VelocityField}
    (U : Flow ν a f S) (V : Flow ν a f T)
    (hU : IsNormalized U) (hV : IsNormalized V) :
    ∀ t ∈ Ico (0 : ℝ) (min S T), ∀ x : Space,
      U.velocity (t, x) = V.velocity (t, x) ∧
      U.pressure (t, x) = V.pressure (t, x) :=
  normalized_flows_agree hν U V hU hV

/-- Equality on every common compact subinterval, as a direct corollary of
the half-open common-interval theorem. -/
theorem normalized_flow_common_Icc
    {ν S T : ℝ} (hν : 0 < ν) {a : Space → Space} {f : VelocityField}
    (U : Flow ν a f S) (V : Flow ν a f T)
    (hU : IsNormalized U) (hV : IsNormalized V)
    {R : ℝ} (hR : 0 ≤ R) (hRS : R < min S T) :
    ∀ t ∈ Icc (0 : ℝ) R, ∀ x : Space,
      U.velocity (t, x) = V.velocity (t, x) ∧
      U.pressure (t, x) = V.pressure (t, x) := by
  intro t ht x
  apply normalized_flow_common_interval hν U V hU hV t
    ⟨ht.1, lt_of_le_of_lt ht.2 hRS⟩ x

end NSFormalization.Paper1.PeriodicCommonIntervalBridge
