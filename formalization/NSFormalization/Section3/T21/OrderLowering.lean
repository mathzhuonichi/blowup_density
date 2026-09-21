import NSFormalization.Section3.T21.Definitions
import NSFormalization.Section3.T18.SobolevRate

/-!
# T21 N1--N2: order lowering for periodic Sobolev data

The coefficient multiplier and its contraction estimate are supplied by T11
and T18.  This module only identifies an arbitrary reweighted datum with that
multiplier, transports the physical datum predicate, and descends through the
two datum infima.
-/

noncomputable section

namespace NSFormalization.Section3.T21

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ENNReal

private theorem periodicDatum_ext {s : ℝ} {A B : PeriodicSobolev s}
    (h : ∀ i k, A.1 i k = B.1 i k) : A = B := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  exact lp.ext (funext (h i))

/-- N1: every order-lowering reweight is contractive. -/
theorem reweightContraction (s t : ℝ) (hst : s ≤ t)
    (A : PeriodicSobolev t) (B : PeriodicSobolev s)
    (hAB : IsPeriodicReweight t s A B) :
    ‖B‖ ≤ ‖A‖ := by
  have hB : B = persistenceDown t s hst A :=
    periodicDatum_ext fun i k ↦ by
      rw [hAB i k, persistenceDown_reweight t s hst A i k]
  rw [hB]
  exact NSFormalization.Section3.T18.persistenceDown_norm_le t s hst A

/-- N1 datum transport: a representing datum at a higher order has a
contractive representative of the same physical field at every lower order. -/
theorem exists_orderLoweringDatum (s t : ℝ) (hst : s ≤ t)
    (z : SpatialField) (A : PeriodicSobolev t) (hA : IsPeriodicDatum t z A) :
    ∃ B : PeriodicSobolev s,
      IsPeriodicReweight t s A B ∧ IsPeriodicDatum s z B ∧ ‖B‖ ≤ ‖A‖ := by
  let B := persistenceDown t s hst A
  have hAB : IsPeriodicReweight t s A B :=
    persistenceDown_reweight t s hst A
  exact ⟨B, hAB, persistence_datum_of_reweight hA hAB,
    reweightContraction s t hst A B hAB⟩

/-- N2: the physical periodic Sobolev extended norm is monotone in its order. -/
theorem sliceSobolevMonotone : ∀ s : ℝ, 1 / 2 ≤ s → ∀ z : SpatialField,
    periodicSobolevENorm (1 / 2) z ≤ periodicSobolevENorm s z := by
  intro s hs z
  apply le_iInf
  intro A
  obtain ⟨B, _hAB, hB, hnorm⟩ :=
    exists_orderLoweringDatum (1 / 2) s hs z A.1 A.2
  calc
    periodicSobolevENorm (1 / 2) z ≤ ‖B‖ₑ :=
      iInf_le_of_le ⟨B, hB⟩ le_rfl
    _ ≤ ‖A.1‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hnorm

end NSFormalization.Section3.T21
