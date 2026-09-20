import NSFormalization.Section3.T10.PhysicalBridge

noncomputable section

namespace NSFormalization.Section3.T10

open MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open scoped BigOperators

/-! The three public theorems close their verbatim `TorusDataAPI` fields. -/

example :
    ∀ z w : SpatialField, IsPeriodicSpatial z → IsPeriodicSpatial w →
      torusLift z = torusLift w → z = w :=
  torusLift_injective

example :
    ∀ Z : PeriodicTorus → Space,
      ∃ z : SpatialField, IsPeriodicSpatial z ∧ torusLift z = Z :=
  torusLift_surjective

example :
    ∀ z : SpatialField, IsPeriodicSpatial z →
      Integrable (torusLift z) periodicTorusMeasure →
        (∀ x : Space, constantPartT z x + meanZeroPartT z x = z x) ∧
          IsMeanZeroT (meanZeroPartT z) :=
  mean_decomposition

/-! The reusable bridge lemmas retain their intended public signatures. -/

example {E : Type*} [Add E] {z : Space → E}
    (hz : IsPeriodicSpatial z) (x : Space) (k : Fin 3 → ℤ) :
    z (x + ∑ i, (k i : ℝ) • coordinateVector i) = z x :=
  periodic_shift_int hz x k

example {E : Type*} [Add E] {z : Space → E}
    (hz : IsPeriodicSpatial z) (x : Space) :
    torusLift z (fun i ↦ (x i : UnitAddCircle)) = z x :=
  torusLift_apply_of_periodic hz x

example {E : Type*} [Add E] (Z : PeriodicTorus → E) :
    IsPeriodicSpatial (fun x : Space ↦ Z (fun i ↦ (x i : UnitAddCircle))) :=
  isPeriodicSpatial_torusLift_comp Z

example (c : Space) : meanT (fun _ : Space ↦ c) = c :=
  meanT_const c

/-! A concrete zero field witnesses that the mean decomposition is non-vacuous. -/

example :
    (∀ x : Space,
      constantPartT (fun _ : Space ↦ (0 : Space)) x +
        meanZeroPartT (fun _ : Space ↦ (0 : Space)) x = 0) ∧
      IsMeanZeroT (meanZeroPartT (fun _ : Space ↦ (0 : Space))) := by
  apply mean_decomposition (fun _ : Space ↦ (0 : Space))
  · intro x i
    rfl
  · exact integrable_zero _ _ _

end NSFormalization.Section3.T10
