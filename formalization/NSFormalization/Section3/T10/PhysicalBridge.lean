import NSFormalization.Section3.T10.PeriodicData
import NSFormalization.Paper1.FourierReconstructionAdapter

/-!
# Physical-field bridge for the periodic data layer

This module identifies unit-periodic fields on Euclidean three-space with
fields on `UnitAddTorus (Fin 3)`, and proves the elementary normalized-mean
decomposition used by the T10 data API.
-/

noncomputable section

namespace NSFormalization.Section3.T10

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (Coords toSpace UnitPeriods)
open NSFormalization.Section4.A02 (SpatialField)
open scoped BigOperators

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Integer translates and the quotient realization -/

/-- Unit coordinate periods imply invariance under every integer lattice
translate.  This is the physical-coordinate form used by later T10 lanes. -/
theorem periodic_shift_int {E : Type*} [Add E] {z : Space → E}
    (hz : IsPeriodicSpatial z) (x : Space) (k : Fin 3 → ℤ) :
    z (x + ∑ i, (k i : ℝ) • coordinateVector i) = z x := by
  have h := NSFormalization.Paper1.unitPeriods_integer_translate
    (f := z) (show UnitPeriods z from hz) k x
  have hvec : (∑ i, (k i : ℝ) • coordinateVector i) =
      toSpace (fun i ↦ (k i : ℝ)) := by
    ext j
    simp [coordinateVector, Pi.single_apply]
  rw [hvec]
  exact h

/-- The canonical lift evaluates to the original field over the quotient
image of every physical point. -/
theorem torusLift_apply_of_periodic {E : Type*} [Add E] {z : Space → E}
    (hz : IsPeriodicSpatial z) (x : Space) :
    torusLift z (fun i ↦ (x i : UnitAddCircle)) = z x := by
  exact NSFormalization.Paper1.torusLift_coe_of_unitPeriods
    (show UnitPeriods z from hz) x

/-- Pulling a torus field back along the quotient map gives a unit-periodic
physical field. -/
theorem isPeriodicSpatial_torusLift_comp {E : Type*} [Add E]
    (Z : PeriodicTorus → E) :
    IsPeriodicSpatial (fun x : Space ↦ Z (fun i ↦ (x i : UnitAddCircle))) := by
  intro x i
  apply congrArg Z
  funext j
  by_cases hji : j = i
  · subst j
    simp [coordinateVector]
  · simp [coordinateVector, hji]

/-- Lifting to the quotient torus is injective on unit-periodic physical
vector fields. -/
theorem torusLift_injective :
    ∀ z w : SpatialField, IsPeriodicSpatial z → IsPeriodicSpatial w →
      torusLift z = torusLift w → z = w := by
  intro z w hz hw hzw
  funext x
  rw [← torusLift_apply_of_periodic hz x,
    ← torusLift_apply_of_periodic hw x, hzw]

/-- Every torus vector field has a unit-periodic physical representative. -/
theorem torusLift_surjective :
    ∀ Z : PeriodicTorus → Space,
      ∃ z : SpatialField, IsPeriodicSpatial z ∧ torusLift z = Z := by
  intro Z
  let z : SpatialField := fun x ↦ Z (fun i ↦ (x i : UnitAddCircle))
  refine ⟨z, isPeriodicSpatial_torusLift_comp Z, ?_⟩
  funext q
  change Z (fun i ↦
    (((UnitAddTorus.measurableEquivPiIoc (0 : Coords) q).val i : ℝ) :
      UnitAddCircle)) = Z q
  exact congrArg Z
    ((UnitAddTorus.measurableEquivPiIoc (0 : Coords)).symm_apply_apply q)

/-! ## Normalized means -/

/-- A constant physical field has that same normalized torus mean. -/
theorem meanT_const (c : Space) : meanT (fun _ : Space ↦ c) = c := by
  simp [meanT, torusLift, NSFormalization.Paper1.torusLift]

/-- Every integrable periodic field is the sum of its constant mean and its
mean-zero part. -/
theorem mean_decomposition :
    ∀ z : SpatialField, IsPeriodicSpatial z →
      Integrable (torusLift z) periodicTorusMeasure →
        (∀ x : Space, constantPartT z x + meanZeroPartT z x = z x) ∧
          IsMeanZeroT (meanZeroPartT z) := by
  intro z _hz hz_int
  constructor
  · intro x
    simp [constantPartT, meanZeroPartT]
  · change meanT (meanZeroPartT z) = 0
    change (∫ y : PeriodicTorus, torusLift z y - meanT z
      ∂periodicTorusMeasure) = 0
    rw [integral_sub hz_int (integrable_const (meanT z))]
    change meanT z - meanT (fun _ : Space ↦ meanT z) = 0
    rw [meanT_const]
    exact sub_self _

end NSFormalization.Section3.T10
