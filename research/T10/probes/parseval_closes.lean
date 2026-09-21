import NSFormalization.Section3.T10.Parseval

noncomputable section
namespace NSFormalization.Section3.T10

open MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open scoped ENNReal

-- Exact statements copied from api_on_canonical.lean.
example :
    ∀ (z : SpatialField) (A : PeriodicSobolev 0), IsPeriodicDatum 0 z A →
      MemLp (torusLift z) 2 periodicTorusMeasure →
      ‖A‖ₑ = eLpNorm (torusLift z) 2 periodicTorusMeasure := parseval_forward

example :
    ∀ z : SpatialField, IsPeriodicSpatial z →
      MemLp (torusLift z) 2 periodicTorusMeasure →
        ∃ A : PeriodicSobolev 0, IsPeriodicDatum 0 z A := parseval_backward

-- Concrete non-vacuity: the zero field produces a datum and its norm is zero.
example : ∃ A : PeriodicSobolev 0, IsPeriodicDatum 0 (fun _ ↦ 0) A ∧ ‖A‖ₑ = 0 := by
  have hp : IsPeriodicSpatial (fun _ : Space ↦ (0 : Space)) := fun _ _ ↦ rfl
  have hz : MemLp (torusLift (fun _ : Space ↦ (0 : Space))) 2 periodicTorusMeasure :=
    MemLp.zero
  obtain ⟨A, hA⟩ := parseval_backward _ hp hz
  refine ⟨A, hA, ?_⟩
  have hn := parseval_forward _ A hA hz
  change ‖A‖ₑ = eLpNorm (fun _ : PeriodicTorus ↦ (0 : Space)) 2 periodicTorusMeasure at hn
  simpa using hn

-- Nonzero constant fields also satisfy both directions.
example (c : Space) : ∃ A : PeriodicSobolev 0,
    IsPeriodicDatum 0 (fun _ ↦ c) A ∧ ‖A‖ₑ = ‖c‖ₑ := by
  let := periodicTorusMeasure_probability
  have hp : IsPeriodicSpatial (fun _ : Space ↦ c) := fun _ _ ↦ rfl
  have hz : MemLp (torusLift (fun _ : Space ↦ c)) 2 periodicTorusMeasure := memLp_const c
  obtain ⟨A, hA⟩ := parseval_backward _ hp hz
  refine ⟨A, hA, ?_⟩
  have hn := parseval_forward _ A hA hz
  change ‖A‖ₑ = eLpNorm (fun _ : PeriodicTorus ↦ c) 2 periodicTorusMeasure at hn
  rw [eLpNorm_const' c (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)] at hn
  simpa using hn

end NSFormalization.Section3.T10
