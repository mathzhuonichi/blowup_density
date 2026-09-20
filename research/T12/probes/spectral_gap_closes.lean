import NSFormalization.Section3.T12.SpectralGap

/-!
# Exact API-field closure probes for the periodic spectral gap
-/

noncomputable section

namespace NSFormalization.Section3.T12

open MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section4.A02 (SpatialField)
open scoped ENNReal

local instance spectralGapProbeUnitAddCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance spectralGapProbeUnitAddCircleProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The `spectralGap` API field, with `Cgap := gapConst`, verbatim. -/
example :
    ∀ s : ℝ, 0 ≤ s → ∀ v : SpatialField,
      MemPeriodicHomogeneous s v →
        periodicSobolevENorm s v ≤
          ENNReal.ofReal (gapConst s) * periodicHomogeneousENorm s v :=
  spectralGap

/-- The constant-one converse API field, verbatim. -/
example :
    ∀ s : ℝ, 0 ≤ s → ∀ v : SpatialField,
      MemPeriodicHomogeneous s v →
        periodicHomogeneousENorm s v ≤ periodicSobolevENorm s v :=
  homogeneous_le_sobolev

/-- The required positivity field for `Cgap := gapConst`. -/
example : ∀ s : ℝ, 0 ≤ s → 0 < gapConst s := gapConst_pos

/-- The zero field satisfies the full API guard at every order. -/
example (s : ℝ) :
    MemPeriodicHomogeneous s (0 : SpatialField) := by
  have hdatum :
      IsPeriodicHomogeneousDatum s (0 : SpatialField) (0 : PeriodicSobolev s) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x i
      rfl
    · change Integrable (fun _ : PeriodicTorus ↦ (0 : Space)) periodicTorusMeasure
      exact integrable_const 0
    · change (∫ _ : PeriodicTorus, (0 : Space) ∂periodicTorusMeasure) = 0
      exact integral_zero PeriodicTorus Space
    · intro i k
      change (0 : ℂ) = (homogeneousDatumWeight s k : ℂ) •
        periodicFourierCoeff (fun _ : Space ↦ (0 : ℂ)) k
      rw [periodicFourierCoeff_const]
      simp
  refine ⟨hdatum.1, MemLp.zero, hdatum.2.2.1, ?_⟩
  have hle : periodicHomogeneousENorm s (0 : SpatialField) ≤
      ‖(0 : PeriodicSobolev s).1‖ₑ :=
    iInf_le_of_le ⟨(0 : PeriodicSobolev s), hdatum⟩ le_rfl
  have hzero : periodicHomogeneousENorm s (0 : SpatialField) = 0 :=
    bot_unique (by simpa using hle)
  rw [hzero]
  exact ENNReal.zero_ne_top

end NSFormalization.Section3.T12
