import Contracts.V1.Localization
import Bindings.Localization
import TestSupport.Axioms
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Tests for `T02.localization`

This module checks the transported declaration, independently restates every
field of the reconciled Spec, and instantiates the uniform localization field
at `s = 1/2` on a genuine nonzero smooth bump field.
-/

noncomputable section

namespace BlowupDensity.Tests

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm
open BlowupDensity.Contracts.V1.TorusData
open scoped ContDiff ENNReal BigOperators Topology

/-- The implementation supplies all six fields of the localization contract. -/
theorem checkedLocalization : Contracts.V1.LocalizationAPI :=
  Bindings.localizationAPI

run_cmd TestSupport.checkAxioms ``checkedLocalization

/-! ## Independent conformance with the six fields of `research/T13/Spec.lean` -/

example :
    ∀ (s : ℝ), 0 < s → s < 1 → 0 < cFrac s ∧ cFrac s < ⊤ :=
  checkedLocalization.constant_pos_finite

example :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
      ContDiff ℝ ∞ f → HasCompactSupport f →
        IReal s f < ⊤ ∧
          IReal s f = cFrac s * dotHomogeneousENorm s f ^ (2 : ℕ) :=
  checkedLocalization.wholeSpace_identity

example :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
      ContDiff ℝ ∞ f → IsPeriodicSpatial f →
        ITorus s f < ⊤ ∧
          ITorus s f = cFrac s *
            periodicHomogeneousENorm s (meanZeroPartT f) ^ (2 : ℕ) :=
  checkedLocalization.torus_identity

example :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∃ C : ℝ, 0 < C ∧ ∀ f : SpatialField,
          (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
            periodicSobolevENorm s (periodize f) ≤
              ENNReal.ofReal C * (eLpNorm f 2 volume + dotHomogeneousENorm s f) :=
  checkedLocalization.localization

example :
    ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
          eLpNorm (periodize f) 2 (volume.restrict fundamentalCube) =
            eLpNorm f 2 volume :=
  checkedLocalization.endpoint_zero

example :
    ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
          gradientENorm (periodize f) (volume.restrict fundamentalCube) =
            gradientENorm f volume :=
  checkedLocalization.endpoint_one

/-! ## Non-vacuity on an explicit nonzero bump field -/

/-- Centre of the registered fundamental cube. -/
def localizationProbeCenter : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1 / 2 : ℝ))

/-- A genuine smooth bump supported in
`closedBall localizationProbeCenter (1/4)`. -/
def localizationProbeBump : ContDiffBump localizationProbeCenter :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- A nonzero smooth vector field supported in
`ball localizationProbeCenter (3/8)`. -/
def localizationProbeField : SpatialField :=
  fun x => (localizationProbeBump x) • coordinateVector 0

theorem localizationProbe_ball_admissible :
    closure (Metric.ball localizationProbeCenter (3 / 8 : ℝ)) ⊆
      interior fundamentalCube := by
  rw [Bindings.fundamentalCube_eq,
    NSFormalization.Section3.T13.interior_fundamentalCube]
  refine (Metric.closure_ball_subset_closedBall).trans ?_
  intro x hx i
  have hd : ‖x - localizationProbeCenter‖ ≤ 3 / 8 := by
    rw [← dist_eq_norm]
    exact hx
  have h1 : |x i - localizationProbeCenter i| ≤ 3 / 8 := by
    have h := NSFormalization.Section3.T13.abs_spaceCoord_le_norm
      (x - localizationProbeCenter) i
    have h2 : (x - localizationProbeCenter) i =
        x i - localizationProbeCenter i := rfl
    rw [h2] at h
    linarith
  have hc : localizationProbeCenter i = 1 / 2 := rfl
  rw [hc, abs_le] at h1
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

theorem localizationProbeField_contDiff :
    ContDiff ℝ ∞ localizationProbeField :=
  localizationProbeBump.contDiff.smul contDiff_const

theorem localizationProbeField_supported :
    SupportedInBall localizationProbeCenter (3 / 8 : ℝ)
      localizationProbeField := by
  have hsub : Function.support localizationProbeField ⊆
      Function.support (⇑localizationProbeBump) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hg
    exact hx (by simp [localizationProbeField, hg])
  have h1 : tsupport localizationProbeField ⊆
      tsupport (⇑localizationProbeBump) := closure_mono hsub
  rw [localizationProbeBump.tsupport_eq] at h1
  refine h1.trans ?_
  intro y hy
  rw [Metric.mem_closedBall] at hy
  rw [Metric.mem_ball]
  have hr : localizationProbeBump.rOut = 1 / 4 := rfl
  rw [hr] at hy
  linarith

/-- The field used below is genuinely nonzero. -/
theorem localizationProbeField_ne_zero :
    localizationProbeField localizationProbeCenter ≠ 0 := by
  have h1 : localizationProbeBump localizationProbeCenter = 1 :=
    localizationProbeBump.one_of_mem_closedBall
      (Metric.mem_closedBall_self localizationProbeBump.rIn_pos.le)
  have h2 : localizationProbeField localizationProbeCenter = coordinateVector 0 := by
    simp [localizationProbeField, h1]
  rw [h2]
  intro hcon
  have hz : (coordinateVector (0 : Fin 3)) 0 = 0 := by
    rw [hcon]
    rfl
  rw [coordinateVector] at hz
  simp at hz

/-- The registered localization field at `s=1/2` bounds the explicit nonzero
field with one positive constant selected before the field. -/
example :
    ∃ C : ℝ, 0 < C ∧
      periodicSobolevENorm (1 / 2 : ℝ)
          (periodize localizationProbeField) ≤
        ENNReal.ofReal C *
          (eLpNorm localizationProbeField 2 volume +
            dotHomogeneousENorm (1 / 2 : ℝ) localizationProbeField) := by
  obtain ⟨C, hCpos, hC⟩ := Bindings.localizationAPI.localization
    (1 / 2) (by norm_num) (by norm_num)
    localizationProbeCenter (3 / 8) (by norm_num)
    localizationProbe_ball_admissible
  exact ⟨C, hCpos,
    hC localizationProbeField
      ⟨localizationProbeField_contDiff, localizationProbeField_supported⟩⟩

end BlowupDensity.Tests
