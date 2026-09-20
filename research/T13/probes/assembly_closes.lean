import NSFormalization.Section3.T13.Assembly
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Lane 359 closure probe

`research/` is not a Lean module root, so this probe re-derives the concrete
witnesses (an admissible ball and a genuine smooth bump field supported in it,
identical to lane 344/354's `constant_endpoints_closes.lean`) and then

* closes the whole reconciled `LocalizationAPI` record by `exact localizationAPI`;
* records the non-vacuity of the `localization` field at `s = 1/2` on the genuine
  lane-344 `ContDiffBump` field `probeField` (a nonzero smooth compactly supported
  vector field): the record's constant really bounds a nontrivial field.
-/

noncomputable section

namespace NSFormalization.Section3.T13

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.D01 (dotHomogeneousENorm)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators Topology

/-! ## The whole reconciled record closes from `localizationAPI`. -/

example : LocalizationAPI := localizationAPI

/-! ## The admissible ball and a genuine smooth compactly supported witness. -/

/-- Centre of the fundamental cube. -/
def probeCenter : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1 / 2 : ℝ))

/-- A genuine smooth bump supported in `closedBall probeCenter (1/4)`. -/
def probeBump : ContDiffBump probeCenter := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- A nonzero smooth vector field supported in `ball probeCenter (3/8)`. -/
def probeField : SpatialField := fun x => (probeBump x) • coordinateVector 0

theorem probe_ball_admissible :
    closure (Metric.ball probeCenter (3 / 8 : ℝ)) ⊆ interior fundamentalCube := by
  refine (Metric.closure_ball_subset_closedBall).trans ?_
  rw [interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - probeCenter‖ ≤ 3 / 8 := by
    rw [← dist_eq_norm]; exact hx
  have h1 : |x i - probeCenter i| ≤ 3 / 8 := by
    have h := abs_spaceCoord_le_norm (x - probeCenter) i
    have h2 : (x - probeCenter) i = x i - probeCenter i := rfl
    rw [h2] at h
    linarith
  have hc : probeCenter i = 1 / 2 := rfl
  rw [hc, abs_le] at h1
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

theorem probeField_contDiff : ContDiff ℝ ∞ probeField :=
  probeBump.contDiff.smul contDiff_const

theorem probeField_supported : SupportedInBall probeCenter (3 / 8 : ℝ) probeField := by
  have hsub : Function.support probeField ⊆ Function.support (⇑probeBump) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hg
    exact hx (by simp [probeField, hg])
  have h1 : tsupport probeField ⊆ tsupport (⇑probeBump) := closure_mono hsub
  rw [probeBump.tsupport_eq] at h1
  refine h1.trans ?_
  intro y hy
  rw [Metric.mem_closedBall] at hy
  rw [Metric.mem_ball]
  have hr : probeBump.rOut = 1 / 4 := rfl
  rw [hr] at hy
  linarith

/-! ## Non-vacuity: the `localization` field bounds a genuine nonzero field. -/

example :
    ∃ C : ℝ, 0 < C ∧
      periodicSobolevENorm (1 / 2 : ℝ) (periodize probeField)
        ≤ ENNReal.ofReal C *
            (eLpNorm probeField 2 volume + dotHomogeneousENorm (1 / 2 : ℝ) probeField) := by
  obtain ⟨C, hCpos, hC⟩ := localizationAPI.localization (1 / 2) (by norm_num) (by norm_num)
    probeCenter (3 / 8) (by norm_num) probe_ball_admissible
  exact ⟨C, hCpos, hC probeField ⟨probeField_contDiff, probeField_supported⟩⟩

end NSFormalization.Section3.T13
