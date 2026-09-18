import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import NSFormalization.Section3.T13.ConstantEndpoints
import NSFormalization.Section4.D01.SmoothDatum

/-!
# T12 U2: a smooth cutoff for the fundamental cube

We use a fixed Euclidean ball as the slightly larger neighborhood: `largerCube`
is `ball 0 4`.  The cutoff is the standard `ContDiffBump` centered at zero
with plateau radius `5/2` and support radius `3`.  The cube `[0,1]^3` lies in
the plateau (the coarse bound `‖x‖ ≤ 2` is enough), while the closed support
ball of radius `3` lies in `largerCube`.  A ball is used instead of a
coordinate cube only to keep the construction canonical and elementary; it is
the required fixed enlargement of the fundamental cube.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open Set MeasureTheory Metric
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField MemHInfty)
open NSFormalization.Section4.D01 (memHInfty_of_contDiff_memLp)
open scoped ContDiff ENNReal BigOperators Topology

/-- The fixed open enlargement used for the cutoff support. -/
def largerCube : Set Space := ball (0 : Space) 4

/-- A standard smooth bump: one on the radius-`5/2` ball, supported in radius `3`. -/
def cutoffBump : ContDiffBump (0 : Space) :=
  ⟨5 / 2, 3, by norm_num, by norm_num⟩

/-- The cutoff function `χ`. -/
def cutoff : Space → ℝ := cutoffBump

lemma norm_le_two_of_mem_fundamentalCube {x : Space} (hx : x ∈ fundamentalCube) :
    ‖x‖ ≤ 2 := by
  have hs : ‖x‖ ^ 2 = ∑ i : Fin 3, ‖x i‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ x
  have hsum : (∑ i : Fin 3, ‖x i‖ ^ 2) ≤ 3 := by
    calc
      (∑ i : Fin 3, ‖x i‖ ^ 2) ≤ ∑ i : Fin 3, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Real.norm_eq_abs, abs_of_nonneg (hx i).1]
        have hp : 0 ≤ x i * (1 - x i) :=
          mul_nonneg (hx i).1 (by linarith [(hx i).2])
        nlinarith [hp]
      _ = 3 := by norm_num
  nlinarith [norm_nonneg x]

theorem cutoff_contDiff : ContDiff ℝ ∞ cutoff := by
  exact cutoffBump.contDiff

theorem cutoff_eq_one_on_ball : EqOn cutoff (fun _ : Space => (1 : ℝ))
    (ball (0 : Space) (5 / 2)) := by
  intro x hx
  apply cutoffBump.one_of_mem_closedBall
  change x ∈ closedBall (0 : Space) cutoffBump.rIn
  apply ball_subset_closedBall
  change x ∈ ball (0 : Space) (5 / 2) at hx
  simpa [cutoffBump] using hx

theorem cutoff_eq_one : ∀ x ∈ fundamentalCube, cutoff x = 1 := by
  intro x hx
  apply cutoff_eq_one_on_ball
  rw [mem_ball, dist_zero_right]
  exact (norm_le_two_of_mem_fundamentalCube hx).trans_lt (by norm_num)

theorem cutoff_range : ∀ x, cutoff x ∈ Icc (0 : ℝ) 1 := by
  intro x
  exact ⟨cutoffBump.nonneg' x, cutoffBump.le_one⟩

theorem tsupport_cutoff : tsupport cutoff ⊆ interior largerCube := by
  change tsupport (cutoffBump : Space → ℝ) ⊆ interior largerCube
  rw [show interior largerCube = largerCube by
    exact Metric.isOpen_ball.interior_eq]
  rw [cutoffBump.tsupport_eq]
  intro x hx
  rw [mem_closedBall, dist_zero_right] at hx
  change x ∈ ball (0 : Space) 4
  rw [mem_ball, dist_zero_right]
  have hx' : ‖x‖ ≤ 3 := by simpa [cutoffBump] using hx
  linarith [hx']

theorem hasCompactSupport_cutoff : HasCompactSupport cutoff := by
  exact cutoffBump.hasCompactSupport

theorem tsupport_fderiv_cutoff :
    tsupport (fderiv ℝ cutoff) ⊆ interior largerCube := by
  exact (tsupport_fderiv_subset ℝ).trans tsupport_cutoff

theorem tsupport_iteratedFDeriv_two_cutoff :
    tsupport (iteratedFDeriv ℝ 2 cutoff) ⊆ interior largerCube := by
  exact (tsupport_iteratedFDeriv_subset 2).trans tsupport_cutoff

theorem exists_cutoff_fderiv_bound :
    ∃ M₁ : ℝ, ∀ x, ‖fderiv ℝ cutoff x‖ ≤ M₁ := by
  have hc : Continuous (fderiv ℝ cutoff) :=
    cutoff_contDiff.continuous_fderiv (by simp)
  have hs : HasCompactSupport (fderiv ℝ cutoff) :=
    HasCompactSupport.fderiv ℝ hasCompactSupport_cutoff
  exact hc.bounded_above_of_compact_support hs

theorem exists_cutoff_iteratedFDeriv_two_bound :
    ∃ M₂ : ℝ, ∀ x, ‖iteratedFDeriv ℝ 2 cutoff x‖ ≤ M₂ := by
  have hc : Continuous (iteratedFDeriv ℝ 2 cutoff) :=
    cutoff_contDiff.continuous_iteratedFDeriv (by norm_num)
  have hs : HasCompactSupport (iteratedFDeriv ℝ 2 cutoff) :=
    hasCompactSupport_cutoff.iteratedFDeriv 2
  exact hc.bounded_above_of_compact_support hs

theorem fderiv_cutoff_eq_zero : EqOn (fderiv ℝ cutoff) 0 fundamentalCube := by
  intro x hx
  have hball : x ∈ ball (0 : Space) cutoffBump.rIn := by
    rw [mem_ball, dist_zero_right]
    exact (norm_le_two_of_mem_fundamentalCube hx).trans_lt (by norm_num [cutoffBump])
  have heq : cutoff =ᶠ[𝓝 x] (fun _ : Space => (1 : ℝ)) :=
    cutoffBump.eventuallyEq_one_of_mem_ball hball
  rw [heq.fderiv_eq]
  simp

theorem iteratedFDeriv_two_cutoff_eq_zero :
    EqOn (iteratedFDeriv ℝ 2 cutoff) 0 fundamentalCube := by
  intro x hx
  have hball : x ∈ ball (0 : Space) cutoffBump.rIn := by
    rw [mem_ball, dist_zero_right]
    exact (norm_le_two_of_mem_fundamentalCube hx).trans_lt (by norm_num [cutoffBump])
  have heq : cutoff =ᶠ[𝓝 x] (fun _ : Space => (1 : ℝ)) :=
    cutoffBump.eventuallyEq_one_of_mem_ball hball
  have hderiv := heq.iteratedFDeriv ℝ 2
  have hpoint : iteratedFDeriv ℝ 2 cutoff x =
      iteratedFDeriv ℝ 2 (fun _ : Space => (1 : ℝ)) x := hderiv.self_of_nhds
  rw [hpoint]
  have hzero0 : iteratedFDeriv ℝ 0 (fun _ : Space => (1 : ℝ)) =
      (fun _ : Space => (continuousMultilinearCurryFin0 ℝ Space ℝ).symm 1) := by
    funext y
    simp [iteratedFDeriv_zero_eq_comp]
  have hfzero0 : fderiv ℝ (iteratedFDeriv ℝ 0 (fun _ : Space => (1 : ℝ))) = 0 := by
    rw [hzero0]
    change fderiv ℝ (Function.const Space
      ((continuousMultilinearCurryFin0 ℝ Space ℝ).symm 1)) = 0
    exact fderiv_const _
  have hconst : iteratedFDeriv ℝ 1 (fun _ : Space => (1 : ℝ)) = 0 := by
    rw [show (1 : ℕ) = 0 + 1 by norm_num, iteratedFDeriv_succ_eq_comp_left]
    rw [hfzero0]
    ext y
    simp
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedFDeriv_succ_eq_comp_left, hconst]
  rw [fderiv_zero]
  ext y
  simp only [Function.comp_apply, Pi.zero_apply]
  rw [(continuousMultilinearCurryLeftEquiv ℝ (fun x => Space) ℝ).symm.map_zero]

theorem support_fderiv_cutoff_subset_shell :
    Function.support (fderiv ℝ cutoff) ⊆ interior largerCube \ fundamentalCube := by
  intro x hx
  refine ⟨tsupport_fderiv_cutoff ((subset_tsupport (fderiv ℝ cutoff)) hx), ?_⟩
  intro hcube
  exact hx (fderiv_cutoff_eq_zero hcube)

theorem support_iteratedFDeriv_two_cutoff_subset_shell :
    Function.support (iteratedFDeriv ℝ 2 cutoff) ⊆ interior largerCube \ fundamentalCube := by
  intro x hx
  refine ⟨tsupport_iteratedFDeriv_two_cutoff
    ((subset_tsupport (iteratedFDeriv ℝ 2 cutoff)) hx), ?_⟩
  intro hcube
  exact hx (iteratedFDeriv_two_cutoff_eq_zero hcube)

/-- Cutoff localization of a vector field. -/
def cutoffMul (v : SpatialField) : SpatialField := fun x => cutoff x • v x

theorem contDiff_cutoffMul {v : SpatialField} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (cutoffMul v) := by
  exact cutoff_contDiff.smul hv

theorem hasCompactSupport_cutoffMul (v : SpatialField) :
    HasCompactSupport (cutoffMul v) := by
  change HasCompactSupport (cutoff • v)
  exact hasCompactSupport_cutoff.smul_right

theorem cutoffMul_eq_on_cube (v : SpatialField) :
    EqOn (cutoffMul v) v fundamentalCube := by
  intro x hx
  simp [cutoffMul, cutoff_eq_one x hx]

theorem memHInfty_cutoffMul {v : SpatialField} (hv : ContDiff ℝ ∞ v) :
    MemHInfty (cutoffMul v) := by
  apply memHInfty_of_contDiff_memLp (contDiff_cutoffMul hv)
  intro n
  exact Continuous.memLp_of_hasCompactSupport
    ((contDiff_cutoffMul hv).continuous_iteratedFDeriv (by norm_num))
    ((hasCompactSupport_cutoffMul v).iteratedFDeriv n)

end NSFormalization.Section3.T12
