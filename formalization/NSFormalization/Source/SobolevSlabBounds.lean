import Euler.MeanSobolevBoundedField
import NavierStokes.R3.ProblemStatement

/-!
# Uniform physical bounds from continuous H-infinity paths

This module uses the source's actual smooth L2 fields: every spatial Frechet
derivative belongs to L2. Continuity of all these L2 jets is the projective
integer-Sobolev topology. The pointwise bounds below directly reuse OpenAI's
Sobolev evaluation construction; no embedding estimate is assumed here.
-/
noncomputable section
namespace NSFormalization.Source.SobolevSlabBounds
open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field
open scoped ContDiff

variable {K V : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_uniform_pointwise_bound (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t x, ‖(A t).field x‖ ≤ B := by
  have hc := EulerMeanSobolevBoundedField.continuous_finiteField A hA
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t x
  rw [← EulerMeanSobolevBoundedField.finiteField_apply]
  exact (BoundedContinuousFunction.norm_coe_le_norm _ x).trans
    ((hC t (mem_univ t)).trans (le_max_left _ _))

theorem exists_uniform_derivative_bound (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t x, ‖fderiv ℝ (A t).field x‖ ≤ B := by
  exact exists_uniform_pointwise_bound (fun t => (A t).derivative)
    (continuous_jetLp_derivative A hA)

theorem exists_uniform_square_integral_bound (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ t,
      Integrable (fun x => ‖(A t).field x‖ ^ 2) ∧
      (∫ x, ‖(A t).field x‖ ^ 2) ≤ E := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_toLp A (hA 0)).continuousOn
  refine ⟨(max C 0) ^ 2, sq_nonneg _, ?_⟩
  intro t
  refine ⟨(memLp_two_iff_integrable_sq_norm (A t).memLp.1).mp (A t).memLp, ?_⟩
  have he : (∫ x, ‖(A t).field x‖ ^ 2) = ‖(A t).toLp‖ ^ 2 := by
    rw [EulerLpConvergence.norm_sq_eq_integral]
    exact integral_congr_ae ((A t).toLp_ae.mono (fun _ hx => by dsimp only; rw [hx]))
  rw [he]
  have hb := (hC t (mem_univ t)).trans (le_max_left C 0)
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

end NSFormalization.Source.SobolevSlabBounds
