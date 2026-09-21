import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import NavierStokes.ProblemStatement

/-!
# Smooth fields with square-integrable jets, and their coordinate derivatives

Support layer for task `A05` (`collaboration/tasks/A05.md`), unit `U9` of
`research/A05/COMPARISON.md:213`.  Nothing here is Fourier analysis: the whole
file is calculus on `R³` plus `L²` bookkeeping.

`SmoothL2` is the **jet form** of the manuscript's smooth `H^∞` class
(`paper/sections/02-preliminaries.tex:12` eq:Rinitial,
`paper/sections/appendix-b-embeddings.tex:36-37`): a smooth field all of whose
Fréchet jets are square integrable.  It is the field-for-field copy of the
vendor's `EulerLpTranslation.SmoothL2Field`
(`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31-34`), rewritten here so
that this file does not import the Euler development.

`dirDeriv i` is `∂_i`, the derivative along the `i`-th unit coordinate vector,
i.e. the `i`-th entry of `paper/sections/01-introduction.tex:145` eq:Enorm's
gradient tensor.
-/

noncomputable section

open MeasureTheory
open NavierStokes.ProblemStatement
open scoped ContDiff ENNReal

namespace NSFormalization.Section4.A05

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A smooth field on `R³` all of whose Fréchet jets are square integrable.
This is `EulerLpTranslation.SmoothL2Field`
(`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31-34`) as a predicate on
the field instead of a bundled structure. -/
def SmoothL2 (w : Space → F) : Prop :=
  ContDiff ℝ ∞ w ∧ ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n w) 2 volume

namespace SmoothL2

theorem contDiff {w : Space → F} (h : SmoothL2 w) : ContDiff ℝ ∞ w := h.1

/-- Order zero of the jet hypothesis, with `‖iteratedFDeriv ℝ 0 w x‖ = ‖w x‖`. -/
theorem memLp {w : Space → F} (h : SmoothL2 w) : MemLp w 2 volume :=
  (h.2 0).congr_norm h.1.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => norm_iteratedFDeriv_zero)

/-- The Fréchet derivative of a `SmoothL2` field is `SmoothL2`: its order-`n`
jet has the same pointwise norm as the order-`(n+1)` jet of the field.  Same
proof as `EulerLpTranslation.SmoothL2Field.derivative`
(`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:45-50`). -/
theorem fderiv {w : Space → F} (h : SmoothL2 w) : SmoothL2 (fderiv ℝ w) := by
  refine ⟨h.1.fderiv_right (m := ∞) (by simp), fun n => ?_⟩
  have hle : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  exact (h.2 (n + 1)).congr_norm
    (((h.1.fderiv_right (m := ∞) (by simp)).continuous_iteratedFDeriv hle).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => norm_iteratedFDeriv_fderiv.symm)

/-- Post-composition with a continuous linear map preserves `SmoothL2`. -/
theorem clm {w : Space → F} (h : SmoothL2 w) (L : F →L[ℝ] G) :
    SmoothL2 (fun x => L (w x)) := by
  refine ⟨L.contDiff.comp h.1, fun n => ?_⟩
  have hc : ContDiff ℝ ∞ (fun x => L (w x)) := L.contDiff.comp h.1
  have hle : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  have hsm : MemLp ((‖L‖ : ℝ) • iteratedFDeriv ℝ n w) 2 volume :=
    MemLp.const_smul (h.2 n) (‖L‖ : ℝ)
  refine MemLp.mono hsm ((hc.continuous_iteratedFDeriv hle).aestronglyMeasurable) ?_
  filter_upwards with x
  have hb := L.norm_iteratedFDeriv_comp_left (h.1.contDiffAt (x := x)) (n := n) hle
  have he : ‖(‖L‖ • iteratedFDeriv ℝ n w) x‖ = ‖L‖ * ‖iteratedFDeriv ℝ n w x‖ := by
    simp [norm_smul]
  rw [he]
  exact hb

end SmoothL2

/-- `∂_i`: the derivative along the `i`-th unit coordinate vector
(`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:39`). -/
def dirDeriv (i : Fin 3) (w : Space → F) : Space → F :=
  fun x => fderiv ℝ w x (coordinateVector i)

theorem dirDeriv_eq_clm (i : Fin 3) (w : Space → F) :
    dirDeriv i w = fun x => (ContinuousLinearMap.apply ℝ F (coordinateVector i)) (fderiv ℝ w x) :=
  rfl

theorem SmoothL2.dir {w : Space → F} (h : SmoothL2 w) (i : Fin 3) : SmoothL2 (dirDeriv i w) :=
  h.fderiv.clm (ContinuousLinearMap.apply ℝ F (coordinateVector i))

/-- A repeated coordinate derivative is an entry of the second Fréchet
derivative. -/
theorem dirDeriv_dirDeriv_eq {w : Space → F} (h : ContDiff ℝ ∞ w) (i j : Fin 3) (x : Space) :
    dirDeriv i (dirDeriv j w) x
      = fderiv ℝ (fderiv ℝ w) x (coordinateVector i) (coordinateVector j) := by
  have hd : HasFDerivAt (fderiv ℝ w) (fderiv ℝ (fderiv ℝ w) x) x :=
    ((h.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt
  have hc := (ContinuousLinearMap.apply ℝ F (coordinateVector j)).hasFDerivAt.comp x hd
  simp only [Function.comp_def] at hc
  show fderiv ℝ (dirDeriv j w) x (coordinateVector i) = _
  rw [dirDeriv_eq_clm, hc.fderiv]
  rfl

/-- Clairaut: coordinate derivatives of a smooth field commute. -/
theorem dirDeriv_comm {w : Space → F} (h : ContDiff ℝ ∞ w) (i j : Fin 3) :
    dirDeriv i (dirDeriv j w) = dirDeriv j (dirDeriv i w) := by
  funext x
  rw [dirDeriv_dirDeriv_eq h, dirDeriv_dirDeriv_eq h]
  exact (h.contDiffAt (x := x)).isSymmSndFDerivAt (by simp) _ _

/-! ## Two crude norm comparisons

Both are `l² ≤ l¹` estimates on three terms.  They cost a factor of at most `3`
in the final constant, which `appendix-b-embeddings.tex:109-110` leaves free. -/

/-- The operator norm of a map out of `R³` is at most the sum of the norms of
the three images of the unit coordinate vectors. -/
theorem opNorm_le_sum (T : Space →L[ℝ] G) : ‖T‖ ≤ ∑ i : Fin 3, ‖T (coordinateVector i)‖ := by
  refine T.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _) fun y => ?_
  have hy : y = ∑ i : Fin 3, y i • coordinateVector i := by
    ext j; simp [coordinateVector, Pi.single_apply]
  calc ‖T y‖ = ‖∑ i : Fin 3, y i • T (coordinateVector i)‖ := by
        conv_lhs => rw [hy]
        simp [map_sum]
    _ ≤ ∑ i : Fin 3, ‖y i • T (coordinateVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖y‖ * ‖T (coordinateVector i)‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le y i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖T (coordinateVector i)‖) * ‖y‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => mul_comm (‖y‖) (‖T (coordinateVector i)‖)

/-- The Frobenius (`PiLp 2`) norm of an assembled tensor column is at most the
sum of the norms of its three entries. -/
theorem norm_toLp_le_sum (g : Fin 3 → Space) :
    ‖(WithLp.toLp 2 g : WithLp 2 (Fin 3 → Space))‖ ≤ ∑ j : Fin 3, ‖g j‖ := by
  rw [PiLp.norm_eq_of_L2]
  have h : ∑ j : Fin 3, ‖(WithLp.toLp 2 g : WithLp 2 (Fin 3 → Space)) j‖ ^ 2
      ≤ (∑ j : Fin 3, ‖g j‖) ^ 2 := by
    simpa using Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg (g j))
  calc Real.sqrt (∑ j : Fin 3, ‖(WithLp.toLp 2 g : WithLp 2 (Fin 3 → Space)) j‖ ^ 2)
      ≤ Real.sqrt ((∑ j : Fin 3, ‖g j‖) ^ 2) := Real.sqrt_le_sqrt h
    _ = ∑ j : Fin 3, ‖g j‖ := Real.sqrt_sq (Finset.sum_nonneg fun j _ => norm_nonneg _)

omit [NormedSpace ℝ F] [NormedSpace ℝ G] in
/-- An `L^p` triangle inequality specialised to a pointwise `l¹` majorant. -/
theorem eLpNorm_le_sum_of_norm_le {p : ℝ≥0∞} (hp : 1 ≤ p) {ι : Type*} [Fintype ι]
    {f : Space → F} {g : ι → Space → G}
    (hg : ∀ i, AEStronglyMeasurable (g i) volume)
    (h : ∀ x, ‖f x‖ ≤ ∑ i, ‖g i x‖) :
    eLpNorm f p volume ≤ ∑ i, eLpNorm (g i) p volume := by
  calc eLpNorm f p volume ≤ eLpNorm (fun x => ∑ i, ‖g i x‖) p volume := eLpNorm_mono_real h
    _ = eLpNorm (∑ i : ι, fun x => ‖g i x‖) p volume := by
        congr 1; funext x; simp
    _ ≤ ∑ i : ι, eLpNorm (fun x => ‖g i x‖) p volume :=
        eLpNorm_sum_le (fun i _ => (hg i).norm) hp
    _ = ∑ i : ι, eLpNorm (g i) p volume := by simp [eLpNorm_norm]

end NSFormalization.Section4.A05
