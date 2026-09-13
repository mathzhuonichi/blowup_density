import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import NSFormalization.Section4.A05.SmoothJets

/-!
# `‖D²v‖₂ = ‖Δv‖₂` for smooth fields with square-integrable jets

`paper/sections/04-whole-space.tex:112`: "The derivative estimate
`‖∇u‖₆ ≤ C‖Δu‖₂` follows from the `Ḣ¹→L⁶` case of
Lemma~\ref{lem:critical-embeddings}, **since Plancherel gives
`‖D²u‖₂ = ‖Δu‖₂`**."  The manuscript's justification is Plancherel; the proof
below is Fourier-free and uses integration by parts instead, so no normalization
convention enters (`research/A05/COMPARISON.md:128`: "the `gradientLSix` clause
has no normalization content at all").

The identity proved is, for every pair of coordinate directions `i`, `j`,
`∫⟪∂_i∂_j v, ∂_i∂_j v⟫ = ∫⟪∂_i∂_i v, ∂_j∂_j v⟫`, whose double sum over `i, j`
is exactly `‖D²v‖₂² = ‖Δv‖₂²`.  The two integrations by parts carry **no
boundary term** because
`MeasureTheory.integral_bilinear_fderiv_right_eq_neg_left_of_integrable`
(`Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean:195`) asks only
that the three pairings be integrable, which square integrability of the jets of
order one to three supplies by Cauchy-Schwarz.  No decay at infinity is assumed
and no cutoff is used.

Jets of order three are genuinely used (they are the `f'g` pairing of the first
integration by parts); jets of order four and higher are not.  A smooth `H^∞`
field supplies every order.
-/

noncomputable section

open MeasureTheory
open NavierStokes.ProblemStatement
open scoped ContDiff ENNReal RealInnerProductSpace

namespace NSFormalization.Section4.A05

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cauchy-Schwarz: the pointwise inner product of two `L²` fields is
integrable. -/
theorem integrable_inner_of_memLp {a b : Space → E}
    (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) :
    Integrable (fun x => ⟪a x, b x⟫) volume := by
  have hm := MemLp.integrable_mul ha.norm hb.norm
  refine Integrable.mono hm (ha.aestronglyMeasurable.inner hb.aestronglyMeasurable) ?_
  filter_upwards with x
  have h := abs_real_inner_le_norm (a x) (b x)
  simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _)] using h

/-- Integration by parts along the `i`-th coordinate direction, with no boundary
term: the two fields need only be smooth with square-integrable jets. -/
theorem integral_inner_dirDeriv_right {a b : Space → E}
    (ha : SmoothL2 a) (hb : SmoothL2 b) (i : Fin 3) :
    ∫ x, ⟪a x, dirDeriv i b x⟫ = -∫ x, ⟪dirDeriv i a x, b x⟫ :=
  integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)) (v := coordinateVector i)
    (integrable_inner_of_memLp (ha.dir i).memLp hb.memLp)
    (integrable_inner_of_memLp ha.memLp (hb.dir i).memLp)
    (integrable_inner_of_memLp ha.memLp hb.memLp)
    (fun x _ => (ha.contDiff.differentiable (by simp)).differentiableAt)
    (fun x _ => (hb.contDiff.differentiable (by simp)).differentiableAt)

/-- `Δ = ∑ᵢ ∂ᵢ∂ᵢ`, the componentwise Euclidean Laplacian of
`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:76`, written on a
spatial field. -/
def lap (w : Space → E) : Space → E := fun x => ∑ i : Fin 3, dirDeriv i (dirDeriv i w) x

/-- The single entry of `‖D²v‖₂² = ‖Δv‖₂²`: two integrations by parts and one
use of Clairaut move both derivatives from one factor to the other. -/
theorem integral_inner_hessian {w : Space → E} (hw : SmoothL2 w) (i j : Fin 3) :
    ∫ x, ⟪dirDeriv i (dirDeriv j w) x, dirDeriv i (dirDeriv j w) x⟫
      = ∫ x, ⟪dirDeriv i (dirDeriv i w) x, dirDeriv j (dirDeriv j w) x⟫ := by
  have h1 := integral_inner_dirDeriv_right ((hw.dir j).dir i) (hw.dir j) i
  have h2 : dirDeriv i (dirDeriv i (dirDeriv j w)) = dirDeriv j (dirDeriv i (dirDeriv i w)) := by
    rw [dirDeriv_comm hw.contDiff i j, dirDeriv_comm (hw.dir i).contDiff i j]
  have h3 := integral_inner_dirDeriv_right (hw.dir j) ((hw.dir i).dir i) j
  rw [h1, h2]
  have h4 : ∀ x : Space, ⟪dirDeriv j (dirDeriv i (dirDeriv i w)) x, dirDeriv j w x⟫
      = ⟪dirDeriv j w x, dirDeriv j (dirDeriv i (dirDeriv i w)) x⟫ := fun x => real_inner_comm _ _
  simp only [h4]
  rw [h3, neg_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_comm _ _)

/-- `‖D²v‖₂² = ‖Δv‖₂²`, the identity `04-whole-space.tex:112` attributes to
Plancherel. -/
theorem sum_integral_hessian {w : Space → E} (hw : SmoothL2 w) :
    ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, ‖dirDeriv i (dirDeriv j w) x‖ ^ 2
      = ∫ x, ‖lap w x‖ ^ 2 := by
  have hint : ∀ i j : Fin 3,
      Integrable (fun x => ⟪dirDeriv i (dirDeriv i w) x, dirDeriv j (dirDeriv j w) x⟫) volume :=
    fun i j => integrable_inner_of_memLp ((hw.dir i).dir i).memLp ((hw.dir j).dir j).memLp
  have hstep : ∀ i j : Fin 3, ∫ x, ‖dirDeriv i (dirDeriv j w) x‖ ^ 2
      = ∫ x, ⟪dirDeriv i (dirDeriv i w) x, dirDeriv j (dirDeriv j w) x⟫ := by
    intro i j
    rw [← integral_inner_hessian hw i j]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun x => (real_inner_self_eq_norm_sq _).symm)
  have hlap : ∫ x, ‖lap w x‖ ^ 2
      = ∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
          ⟪dirDeriv i (dirDeriv i w) x, dirDeriv j (dirDeriv j w) x⟫ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖lap w x‖ ^ 2 = _
    rw [← real_inner_self_eq_norm_sq]
    simp only [lap, sum_inner, inner_sum]
    exact Finset.sum_comm
  simp only [hstep]
  rw [hlap, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  exact Finset.sum_congr rfl fun i _ => (integral_finsetSum _ (fun j _ => hint i j)).symm

/-- Each entry of the Hessian is dominated by the Laplacian in `L²`, because the
entries are the nonnegative summands of the identity above. -/
theorem integral_hessian_le {w : Space → E} (hw : SmoothL2 w) (i j : Fin 3) :
    ∫ x, ‖dirDeriv i (dirDeriv j w) x‖ ^ 2 ≤ ∫ x, ‖lap w x‖ ^ 2 := by
  rw [← sum_integral_hessian hw]
  have hnn : ∀ a b : Fin 3, 0 ≤ ∫ x, ‖dirDeriv a (dirDeriv b w) x‖ ^ 2 :=
    fun a b => integral_nonneg fun x => by positivity
  calc ∫ x, ‖dirDeriv i (dirDeriv j w) x‖ ^ 2
      ≤ ∑ b : Fin 3, ∫ x, ‖dirDeriv i (dirDeriv b w) x‖ ^ 2 :=
        Finset.single_le_sum (f := fun b => ∫ x, ‖dirDeriv i (dirDeriv b w) x‖ ^ 2)
          (fun b _ => hnn i b) (Finset.mem_univ j)
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ∫ x, ‖dirDeriv a (dirDeriv b w) x‖ ^ 2 :=
        Finset.single_le_sum
          (f := fun a => ∑ b : Fin 3, ∫ x, ‖dirDeriv a (dirDeriv b w) x‖ ^ 2)
          (fun a _ => Finset.sum_nonneg fun b _ => hnn a b) (Finset.mem_univ i)

theorem memLp_lap {w : Space → E} (hw : SmoothL2 w) : MemLp (lap w) 2 volume :=
  memLp_finsetSum _ (fun i _ => ((hw.dir i).dir i).memLp)

omit [InnerProductSpace ℝ E] in
/-- Transfer of an `∫‖·‖²` comparison to the extended-valued `L²` seminorms. -/
theorem eLpNorm_le_of_integral_sq_le {f g : Space → E}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (h : ∫ x, ‖f x‖ ^ 2 ≤ ∫ x, ‖g x‖ ^ 2) :
    eLpNorm f 2 volume ≤ eLpNorm g 2 volume := by
  have hrw : ∀ h : Space → E, (∫ x, ‖h x‖ ^ ((2 : ℝ≥0∞).toReal)) = ∫ x, ‖h x‖ ^ 2 := by
    intro h
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖h x‖ ^ ((2 : ℝ≥0∞).toReal) = ‖h x‖ ^ (2 : ℕ)
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), hrw, hrw]
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ?_ h (by positivity))
  exact integral_nonneg fun x => by positivity

/-- `‖∂_i∂_j v‖₂ ≤ ‖Δv‖₂`. -/
theorem eLpNorm_hessian_le {w : Space → E} (hw : SmoothL2 w) (i j : Fin 3) :
    eLpNorm (dirDeriv i (dirDeriv j w)) 2 volume ≤ eLpNorm (lap w) 2 volume :=
  eLpNorm_le_of_integral_sq_le ((hw.dir j).dir i).memLp (memLp_lap hw)
    (integral_hessian_le hw i j)

end NSFormalization.Section4.A05
