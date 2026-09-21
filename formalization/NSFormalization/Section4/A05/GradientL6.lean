import NSFormalization.Section4.A05.HessianLaplacian
import NavierStokes.R3.SmoothSobolevL6

/-!
# `‖∇v‖₆ ≤ C‖Δv‖₂` for smooth fields with square-integrable jets

Third line of `eq:critical-derived`, Lemma B.1 ("Critical embeddings on the two
domains", `lem:critical-embeddings`),
`paper/sections/appendix-b-embeddings.tex:32`, in the Euclidean case and in the
form Propositions 4.3 and 4.4 consume it
(`paper/sections/04-whole-space.tex:110-112`, `:171`).

Route, which differs from the manuscript's (`research/A05/COMPARISON.md:308-316`
records the difference and accepts it):

* the manuscript derives the clause from its own `Ḣ¹ → L⁶` embedding plus
  Plancherel;
* here the `H¹ → L⁶` half is the **Fourier-free** vendor inequality
  `NavierStokesR3.RieszTestOperators.smooth_eLpNorm_six_le`
  (`vendor/NavierStokesAndEuler/NavierStokes/R3/SmoothSobolevL6.lean:72`), which
  needs no compact support, and the `‖D²v‖₂ = ‖Δv‖₂` half is
  `NSFormalization.Section4.A05.eLpNorm_hessian_le`, proved by integration by
  parts.  Nothing in this file mentions a Fourier transform, so no `(2π)` factor
  can enter.

Both crude `l² ≤ l¹` steps (`opNorm_le_sum`, `norm_toLp_le_sum`) and the three
coordinate directions cost a factor `9`; `appendix-b-embeddings.tex:109-110`
leaves the constant free ("All constants depend only on the fixed exponents,
domain, and norm conventions, not on the field or its frequency support").
-/

noncomputable section

open MeasureTheory
open NavierStokes.ProblemStatement
open scoped ContDiff ENNReal NNReal

namespace NSFormalization.Section4.A05

/-- The gradient tensor `∇v` as the `PiLp 2` assembly of its three columns, so
that its pointwise norm is the Frobenius quantity `(∑_{i,j}|∂_iv_j|²)^{1/2}` of
`paper/sections/01-introduction.tex:103` and not an operator norm.  This is
definitionally `BlowupDensity.Contracts.V1.Data.spatialGradient` on the
time-independent lift; the binding records the `rfl` bridge. -/
def gradTensor (v : Space → Space) : Space → WithLp 2 (Fin 3 → Space) :=
  fun x => WithLp.toLp 2 (fun j => dirDeriv j v x)

/-- The constant of `eq:critical-derived`, third line.  Three coordinate
directions times three tensor columns times the vendor's Sobolev constant, plus
one so that positivity is available without unfolding Mathlib's irreducible
`eLpNormLESNormFDerivOfEqInnerConst`. -/
def gradientL6Const : ℝ :=
  9 * (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ) + 1

theorem gradientL6Const_pos : 0 < gradientL6Const := by
  have : (0 : ℝ) ≤ (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ) :=
    (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2).coe_nonneg
  simp only [gradientL6Const]
  linarith

/-- `‖∇v‖_{L⁶} ≤ C‖Δv‖_{L²}` (`appendix-b-embeddings.tex:32`,
`04-whole-space.tex:112`), for every smooth field on `R³` whose Fréchet jets are
square integrable. -/
theorem eLpNorm_gradTensor_six_le {v : Space → Space} (hv : SmoothL2 v) :
    eLpNorm (gradTensor v) 6 volume
      ≤ ENNReal.ofReal gradientL6Const * eLpNorm (lap v) 2 volume := by
  set C : ℝ≥0 := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 with hC
  set L : ℝ≥0∞ := eLpNorm (lap v) 2 volume with hL
  -- Each column of the Hessian is bounded by the Laplacian in `L²`.
  have hfd : ∀ j : Fin 3, eLpNorm (fderiv ℝ (dirDeriv j v)) 2 volume ≤ 3 * L := by
    intro j
    have h1 : eLpNorm (fderiv ℝ (dirDeriv j v)) 2 volume
        ≤ ∑ i : Fin 3, eLpNorm (dirDeriv i (dirDeriv j v)) 2 volume :=
      eLpNorm_le_sum_of_norm_le (by norm_num)
        (fun i => ((hv.dir j).dir i).memLp.aestronglyMeasurable)
        (fun x => opNorm_le_sum (fderiv ℝ (dirDeriv j v) x))
    refine h1.trans ?_
    calc ∑ i : Fin 3, eLpNorm (dirDeriv i (dirDeriv j v)) 2 volume
        ≤ ∑ _i : Fin 3, L := Finset.sum_le_sum fun i _ => eLpNorm_hessian_le hv i j
      _ = 3 * L := by simp [Finset.sum_const]
  -- The support-free `H¹ → L⁶` inequality, applied to each column `∂_j v`.
  have hsix : ∀ j : Fin 3, eLpNorm (dirDeriv j v) 6 volume ≤ (C : ℝ≥0∞) * (3 * L) := by
    intro j
    refine (NavierStokesR3.RieszTestOperators.smooth_eLpNorm_six_le
      ((hv.dir j).contDiff.of_le (by simp)) (hv.dir j).memLp).trans ?_
    gcongr
    exact hfd j
  have hg : eLpNorm (gradTensor v) 6 volume ≤ ∑ j : Fin 3, eLpNorm (dirDeriv j v) 6 volume :=
    eLpNorm_le_sum_of_norm_le (by norm_num)
      (fun j => (hv.dir j).memLp.aestronglyMeasurable)
      (fun x => norm_toLp_le_sum (fun j => dirDeriv j v x))
  have hnine : eLpNorm (gradTensor v) 6 volume ≤ 9 * (C : ℝ≥0∞) * L := by
    refine hg.trans ?_
    calc ∑ _j : Fin 3, eLpNorm (dirDeriv _j v) 6 volume
        ≤ ∑ _j : Fin 3, (C : ℝ≥0∞) * (3 * L) := Finset.sum_le_sum fun j _ => hsix j
      _ = 9 * (C : ℝ≥0∞) * L := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  refine hnine.trans ?_
  have hco : 9 * (C : ℝ≥0∞) = ENNReal.ofReal (9 * (C : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal]
    norm_num
  rw [hco]
  gcongr
  simp only [gradientL6Const]
  linarith

end NSFormalization.Section4.A05
