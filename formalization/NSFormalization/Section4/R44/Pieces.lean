import NSFormalization.Section4.A04.Gronwall
import NSFormalization.Section4.R43.Pieces

/-!
# R44 (Proposition 4.4) — cheap proof-route pieces

This module contains only the scalar and constant bookkeeping for
`paper/sections/04-whole-space.tex:145-174`.  The PDE input
`eq:Rcritical2`, the `J = (I-Δ)^{1/2}` weight identity, and the
`H^{-1/2}` force-slice construction remain separate analytic obligations.

The two pieces that are literally shared with R43 are imported rather than
duplicated:

* `R43.enorm_npow_two_eq_rpow_two` is the A04/C01 `ℕ`-power versus
  `ℝ`-power pin in `ℝ≥0∞`;
* `R43.criticalL3_gate_enorm` is exactly C01's absorption-gate discharge.

The new results below choose one set of universal R44 constants and close the
linear Grönwall/first-exit bootstrap once the squared `J`-energy inequality
and the force-square integral bound have been supplied.
-/

noncomputable section

namespace NSFormalization.Section4.R44

open Set intervalIntegral MeasureTheory

/-! ## Universal constant choices -/

/-- The universal small constants needed after `eq:Rcritical2`.

`theta` is simultaneously small enough for the nonlinear `J`-energy absorption
and for C01's exact gate `C₁ * ‖u‖₃ ≤ nu/4`; `c` is then small enough that
the Grönwall bound is strictly below `theta² nu²/4`.  `C = C₂ + 1` is a
positive exponential rate dominating the rate `C₂` from `eq:Rcritical2`.
All choices precede `nu` and `S`.
-/
theorem exists_rcritical2_constants {C₀ C₁ Cemb C₂ C₃ : ℝ}
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hCemb : 0 < Cemb)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 < C₃) :
    ∃ theta c C : ℝ,
      0 < theta ∧ 0 < c ∧ 0 < C ∧
      C₀ * theta < 1 / 4 ∧ C₁ * Cemb * theta ≤ 1 / 4 ∧
      C₃ * c ^ 2 < theta ^ 2 / 4 ∧ C = C₂ + 1 := by
  obtain ⟨theta, htheta, hthetaC₀, hthetaGate⟩ :=
    NSFormalization.Section4.R43.exists_critical_radius hC₀ hC₁ hCemb
  let c : ℝ := theta / (4 * (C₃ + 1))
  have hC₃one : 0 < C₃ + 1 := by linarith
  have hc : 0 < c := by simp only [c]; positivity
  have hfirst : C₀ * theta < 1 / 4 := by
    have := mul_lt_mul_of_pos_left hthetaC₀ hC₀
    field_simp at this ⊢
    exact this
  have hcsq : C₃ * c ^ 2 < theta ^ 2 / 4 := by
    have hlt : C₃ * c ^ 2 < (C₃ + 1) * c ^ 2 := by
      nlinarith [sq_pos_of_pos hc]
    have heq : (C₃ + 1) * c ^ 2 = theta ^ 2 / (16 * (C₃ + 1)) := by
      simp only [c]
      field_simp
      ring
    have hdiv : theta ^ 2 / (16 * (C₃ + 1)) < theta ^ 2 / 4 := by
      apply div_lt_div_of_pos_left (sq_pos_of_pos htheta) (by norm_num)
      nlinarith
    exact hlt.trans (heq.trans_lt hdiv)
  refine ⟨theta, c, C₂ + 1, htheta, hc, by linarith, hfirst,
    hthetaGate, hcsq, rfl⟩

/-- The radius formula produced by `exists_rcritical2_constants` implies the
strict smallness input of `criticalSquaredNormBound_radius` below.  This is the
arithmetic behind the manuscript's `c * nu^(3/2) * exp (-C*nu*S)` scaling:
the square contributes `nu^3`, the energy estimate contributes `nu⁻¹`, and
the choice `C = C₂ + 1` leaves a nonpositive exponential.
-/
theorem radius_forces_gronwall_small
    {nu S theta c C₂ C₃ F : ℝ}
    (hnu : 0 < nu) (hS : 0 ≤ S) (hC₂ : 0 ≤ C₂) (hC₃ : 0 < C₃)
    (hc : 0 < c)
    (hcsmall : C₃ * c ^ 2 < theta ^ 2 / 4)
    (hF : 0 ≤ F)
    (hFsmall : F < c * nu ^ (3 / 2 : ℝ) *
      Real.exp (-((C₂ + 1) * nu * S))) :
    C₃ * nu⁻¹ * F ^ 2 * Real.exp (C₂ * nu * S) < (theta * nu) ^ 2 / 4 := by
  have hrpow : 0 < nu ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hexp : 0 < Real.exp (-((C₂ + 1) * nu * S)) := Real.exp_pos _
  have hradius : 0 < c * nu ^ (3 / 2 : ℝ) * Real.exp (-((C₂ + 1) * nu * S)) :=
    mul_pos (mul_pos hc hrpow) hexp
  have hFsq : F ^ 2 <
      (c * nu ^ (3 / 2 : ℝ) * Real.exp (-((C₂ + 1) * nu * S))) ^ 2 :=
    (sq_lt_sq₀ hF hradius.le).2 hFsmall
  have hfactor : 0 < C₃ * nu⁻¹ * Real.exp (C₂ * nu * S) := by positivity
  have hfirst := mul_lt_mul_of_pos_left hFsq hfactor
  have hpow : (nu ^ (3 / 2 : ℝ)) ^ 2 = nu ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnu.le]
    norm_num
  have hexp_le : Real.exp (C₂ * nu * S) *
      Real.exp (-((C₂ + 1) * nu * S)) ^ 2 ≤ 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have hnuS : 0 ≤ nu * S := mul_nonneg hnu.le hS
    have hC₂nuS : 0 ≤ C₂ * nu * S := mul_nonneg (mul_nonneg hC₂ hnu.le) hS
    calc
      C₂ * nu * S + (2 : ℝ) * -((C₂ + 1) * nu * S)
          = -(C₂ * nu * S) - 2 * (nu * S) := by ring
      _ ≤ 0 := add_nonpos (neg_nonpos.mpr hC₂nuS)
        (neg_nonpos.mpr (mul_nonneg (by norm_num) hnuS))
  have hradius_bound :
      C₃ * nu⁻¹ * Real.exp (C₂ * nu * S) *
          (c * nu ^ (3 / 2 : ℝ) * Real.exp (-((C₂ + 1) * nu * S))) ^ 2
        ≤ (C₃ * c ^ 2) * nu ^ 2 := by
    have hbase : 0 ≤ (C₃ * c ^ 2) * nu ^ 2 := by positivity
    calc
      C₃ * nu⁻¹ * Real.exp (C₂ * nu * S) *
          (c * nu ^ (3 / 2 : ℝ) * Real.exp (-((C₂ + 1) * nu * S))) ^ 2
          = ((C₃ * c ^ 2) * nu ^ 2) *
              (Real.exp (C₂ * nu * S) *
                Real.exp (-((C₂ + 1) * nu * S)) ^ 2) := by
              simp only [mul_pow]
              rw [hpow]
              field_simp
      _ ≤ ((C₃ * c ^ 2) * nu ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hexp_le hbase
      _ = (C₃ * c ^ 2) * nu ^ 2 := mul_one _
  have hscale : (C₃ * c ^ 2) * nu ^ 2 < (theta ^ 2 / 4) * nu ^ 2 :=
    mul_lt_mul_of_pos_right hcsmall (sq_pos_of_pos hnu)
  calc
    C₃ * nu⁻¹ * F ^ 2 * Real.exp (C₂ * nu * S)
        = (C₃ * nu⁻¹ * Real.exp (C₂ * nu * S)) * F ^ 2 := by ring
    _ < (C₃ * nu⁻¹ * Real.exp (C₂ * nu * S)) *
        (c * nu ^ (3 / 2 : ℝ) * Real.exp (-((C₂ + 1) * nu * S))) ^ 2 := hfirst
    _ ≤ (C₃ * c ^ 2) * nu ^ 2 := hradius_bound
    _ < (theta ^ 2 / 4) * nu ^ 2 := hscale
    _ = (theta * nu) ^ 2 / 4 := by ring

/-! ## Squared `J`-energy Grönwall and first-exit bootstrap -/

/-- Scalar closure of the R44 bootstrap.

Assume `Y` is continuous and nonnegative, `Y(0)=0`, and while
`Y ≤ theta * nu` its squared energy satisfies

`E' + nu * Z² ≤ C₂ * nu * Y² + C₃ * nu⁻¹ * B²`.

If every prefix integral of `B²` is bounded by `R` and the resulting
Grönwall expression is strictly below `(theta * nu)²/4`, then
`Y ≤ theta * nu / 2` throughout `[0,T]`.  The proof uses A04's already-proved
scalar Grönwall lemma for the improvement and
`Paper1.continuous_bootstrap` (imported through `R43.Pieces`) for the first-exit
argument.  Thus no division by `Y` and no positivity assumption on `Y` beyond
its norm nonnegativity is introduced here.
-/
theorem criticalSquaredNormBound_radius
    {T nu theta C₂ C₃ R : ℝ} {Y E' Z B : ℝ → ℝ}
    (hT : 0 ≤ T) (hnu : 0 < nu) (htheta : 0 < theta)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hR : 0 ≤ R)
    (hsmall : C₃ * nu⁻¹ * R * Real.exp (C₂ * nu * T) < (theta * nu) ^ 2 / 4)
    (hY : Continuous Y) (hY0 : Y 0 = 0)
    (hYnonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ Y t)
    (hBsq : ContinuousOn (fun t => B t ^ 2) (Icc (0 : ℝ) T))
    (hBbound : ∀ t ∈ Icc (0 : ℝ) T, ∫ s in (0 : ℝ)..t, B s ^ 2 ≤ R)
    (hdE : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt (fun s => Y s ^ 2) (E' t) t)
    (hE'int : IntervalIntegrable E' volume 0 T)
    (henergy : ∀ t ∈ Ioo (0 : ℝ) T, Y t ≤ theta * nu →
      E' t + nu * Z t ^ 2 ≤ C₂ * nu * Y t ^ 2 + C₃ * nu⁻¹ * B t ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) T, Y t ≤ theta * nu / 2 := by
  have hthetaNu : 0 < theta * nu := mul_pos htheta hnu
  apply NSFormalization.Paper1.continuous_bootstrap hY
    (show Y 0 ≤ theta * nu / 2 by rw [hY0]; positivity)
    (show theta * nu / 2 < theta * nu by linarith)
  intro t ht hprefix
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
    fun x hx => ⟨hx.1, hx.2.trans ht.2⟩
  have hsub' : Ioo (0 : ℝ) t ⊆ Ioo (0 : ℝ) T :=
    fun x hx => ⟨hx.1, hx.2.trans_le ht.2⟩
  have hgron := NSFormalization.Section4.A04.gronwall_deriv
    (t₀ := (0 : ℝ)) (t₁ := t)
    (y := fun s => Y s ^ 2) (y' := E')
    (c := fun _ => C₂ * nu) (b := fun s => C₃ * nu⁻¹ * B s ^ 2)
    ht.1 (hY.pow 2).continuousOn continuousOn_const
    ((continuousOn_const.mul continuousOn_const).mul (hBsq.mono hsub))
    (fun _ _ => mul_nonneg hC₂ hnu.le)
    (fun s _ => mul_nonneg (mul_nonneg hC₃ (inv_nonneg.mpr hnu.le)) (sq_nonneg (B s)))
    (fun x hx => (hdE x (hsub' hx)).hasDerivWithinAt)
    (hE'int.mono_set (by
      rw [uIcc_of_le hT, uIcc_of_le ht.1]
      exact hsub))
    (fun x hx => by
      have hdrop : E' x ≤ C₂ * nu * Y x ^ 2 + C₃ * nu⁻¹ * B x ^ 2 := by
        have hz := mul_nonneg hnu.le (sq_nonneg (Z x))
        linarith [henergy x (hsub' hx) (hprefix x ⟨hx.1.le, hx.2.le⟩)]
      simpa only using hdrop)
    t ⟨ht.1, le_rfl⟩
  simp only [hY0, zero_pow (by decide : 2 ≠ 0), zero_add,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hgron
  rw [intervalIntegral.integral_const_mul] at hgron
  have hgron' : Y t ^ 2 ≤ (C₃ * nu⁻¹ * ∫ s in (0 : ℝ)..t, B s ^ 2) *
      Real.exp (C₂ * nu * t) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hgron
  have hexpmono : Real.exp (C₂ * nu * t) ≤ Real.exp (C₂ * nu * T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hC₂ hnu.le)
  have hcoef : 0 ≤ C₃ * nu⁻¹ := mul_nonneg hC₃ (inv_nonneg.mpr hnu.le)
  have hint : ∫ s in (0 : ℝ)..t, B s ^ 2 ≤ R := hBbound t ht
  have hbound : Y t ^ 2 < (theta * nu) ^ 2 / 4 := by
    calc
      Y t ^ 2 ≤ (C₃ * nu⁻¹ * ∫ s in (0 : ℝ)..t, B s ^ 2) *
          Real.exp (C₂ * nu * t) := hgron'
      _ ≤ (C₃ * nu⁻¹ * R) * Real.exp (C₂ * nu * t) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hint hcoef)
          (Real.exp_pos _).le
      _ ≤ (C₃ * nu⁻¹ * R) * Real.exp (C₂ * nu * T) :=
        mul_le_mul_of_nonneg_left hexpmono (mul_nonneg hcoef hR)
      _ < (theta * nu) ^ 2 / 4 := by simpa [mul_assoc] using hsmall
  have hYt := hYnonneg t ht
  nlinarith [sq_pos_of_pos hthetaNu]

end NSFormalization.Section4.R44
