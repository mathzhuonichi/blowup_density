import NSFormalization.Section3.T22.WeightRatio
import NSFormalization.Section3.T22.CutoffKernel
import NSFormalization.Source.YoungConvolution

/-!
# T22 U-A3 — the analytic core of `cutoffMultiplier` (`03-torus.tex:616-624`)

`BoundedDomainNormAPI.cutoffMultiplier` (`research/T22/Spec.lean:140-144`,
`Section3/T22/Domain.lean`) asserts that a fixed smooth compactly supported
cutoff `χ` acts as a bounded multiplier on every inhomogeneous Sobolev datum
space `H^s(ℝ³)`, for **every real** order `s`.

In the weighted Fourier `L²` model of the datum layer, the datum of a field is
its Bessel-weighted Fourier transform, and the datum of the cutoff product is
the same weight applied to the **convolution** of the cutoff transform with the
input transform.  The whole `H^s` bound therefore reduces to a single, purely
real-analytic estimate on `L²` convolutions with the Bessel weight — the
`Peetre × kernel-mass × Young` route named by `research/T22/T22_SPLIT.md`
(unit `U-A3`):

* **Peetre** (lane 386, `WeightRatio.weight_ratio_le_const`) dominates the output
  weight `(1+‖ξ‖²)^{s/2}` pointwise by `peetreConst s · (1+‖ξ-η‖²)^{|s|/2}·(1+‖η‖²)^{s/2}`;
* the **kernel mass** `∫ (1+‖ζ‖²)^{|s|/2}‖𝓕χ ζ‖` (lane 391,
  `CutoffKernel.integrable_weighted_fourier_cutoff`) is finite;
* **Young** `L¹ ∗ L² → L²` (`Source.YoungConvolution.memLp_convolution_one_two`)
  turns the pointwise convolution domination into the `L²` operator bound.

This module supplies exactly that estimate:
`eLpNorm_besselWeight_scalarConvolution_le` — the abstract weighted-convolution
`L²` multiplier bound with the explicit constant
`peetreConst s · ∫ (1+‖ζ‖²)^{|s|/2}‖K ζ‖` — and its specialization to the
cutoff transform kernel `K = angularFourier χ_ℂ`
(`eLpNorm_cutoff_multiplier_le`, constant `cutoffMultiplierConst s χ`).

## Scope note (honest partial, `research/T22/ATTEMPTS_UA3.md`)

This is the genuine analytic engine of `U-A3`.  The remaining gap to the
verbatim `cutoffMultiplier` field is **not** analytic: it is the datum-layer
identification, for a *general tempered* datum `A`, of `angularRealization`'s
cutoff product `B` with `besselW s • scalarConvolution (angularFourier χ_ℂ)
(besselW (-s) • (A i))`, i.e. the `L²`-level angular Fourier product↔convolution
identity, together with the real-subspace preservation and the `smulLeftCLM`
graph.  Those residual statements are recorded in `research/T22/ATTEMPTS_UA3.md`;
they are datum-model plumbing on top of the estimate proved here, not new
analysis.
-/

noncomputable section

namespace NSFormalization.Section3.T22

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source (angularFourier)
open NSFormalization.Source.YoungConvolution
open NavierStokes.R3ConvolutionYoung (scalarConvolution)
open scoped ContDiff ENNReal

/-- The inhomogeneous Sobolev (Japanese-bracket / Bessel) weight
`(1+‖ξ‖²)^{t/2}`.  Its real magnitude is exactly `‖sobolevBesselWeight t ξ‖`
(lane 386, `sobolevBesselWeight_norm`). -/
def besselW (t : ℝ) (ξ : Space) : ℝ := (1 + ‖ξ‖ ^ 2) ^ (t / 2)

theorem besselW_nonneg (t : ℝ) (ξ : Space) : 0 ≤ besselW t ξ := by
  unfold besselW; positivity

/-- **Peetre domination in the `besselW` spelling** (lane 386,
`weight_ratio_le_const`, with `η := ξ - y` so `ξ - η = y`).  The output weight
`besselW s ξ` is dominated by `peetreConst s` times the shifted input weight
`besselW s (ξ - y)` and the kernel weight `besselW |s| y`. -/
theorem besselW_peetre (s : ℝ) (ξ y : Space) :
    besselW s ξ ≤ peetreConst s * besselW s (ξ - y) * besselW |s| y := by
  have h := weight_ratio_le_const s ξ (ξ - y)
  rw [show ξ - (ξ - y) = y by abel] at h
  simpa only [besselW] using h

/-- **The analytic engine of `U-A3`.**  For every real order `s`, every
integrable weighted kernel `K` (weight `(1+‖ζ‖²)^{|s|/2}`) and every input
transform `g` whose Bessel-weighted profile `besselW s • g` is in `L²`, the
Bessel-weighted convolution `besselW s • (K ∗ g)` is in `L²` with

`‖besselW s • (K ∗ g)‖_{L²} ≤ (peetreConst s · ∫ (1+‖ζ‖²)^{|s|/2}‖K ζ‖) · ‖besselW s • g‖_{L²}`.

Route: pointwise `‖besselW s ξ • (K ∗ g) ξ‖ ≤ peetreConst s · (K̃ ∗ g̃) ξ` with
`K̃ = besselW |s| · ‖K‖`, `g̃ = ‖besselW s • g‖` (Peetre inside the convolution
integral), then Young `L¹ ∗ L² → L²`. -/
theorem eLpNorm_besselWeight_scalarConvolution_le (s : ℝ) (K g : Space → ℂ)
    (hK : Integrable (fun ζ : Space => besselW |s| ζ * ‖K ζ‖))
    (hg : MemLp (fun η : Space => (besselW s η : ℝ) • g η) 2 volume) :
    eLpNorm (fun ξ : Space => (besselW s ξ : ℝ) • scalarConvolution K g ξ) 2 volume ≤
      ENNReal.ofReal (peetreConst s * ∫ ζ : Space, besselW |s| ζ * ‖K ζ‖)
        * eLpNorm (fun η : Space => (besselW s η : ℝ) • g η) 2 volume := by
  classical
  set a : Space → ℂ := fun η => (besselW s η : ℝ) • g η with ha
  set KK : Space → ℝ := fun ζ => besselW |s| ζ * ‖K ζ‖ with hKKdef
  set GG : Space → ℝ := fun η => ‖a η‖ with hGGdef
  have hKKnonneg : ∀ ζ, 0 ≤ KK ζ := fun ζ =>
    mul_nonneg (besselW_nonneg _ _) (norm_nonneg _)
  have hMemKK : MemLp KK 1 volume := memLp_one_iff_integrable.mpr hK
  have hMemGG : MemLp GG 2 volume := hg.norm
  obtain ⟨hInt, _hMemConv, hReal⟩ := memLp_convolution_one_two hMemKK hMemGG
  have hMemConv : MemLp (scalarConvolution KK GG) 2 volume :=
    (memLp_convolution_one_two hMemKK hMemGG).2.1
  -- `GG η = besselW s η * ‖g η‖`.
  have hGGeq : ∀ η, GG η = besselW s η * ‖g η‖ := by
    intro η
    rw [hGGdef, ha]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (besselW_nonneg s η)]
  -- Pointwise a.e. domination `‖besselW s ξ • (K ∗ g) ξ‖ ≤ peetreConst s · (K̃ ∗ g̃) ξ`.
  have hpt : ∀ᵐ ξ ∂volume,
      ‖(besselW s ξ : ℝ) • scalarConvolution K g ξ‖ ≤
        peetreConst s * scalarConvolution KK GG ξ := by
    filter_upwards [hInt] with ξ hξint
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (besselW_nonneg s ξ)]
    -- `‖(K ∗ g) ξ‖ ≤ ∫ y, ‖K y‖ * ‖g (ξ - y)‖`.
    have hnorm : ‖scalarConvolution K g ξ‖ ≤ ∫ y : Space, ‖K y‖ * ‖g (ξ - y)‖ := by
      have hsc : scalarConvolution K g ξ = ∫ y : Space, K y * g (ξ - y) := rfl
      rw [hsc]
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      apply integral_congr_ae
      filter_upwards [] with y
      rw [norm_mul]
    have hstep1 : besselW s ξ * ‖scalarConvolution K g ξ‖ ≤
        besselW s ξ * ∫ y : Space, ‖K y‖ * ‖g (ξ - y)‖ :=
      mul_le_mul_of_nonneg_left hnorm (besselW_nonneg s ξ)
    have hpull : besselW s ξ * ∫ y : Space, ‖K y‖ * ‖g (ξ - y)‖ =
        ∫ y : Space, besselW s ξ * (‖K y‖ * ‖g (ξ - y)‖) :=
      (integral_const_mul (besselW s ξ) _).symm
    have hmaj_int :
        Integrable (fun y : Space => peetreConst s * (KK y * GG (ξ - y))) volume :=
      hξint.const_mul (peetreConst s)
    have hzero : (0 : Space → ℝ) ≤ᵐ[volume]
        (fun y : Space => besselW s ξ * (‖K y‖ * ‖g (ξ - y)‖)) := by
      filter_upwards [] with y
      simp only [Pi.zero_apply]
      exact mul_nonneg (besselW_nonneg s ξ)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hle : (fun y : Space => besselW s ξ * (‖K y‖ * ‖g (ξ - y)‖)) ≤ᵐ[volume]
        (fun y : Space => peetreConst s * (KK y * GG (ξ - y))) := by
      filter_upwards [] with y
      have hpe := besselW_peetre s ξ y
      have hKg : (0 : ℝ) ≤ ‖K y‖ * ‖g (ξ - y)‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      rw [hGGeq (ξ - y)]
      calc besselW s ξ * (‖K y‖ * ‖g (ξ - y)‖)
          ≤ (peetreConst s * besselW s (ξ - y) * besselW |s| y) * (‖K y‖ * ‖g (ξ - y)‖) :=
            mul_le_mul_of_nonneg_right hpe hKg
        _ = peetreConst s * (KK y * (besselW s (ξ - y) * ‖g (ξ - y)‖)) := by
            simp only [hKKdef]; ring
    have hstep2 : (∫ y : Space, besselW s ξ * (‖K y‖ * ‖g (ξ - y)‖)) ≤
        ∫ y : Space, peetreConst s * (KK y * GG (ξ - y)) :=
      integral_mono_of_nonneg hzero hmaj_int hle
    have hstep3 : (∫ y : Space, peetreConst s * (KK y * GG (ξ - y))) =
        peetreConst s * scalarConvolution KK GG ξ := by
      rw [integral_const_mul]; rfl
    calc besselW s ξ * ‖scalarConvolution K g ξ‖
        ≤ besselW s ξ * ∫ y : Space, ‖K y‖ * ‖g (ξ - y)‖ := hstep1
      _ = ∫ y : Space, besselW s ξ * (‖K y‖ * ‖g (ξ - y)‖) := hpull
      _ ≤ ∫ y : Space, peetreConst s * (KK y * GG (ξ - y)) := hstep2
      _ = peetreConst s * scalarConvolution KK GG ξ := hstep3
  -- eLpNorm monotonicity through the pointwise bound.
  have hmono :
      eLpNorm (fun ξ : Space => (besselW s ξ : ℝ) • scalarConvolution K g ξ) 2 volume ≤
        eLpNorm (fun ξ : Space => peetreConst s * scalarConvolution KK GG ξ) 2 volume :=
    eLpNorm_mono_ae_real hpt
  -- Pull the constant out of the majorant `eLpNorm`.
  have hfun : (fun ξ : Space => peetreConst s * scalarConvolution KK GG ξ)
      = (peetreConst s • scalarConvolution KK GG) := by
    funext ξ; simp [Pi.smul_apply, smul_eq_mul]
  have hconstsmul :
      eLpNorm (fun ξ : Space => peetreConst s * scalarConvolution KK GG ξ) 2 volume =
        ENNReal.ofReal (peetreConst s) * eLpNorm (scalarConvolution KK GG) 2 volume := by
    rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal (le_of_lt (peetreConst_pos s))]
  -- Young `L¹ ∗ L² → L²`, lifted from the `.toReal` bound to `ℝ≥0∞`.
  have hKK1_ne : eLpNorm KK 1 volume ≠ ⊤ := hMemKK.2.ne
  have hGG2_ne : eLpNorm GG 2 volume ≠ ⊤ := hMemGG.2.ne
  have hConv_ne : eLpNorm (scalarConvolution KK GG) 2 volume ≠ ⊤ := hMemConv.2.ne
  have hYoung : eLpNorm (scalarConvolution KK GG) 2 volume ≤
      eLpNorm KK 1 volume * eLpNorm GG 2 volume := by
    have hyz : eLpNorm KK 1 volume * eLpNorm GG 2 volume ≠ ⊤ :=
      ENNReal.mul_ne_top hKK1_ne hGG2_ne
    rw [← ENNReal.toReal_le_toReal hConv_ne hyz, ENNReal.toReal_mul]
    exact hReal
  -- Kernel mass: `eLpNorm K̃ 1 = ofReal (∫ K̃)`.
  have hKKmass : eLpNorm KK 1 volume = ENNReal.ofReal (∫ ζ : Space, KK ζ) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ofReal_integral_eq_lintegral_ofReal hK (Filter.Eventually.of_forall hKKnonneg)]
    apply lintegral_congr
    intro ζ
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hKKnonneg ζ)]
  -- Assemble.
  calc eLpNorm (fun ξ : Space => (besselW s ξ : ℝ) • scalarConvolution K g ξ) 2 volume
        ≤ eLpNorm (fun ξ : Space => peetreConst s * scalarConvolution KK GG ξ) 2 volume := hmono
    _ = ENNReal.ofReal (peetreConst s) * eLpNorm (scalarConvolution KK GG) 2 volume :=
          hconstsmul
    _ ≤ ENNReal.ofReal (peetreConst s) *
          (eLpNorm KK 1 volume * eLpNorm GG 2 volume) :=
          mul_le_mul' le_rfl hYoung
    _ = ENNReal.ofReal (peetreConst s) *
          (ENNReal.ofReal (∫ ζ : Space, KK ζ) * eLpNorm GG 2 volume) := by
          rw [hKKmass]
    _ = ENNReal.ofReal (peetreConst s * ∫ ζ : Space, KK ζ) * eLpNorm GG 2 volume := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (peetreConst_pos s))]
    _ = ENNReal.ofReal (peetreConst s * ∫ ζ : Space, besselW |s| ζ * ‖K ζ‖)
          * eLpNorm (fun η : Space => (besselW s η : ℝ) • g η) 2 volume := by
          rw [hGGdef, eLpNorm_norm]

/-- The explicit `U-A3` multiplier constant for the cutoff `χ`:
`peetreConst s` times the finite angular-kernel mass (lane 391). -/
def cutoffMultiplierConst (s : ℝ) (χ : Space → ℝ) : ℝ :=
  peetreConst s * ∫ ζ : Space, besselW |s| ζ * ‖angularFourier (fun x => (χ x : ℂ)) ζ‖

theorem cutoffMultiplierConst_nonneg (s : ℝ) (χ : Space → ℝ) :
    0 ≤ cutoffMultiplierConst s χ := by
  refine mul_nonneg (le_of_lt (peetreConst_pos s)) ?_
  refine integral_nonneg ?_
  intro ζ
  exact mul_nonneg (besselW_nonneg _ _) (norm_nonneg _)

/-- **`U-A3` engine specialized to the cutoff transform kernel.**  For the
angular Fourier transform `K = angularFourier χ_ℂ` of a smooth compactly
supported cutoff `χ`, the Bessel-weighted convolution multiplier bound holds
with the constant `cutoffMultiplierConst s χ`.  This is the exact estimate the
`cutoffMultiplier` field consumes once its datum `A` is identified with the
input transform `g` in the angular normalization. -/
theorem eLpNorm_cutoff_multiplier_le {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (s : ℝ) (g : Space → ℂ)
    (hg : MemLp (fun η : Space => (besselW s η : ℝ) • g η) 2 volume) :
    eLpNorm (fun ξ : Space =>
        (besselW s ξ : ℝ) • scalarConvolution (angularFourier (fun x => (χ x : ℂ))) g ξ)
        2 volume ≤
      ENNReal.ofReal (cutoffMultiplierConst s χ) *
        eLpNorm (fun η : Space => (besselW s η : ℝ) • g η) 2 volume := by
  have hK : Integrable
      (fun ζ : Space => besselW |s| ζ * ‖angularFourier (fun x => (χ x : ℂ)) ζ‖) := by
    simpa only [besselW] using integrable_weighted_fourier_cutoff hχ hc s
  simpa only [cutoffMultiplierConst, besselW] using
    eLpNorm_besselWeight_scalarConvolution_le s
      (angularFourier (fun x => (χ x : ℂ))) g hK hg

end NSFormalization.Section3.T22
