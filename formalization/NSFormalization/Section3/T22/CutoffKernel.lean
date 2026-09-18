import NSFormalization.Paper3.AngularFourierDilation
import NSFormalization.Paper3.CompactFourier
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# T22 U-A2 — the Fourier transform of a smooth compact cutoff is weighted-`L¹` (`03-torus.tex:616-624`)

The fixed-cutoff `H^s(ℝ³)` multiplier bound of `cutoffMultiplier`
(`research/T22/Spec.lean:140-144`, unit `U-A3`) realizes the cutoff product as a
Fourier convolution against the transform `𝓕χ` of the cutoff, and closes the
resulting `L¹ ∗ L² → L²` Young estimate with the **finite** kernel mass
`∫ (1+‖ζ‖²)^{|s|/2} · ‖𝓕χ ζ‖`.  This module supplies exactly that finiteness:
for a smooth compactly supported cutoff `χ` and every real order `s`, the
weighted kernel `ζ ↦ (1+‖ζ‖²)^{|s|/2} · ‖𝓕χ ζ‖` is `Integrable`.

The datum layer pairs against the **angular** transform of
`01-introduction.tex:91`, `NSFormalization.Source.angularFourier`, carried by
`angularRealization` / `IsCutoffDatum` (`Spec.lean:99-104`), which multiply the
Schwartz test by `fun x => (χ x : ℂ)`.  The principal statement
`integrable_weighted_fourier_cutoff` is therefore stated for
`angularFourier (fun x => (χ x : ℂ))`; the cycles-convention version for
Mathlib's `𝓕` is `integrable_weighted_fourier_cutoff_mathlib`, and both come
from a single Schwartz-space fact,
`integrable_weighted_schwartz`, applied to two Schwartz representatives of the
same transform (they differ only by the amplitude/dilation
`schwartzAngularDilation`, `Paper3/AngularFourierDilation.lean`).

## Route (`research/T22/T22_SPLIT.md`, unit `U-A2`)

1. `χ` smooth with compact support packages as a Schwartz function
   (`NavierStokesR3.CompactSchwartz.ofCompactSupport`, after the real→complex
   coercion `Complex.ofRealCLM`): `cutoffSchwartz`.
2. The Fourier transform of a Schwartz function is Schwartz
   (`SchwartzMap.fourierTransformCLM`, notation `𝓕` on `SchwartzMap`), and so is
   its normalized angular dilation `schwartzAngularDilation (𝓕 ·)` whose
   coercion is `angularFourier` (`schwartzAngularDilation_fourier_apply`).
3. `integrable_weighted_schwartz`: a Schwartz function `ψ` obeys the uniform
   decay `(1+‖ζ‖)^k · ‖ψ ζ‖ ≤ C_k` for every `k`
   (`SchwartzMap.one_add_le_sup_seminorm_apply` at `n = 0`,
   `norm_iteratedFDeriv_zero`).  Choosing a natural `k > |s| + 3` and using
   `(1+‖ζ‖²)^{|s|/2} ≤ (1+‖ζ‖)^{|s|}` bounds the integrand pointwise by
   `C_k · (1+‖ζ‖)^{-(k-|s|)}`, whose integrability over `EuclideanSpace ℝ (Fin 3)`
   is `MeasureTheory.integrable_one_add_norm` (`finrank = 3 < k - |s|`).
4. `lintegral_weighted_fourier_cutoff_ne_top`: the `ENNReal`/`lintegral` form of
   the same mass (from `Integrable.hasFiniteIntegral`), for the `ℝ≥0∞`-valued
   norm bookkeeping of `U-A3`.

No named input; the whole unit closes from Mathlib and the reused
`Paper3`/vendor Schwartz constructions.
-/

noncomputable section

namespace NSFormalization.Section3.T22

open MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source (angularFourier)
open scoped ContDiff SchwartzMap

/-! ## 1. A Schwartz function is weighted-`L¹` for every polynomial weight -/

/-- **Schwartz weighted integrability.**  For every Schwartz function `ψ` on
`ℝ³` and every real order `s`, the inhomogeneous weight `(1+‖ζ‖²)^{|s|/2}` times
`‖ψ ζ‖` is integrable.  This is the analytic core of `U-A2`: pick a natural
`k > |s| + 3`, dominate the integrand by `C_k · (1+‖ζ‖)^{-(k-|s|)}`, and use
`integrable_one_add_norm` on the `3`-dimensional Japanese-bracket tail. -/
theorem integrable_weighted_schwartz (s : ℝ) (ψ : SchwartzMap Space ℂ) :
    Integrable (fun ζ : Space => (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖ψ ζ‖) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (|s| + 3)
  set C : ℝ := 2 ^ k * (Finset.Iic (k, 0)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ with hC
  -- The polynomial tail is integrable because `finrank ℝ ℝ³ = 3 < k - |s|`.
  have hfr : (Module.finrank ℝ Space : ℝ) < (k : ℝ) - |s| := by
    have h3 : Module.finrank ℝ Space = 3 := by simp [Space]
    rw [h3]; push_cast; linarith
  have hg : Integrable (fun ζ : Space => C * (1 + ‖ζ‖) ^ (-((k : ℝ) - |s|))) :=
    (integrable_one_add_norm hfr).const_mul C
  refine Integrable.mono' hg ?_ ?_
  · exact Continuous.aestronglyMeasurable
      ((Continuous.rpow_const (by fun_prop) (fun _ => Or.inl (by positivity))).mul (by fun_prop))
  · filter_upwards [] with ζ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    set b : ℝ := 1 + ‖ζ‖ with hb
    have hb0 : (0 : ℝ) < b := by rw [hb]; positivity
    -- Weight comparison `(1+‖ζ‖²)^{|s|/2} ≤ (1+‖ζ‖)^{|s|}`.
    have hw : (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) ≤ b ^ |s| := by
      have hbase : (1 + ‖ζ‖ ^ 2) ≤ b ^ 2 := by rw [hb]; nlinarith [norm_nonneg ζ]
      calc (1 + ‖ζ‖ ^ 2) ^ (|s| / 2)
            ≤ (b ^ 2) ^ (|s| / 2) := Real.rpow_le_rpow (by positivity) hbase (by positivity)
        _ = b ^ |s| := by rw [← Real.rpow_natCast b 2, ← Real.rpow_mul hb0.le]; congr 1; ring
    -- Uniform Schwartz decay `(1+‖ζ‖)^k · ‖ψ ζ‖ ≤ C`.
    have hdecay : b ^ (k : ℕ) * ‖ψ ζ‖ ≤ C := by
      have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl ψ ζ
      rw [norm_iteratedFDeriv_zero] at h
      simpa [hb, hC] using h
    have hbk : (0 : ℝ) < b ^ (k : ℕ) := by positivity
    have hψbound : ‖ψ ζ‖ ≤ C * b ^ (-(k : ℝ)) := by
      rw [Real.rpow_neg hb0.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hbk, mul_comm]
      exact hdecay
    have hcomb : b ^ |s| * (C * b ^ (-(k : ℝ))) = C * b ^ (-((k : ℝ) - |s|)) := by
      rw [show (-((k : ℝ) - |s|)) = |s| + -(k : ℝ) by ring, Real.rpow_add hb0]; ring
    calc (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖ψ ζ‖
          ≤ b ^ |s| * (C * b ^ (-(k : ℝ))) :=
            mul_le_mul hw hψbound (norm_nonneg _) (Real.rpow_nonneg hb0.le _)
      _ = C * b ^ (-((k : ℝ) - |s|)) := hcomb

/-! ## 2. The cutoff as a Schwartz function -/

/-- A smooth compactly supported real cutoff `χ`, complexified and packaged as a
Schwartz function.  This is the concrete convolution datum whose transform
`U-A3` uses. -/
def cutoffSchwartz {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    SchwartzMap Space ℂ :=
  NavierStokesR3.CompactSchwartz.ofCompactSupport (fun x => (χ x : ℂ))
    (Complex.ofRealCLM.contDiff.comp hχ)
    (hc.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero)

@[simp] theorem cutoffSchwartz_apply {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (x : Space) :
    cutoffSchwartz hχ hc x = (χ x : ℂ) := rfl

/-! ## 3. Weighted-`L¹` integrability of the cutoff kernel -/

/-- **`U-A2` target (datum-layer angular spelling).**  For a smooth compactly
supported cutoff `χ` and every real order `s`, the weighted angular-Fourier
kernel `ζ ↦ (1+‖ζ‖²)^{|s|/2} · ‖angularFourier χ_ℂ ζ‖` (with `χ_ℂ = (χ · : ℂ)`)
is integrable.  This is the finite kernel mass that `cutoffMultiplier`
(`Spec.lean:140-144`, `U-A3`) feeds into the Young `L¹ ∗ L²` estimate. -/
theorem integrable_weighted_fourier_cutoff {χ : Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (s : ℝ) :
    Integrable (fun ζ : Space =>
      (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖angularFourier (fun x => (χ x : ℂ)) ζ‖) := by
  refine (integrable_weighted_schwartz s
    (schwartzAngularDilation (𝓕 (cutoffSchwartz hχ hc)))).congr ?_
  filter_upwards [] with ζ
  rw [schwartzAngularDilation_fourier_apply]
  rfl

/-- **`U-A2` target (Mathlib cycles convention).**  The same weighted
integrability for Mathlib's Fourier transform `𝓕` of the complexified cutoff.
It differs from `integrable_weighted_fourier_cutoff` only by the amplitude and
frequency dilation relating the two conventions. -/
theorem integrable_weighted_fourier_cutoff_mathlib {χ : Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (s : ℝ) :
    Integrable (fun ζ : Space =>
      (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 (fun x => (χ x : ℂ)) ζ‖) := by
  refine (integrable_weighted_schwartz s (𝓕 (cutoffSchwartz hχ hc))).congr ?_
  filter_upwards [] with ζ
  rw [SchwartzMap.fourier_coe]
  rfl

/-- **`ENNReal`/`lintegral` form** of the angular kernel mass: it is finite.
This is the `ℝ≥0∞`-valued bookkeeping shape `U-A3` uses when bounding
`‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ`. -/
theorem lintegral_weighted_fourier_cutoff_ne_top {χ : Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (s : ℝ) :
    (∫⁻ ζ : Space, ENNReal.ofReal
        ((1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖angularFourier (fun x => (χ x : ℂ)) ζ‖)) ≠ ⊤ := by
  have h := (integrable_weighted_fourier_cutoff hχ hc s).hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => by positivity))] at h
  exact h.ne

end NSFormalization.Section3.T22
