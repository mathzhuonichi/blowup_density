import NSFormalization.Paper1.PeriodicSobolevHilbert
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Temporal interpolation for actual periodic force norms

The spatial Fourier interpolation theorem and Hölder's inequality give an
`L¹_t H^s_x` estimate from the two actual `L¹_t H⁰_x` and `L¹_t H¹_x`
endpoint norms. This step preserves the common time integral and therefore
the packet scaling exponent. It does not require a fractional localization
comparison as an additional premise.

Source anchors:
* `final/paper_1_theory.tex`, Proposition `scaling`, equation `packetHs`.
* `PeriodicSobolevHilbert.periodicSobolevNorm_interpolation` supplies the
  actual Fourier endpoint interpolation.
* Mathlib `ENNReal.lintegral_mul_norm_pow_le` supplies weighted Hölder.
-/

noncomputable section

namespace NSFormalization.Paper1.PeriodicForceTimeInterpolation

open MeasureTheory NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal

/-- On a nonnegative real profile the `L¹` seminorm is its nonnegative
integral. No integrability hypothesis or conversion of infinity to zero is
used. -/
theorem eLpNorm_one_eq_lintegral_ofReal_of_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : ∀ t, 0 ≤ f t) :
    eLpNorm f 1 μ = ∫⁻ t, ENNReal.ofReal (f t) ∂μ := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  apply lintegral_congr
  intro t
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hf t)]

/-- Weighted Hölder for nonnegative real time profiles, including finite or
infinite endpoint norms. The exponent range is closed so this also provides
the two immediate endpoint cases. -/
theorem eLpNorm_mul_rpow_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A B : α → ℝ} (hA : AEMeasurable A μ) (hB : AEMeasurable B μ)
    (hA0 : ∀ t, 0 ≤ A t) (hB0 : ∀ t, 0 ≤ B t)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    eLpNorm (fun t => A t ^ (1 - s) * B t ^ s) 1 μ ≤
      eLpNorm A 1 μ ^ (1 - s) * eLpNorm B 1 μ ^ s := by
  have hns : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  rw [eLpNorm_one_eq_lintegral_ofReal_of_nonneg
    (fun t => mul_nonneg (Real.rpow_nonneg (hA0 t) _)
      (Real.rpow_nonneg (hB0 t) _)),
    eLpNorm_one_eq_lintegral_ofReal_of_nonneg hA0,
    eLpNorm_one_eq_lintegral_ofReal_of_nonneg hB0]
  simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg (hA0 _) _),
    ← ENNReal.ofReal_rpow_of_nonneg (hA0 _) hns,
    ← ENNReal.ofReal_rpow_of_nonneg (hB0 _) hs0]
  exact ENNReal.lintegral_mul_norm_pow_le hA.ennreal_ofReal
    hB.ennreal_ofReal hns hs0 (by ring)

/-- Integrate a pointwise interpolation inequality before taking the
concentrating-parameter limit. Only the endpoint profiles need to be
measurable; their norms remain `ENNReal` throughout. -/
theorem eLpNorm_le_endpoint_interpolation
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A B Z : α → ℝ} (hA : AEMeasurable A μ) (hB : AEMeasurable B μ)
    (hA0 : ∀ t, 0 ≤ A t) (hB0 : ∀ t, 0 ≤ B t) (hZ0 : ∀ t, 0 ≤ Z t)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hpoint : ∀ t, Z t ≤ A t ^ (1 - s) * B t ^ s) :
    eLpNorm Z 1 μ ≤ eLpNorm A 1 μ ^ (1 - s) * eLpNorm B 1 μ ^ s := by
  refine (eLpNorm_mono_real (fun t => ?_)).trans
    (eLpNorm_mul_rpow_le hA hB hA0 hB0 hs0 hs1)
  rw [Real.norm_eq_abs, abs_of_nonneg (hZ0 t)]
  exact hpoint t

/-- Actual periodic `L¹_t H^s_x` interpolation for a scalar force. Both
endpoint norms are the Fourier norms of the same field. The hypotheses are
spatial `C¹` regularity, spatial periodicity, and endpoint time measurability;
no periodization comparison or critical embedding is assumed. The measure
parameter allows positive time, a finite time interval, or all time. -/
theorem periodic_force_L1_interpolation
    {F : ℝ → Space → ℂ} {μ : Measure ℝ}
    (hF : ∀ t, ContDiff ℝ 1 (F t)) (hp : ∀ t, UnitPeriods (F t))
    (hm0 : AEMeasurable (fun t => periodicSobolevNorm 0 (F t)) μ)
    (hm1 : AEMeasurable (fun t => periodicSobolevNorm 1 (F t)) μ)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    eLpNorm (fun t => periodicSobolevNorm s (F t)) 1 μ ≤
      eLpNorm (fun t => periodicSobolevNorm 0 (F t)) 1 μ ^ (1 - s) *
        eLpNorm (fun t => periodicSobolevNorm 1 (F t)) 1 μ ^ s := by
  refine eLpNorm_le_endpoint_interpolation hm0 hm1
    (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
    (fun _ => Real.sqrt_nonneg _) hs0 hs1 ?_
  intro t
  have h := periodicSobolevNorm_interpolation (hF t) (hp t) hs0 hs1
  simpa only [periodicSobolevNorm, periodicSobolevSq_zero (hF t).continuous,
    periodicSobolevSq_one (hF t) (hp t)] using h

end NSFormalization.Paper1.PeriodicForceTimeInterpolation
