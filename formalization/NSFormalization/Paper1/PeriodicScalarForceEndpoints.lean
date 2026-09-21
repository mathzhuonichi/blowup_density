import NSFormalization.Paper1.LocalizationBoundary
import NSFormalization.Source.AngularGradientIdentity

/-!
# Actual scalar force endpoints under periodization

The spatial support sits strictly inside one fundamental cube. Its actual
periodic H¹ energy is consequently the physical whole-space H¹ energy, which
equals the unitary angular Fourier energy. The cycles-frequency Bessel norm
used by the shared scaling library differs by at most `2 * pi` at order one.
All derivative integrability is derived from compact smoothness.

Source anchors: Paper 1, Lemma `localization` at order one and Proposition
`scaling`; the existing OpenAI periodization maps in `PeriodicBridge`;
`Source.AngularGradientIdentity.angular_succ_energy` and the Fourier
convention comparison in `Source.FourierConvention`.
-/

noncomputable section
namespace NSFormalization.Paper1.PeriodicScalarForceEndpoints

open Set MeasureTheory NavierStokes.ProblemStatement
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open NavierStokesR3.HarmonicTestFunctionals
open NSFormalization.Source NSFormalization.Paper3
open NSFormalization.Paper1.PeriodicBridge
open NSFormalization.Paper1.LocalizationBoundary
open scoped ContDiff FourierTransform ENNReal

theorem angularSobolevSq_zero_eq_physical (φ : SchwartzMap Space ℂ) :
    angularSobolevSq 0 (φ : Space → ℂ) = ∫ x : Space, ‖φ x‖ ^ 2 := by
  rw [angularSobolevSq_eq_frequency_weight]
  simpa only [Real.rpow_zero, one_mul, SchwartzMap.fourier_coe] using
    SchwartzMap.integral_norm_sq_fourier φ

/-- The exact physical first-derivative identity, using the already proved
unitary angular Fourier derivative rule. -/
theorem angularSobolevSq_one_eq_physical
    {f : Space → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    angularSobolevSq 1 f =
      (∫ x : Space, ‖f x‖ ^ 2) +
        ∑ i : Fin 3, ∫ x : Space, ‖spatialPartial i f x‖ ^ 2 := by
  let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport f hf hc
  have h := angular_succ_energy 0 φ
  simp only [zero_add, angularSobolevSq_zero_eq_physical] at h
  exact h

/-- Exact scalar H¹ energy preservation for a single compact supported copy.
No integrability of the derivatives is supplied as an extra premise. -/
theorem periodicSobolevSq_one_periodize
    {r : ℝ} {F : SpaceTime → ℂ} (hS : SupportedInCube r F)
    (hr : r < 1 / 2) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (t : ℝ) :
    periodicSobolevSq 1 (fun x => periodize F (t, x)) =
      angularSobolevSq 1 (fun x => F (t, x)) := by
  let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport (fun x => F (t, x))
    (hF.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice hc t)
  have h0 : Integrable (fun x : Space => ‖F (t, x)‖ ^ 2) :=
    (φ.memLp 2 volume).integrable_norm_pow (by norm_num)
  have h1 (i : Fin 3) : Integrable
      (fun x : Space => ‖spatialPartial i (fun y => F (t, y)) x‖ ^ 2) :=
    ((partialCLM i φ).memLp 2 volume).integrable_norm_pow (by norm_num)
  have hreg : ContDiff ℝ 1 (fun x : Space => periodize F (t, x)) :=
    ((contDiff_periodize hS hF).comp
      (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hp : UnitPeriods (fun x : Space => periodize F (t, x)) := by
    intro x i
    exact unitSpatialPeriodsOn_periodize F univ t (mem_univ _) x i
  rw [periodicSobolevSq_one hreg hp,
    angularSobolevSq_one_eq_physical (f := fun x => F (t, x))
      (hF.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice hc t),
    periodicH1Energy, cubeIntegral_periodize_norm_sq hS hr h0]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have heq (x : Space) := congrFun (spatialPartial_periodize_complex hS hr i) (t, x)
  simp_rw [heq]
  exact cubeIntegral_periodize_norm_sq (supported_spatialPartial_complex hS i) hr (h1 i)

/-- Actual periodic H¹ is bounded by the cycles-frequency whole-space Bessel
H¹ norm with the explicit normalization constant `2 * pi`. -/
theorem periodicSobolevNorm_one_periodize_le
    {r : ℝ} {F : SpaceTime → ℂ} (hS : SupportedInCube r F)
    (hr : r < 1 / 2) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (t : ℝ) :
    periodicSobolevNorm 1 (fun x => periodize F (t, x)) ≤
      (2 * Real.pi) * fourierSobolevNorm 1 (fun x => F (t, x)) := by
  have he := (angularSobolevNorm_equivalence 1 (fun x => F (t, x))
    (compact_spacetime_fourier_slice_continuous hF hc t)
    (compact_spacetime_bessel_slices 1 hF hc t)).1
  rw [periodicSobolevNorm, periodicSobolevSq_one_periodize hS hr hF hc t]
  simpa only [abs_one, Real.rpow_one, frequencyUnit, angularSobolevNorm] using he

/-- Endpoint time seminorm transfer, valid for any time measure and exponent.
In particular it supplies the required `L¹_t H¹_x` comparison. -/
theorem eLpNorm_periodized_one_le
    {r : ℝ} {F : SpaceTime → ℂ} (hS : SupportedInCube r F)
    (hr : r < 1 / 2) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (q : ℝ≥0∞) (μ : Measure ℝ) :
    eLpNorm (fun t => periodicSobolevNorm 1 (fun x => periodize F (t, x))) q μ ≤
      ENNReal.ofReal (2 * Real.pi) *
        eLpNorm (fun t => fourierSobolevNorm 1 (fun x => F (t, x))) q μ := by
  have h := eLpNorm_mono_real (p := q) (μ := μ)
    (f := fun t => periodicSobolevNorm 1 (fun x => periodize F (t, x)))
    (g := fun t => (2 * Real.pi) * fourierSobolevNorm 1 (fun x => F (t, x)))
    (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (show 0 ≤ periodicSobolevNorm 1 (fun x => periodize F (t, x)) from
          Real.sqrt_nonneg _)]
      exact periodicSobolevNorm_one_periodize_le hS hr hF hc t)
  refine h.trans_eq ?_
  change eLpNorm ((2 * Real.pi) •
    (fun t => fourierSobolevNorm 1 (fun x => F (t, x)))) q μ = _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]

/-- The actual zero-order endpoint profile is continuous on the whole time
axis, by single-copy energy preservation and compact parameter integration. -/
theorem continuous_periodized_zero_time
    {r : ℝ} {F : SpaceTime → ℂ} (hS : SupportedInCube r F)
    (hr : r < 1 / 2) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    Continuous (fun t => periodicSobolevNorm 0 (fun x => periodize F (t, x))) := by
  have he (t : ℝ) : periodicSobolevNorm 0 (fun x => periodize F (t, x)) =
      Real.sqrt (∫ x : Space, ‖F (t, x)‖ ^ 2) := by
    let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport (fun x => F (t, x))
      (hF.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice hc t)
    have hi : Integrable (fun x : Space => ‖F (t, x)‖ ^ 2) :=
      (φ.memLp 2 volume).integrable_norm_pow (by norm_num)
    unfold periodicSobolevNorm
    congr 1
    have hcont : Continuous (fun x : Space => periodize F (t, x)) :=
      (contDiff_periodize hS hF).continuous.comp
        (continuous_const.prodMk continuous_id)
    rw [periodicSobolevSq_zero hcont,
      cubeIntegral_periodize_norm_sq hS hr hi]
  simp_rw [he]
  exact Real.continuous_sqrt.comp
    (continuous_integral_norm_pow_time hF.continuous hc 2 (by norm_num))

/-- The actual H¹ endpoint profile is continuous. Its three derivative
energies come from the smooth compact spacetime derivatives of the original
force; no derivative profile measurability is assumed. -/
theorem continuous_periodized_one_time
    {r : ℝ} {F : SpaceTime → ℂ} (hS : SupportedInCube r F)
    (hr : r < 1 / 2) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    Continuous (fun t => periodicSobolevNorm 1 (fun x => periodize F (t, x))) := by
  have he (t : ℝ) : periodicSobolevNorm 1 (fun x => periodize F (t, x)) =
      Real.sqrt ((∫ x : Space, ‖F (t, x)‖ ^ 2) +
        ∑ i : Fin 3, ∫ x : Space, ‖spacetimePartial i F (t, x)‖ ^ 2) := by
    rw [periodicSobolevNorm, periodicSobolevSq_one_periodize hS hr hF hc t,
      angularSobolevSq_one_eq_physical (f := fun x => F (t, x))
        (hF.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice hc t)]
    simp_rw [spacetimePartial_eq_slice hF]
  simp_rw [he]
  apply Real.continuous_sqrt.comp
  exact (continuous_integral_norm_pow_time hF.continuous hc 2 (by norm_num)).add
    (continuous_finset_sum Finset.univ (fun i _ =>
      continuous_integral_norm_pow_time (spacetimePartial_smooth hF i).continuous
        (spacetimePartial_compact hc i) 2 (by norm_num)))

end NSFormalization.Paper1.PeriodicScalarForceEndpoints
