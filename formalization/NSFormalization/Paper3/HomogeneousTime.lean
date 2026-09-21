import NSFormalization.Paper3.CompactPhysicalTime

/-! Uniform low/high-frequency bounds and actual homogeneous negative-order
Fourier time integrability for compact smooth spacetime forces. -/

noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped ContDiff ENNReal

/-- Explicit low/high-frequency control of the actual homogeneous energy.
The low-frequency contribution uses a supremum bound; the high-frequency
contribution uses the actual unweighted squared integral. -/
theorem homogeneous_energy_le_bound_add_L2 {s C : ℝ}
    (hs : -3 / 2 < s) (hs0 : s ≤ 0) {φ : Space → ℂ}
    (hφ : Measurable φ) (hC : 0 ≤ C) (hbound : ∀ ξ, ‖φ ξ‖ ≤ C)
    (hL2 : Integrable (fun ξ => ‖φ ξ‖ ^ 2)) :
    (∫ ξ : Space, ‖ξ‖ ^ (2 * s) * ‖φ ξ‖ ^ 2) ≤
      C ^ 2 * (∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)) +
        ∫ ξ : Space, ‖φ ξ‖ ^ 2 := by
  have hW : IntegrableOn (fun ξ : Space => ‖ξ‖ ^ (2 * s)) (Metric.ball 0 1) := by
    simpa using homogeneous_low_frequency_integrable hs
      (φ := fun _ : Space => (1 : ℂ)) measurable_const (by norm_num : (0 : ℝ) ≤ 1)
      (fun _ => by simp)
  have hWi : Integrable ((Metric.ball (0 : Space) 1).indicator (fun ξ => ‖ξ‖ ^ (2 * s))) :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr hW
  have hmajor : Integrable (fun ξ : Space =>
      C ^ 2 * (Metric.ball (0 : Space) 1).indicator (fun y => ‖y‖ ^ (2 * s)) ξ + ‖φ ξ‖ ^ 2) :=
    (hWi.const_mul _).add hL2
  have hpoint (ξ : Space) : ‖ξ‖ ^ (2 * s) * ‖φ ξ‖ ^ 2 ≤
      C ^ 2 * (Metric.ball (0 : Space) 1).indicator (fun y => ‖y‖ ^ (2 * s)) ξ + ‖φ ξ‖ ^ 2 := by
    by_cases hξ : ξ ∈ Metric.ball (0 : Space) 1
    · rw [Set.indicator_of_mem hξ]
      have hb : ‖φ ξ‖ ^ 2 ≤ C ^ 2 := (sq_le_sq₀ (norm_nonneg _) hC).mpr (hbound ξ)
      nlinarith [Real.rpow_nonneg (norm_nonneg ξ) (2 * s), sq_nonneg ‖φ ξ‖]
    · rw [Set.indicator_of_notMem hξ, mul_zero, zero_add]
      have hn : 1 ≤ ‖ξ‖ := by simpa using hξ
      have hw := Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith : 2 * s ≤ 0)
      nlinarith [sq_nonneg ‖φ ξ‖]
  have hle := integral_mono (homogeneous_negative_integrable hs hs0 hφ hC hbound hL2) hmajor hpoint
  rw [integral_add (hWi.const_mul _) hL2, integral_const_mul,
    integral_indicator Metric.isOpen_ball.measurableSet] at hle
  exact hle

/-- A scalar compact smooth input has its actual homogeneous Fourier norm
bounded solely by its physical L¹ integral and squared L² integral. -/
theorem homogeneousFourierNorm_le_physical {s C₁ C₂ : ℝ}
    (hs : -3 / 2 < s) (hs0 : s ≤ 0) {f : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hC₁ : 0 ≤ C₁)
    (h₁ : (∫ x : Space, ‖f x‖) ≤ C₁)
    (h₂ : (∫ x : Space, ‖f x‖ ^ 2) ≤ C₂) :
    NSFormalization.Source.homogeneousFourierNorm s f ≤
      Real.sqrt (C₁ ^ 2 * (∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)) + C₂) := by
  let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport f hf hc
  have hb (ξ : Space) : ‖𝓕 φ ξ‖ ≤ C₁ := by
    have h := SchwartzMap.norm_fourier_apply_le_toLp_one φ ξ
    rw [SchwartzMap.norm_toLp_one] at h
    exact h.trans h₁
  have hi : Integrable (fun ξ : Space => ‖𝓕 φ ξ‖ ^ 2) :=
    ((𝓕 φ).memLp 2 volume).integrable_norm_pow (by norm_num)
  have hle := homogeneous_energy_le_bound_add_L2 hs hs0 (𝓕 φ).continuous.measurable hC₁ hb hi
  rw [SchwartzMap.integral_norm_sq_fourier] at hle
  exact Real.sqrt_le_sqrt (hle.trans (add_le_add_right h₂ _))

/-- A nonpositive inhomogeneous Fourier norm is bounded by the physical L²
integral. The bound is uniform over any additional parameters in the input. -/
theorem fourierSobolevNorm_le_physical {s C : ℝ} (hs : s ≤ 0)
    {f : Space → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (h₂ : (∫ x : Space, ‖f x‖ ^ 2) ≤ C) :
    NSFormalization.Source.fourierSobolevNorm s f ≤ Real.sqrt C := by
  let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport f hf hc
  have hi := integral_besselIntegrand_mono hs (𝓕 φ).continuous
    (compact_fourier_bessel_integrable 0 f hf hc)
  simp only [besselIntegrand, Real.rpow_zero, one_mul] at hi
  have hp : (∫ ξ : Space, ‖𝓕 f ξ‖ ^ 2) = ∫ x : Space, ‖f x‖ ^ 2 :=
    SchwartzMap.integral_norm_sq_fourier φ
  rw [hp] at hi
  exact Real.sqrt_le_sqrt (hi.trans h₂)

/-- Compact smooth spacetime inputs have a uniformly bounded actual
homogeneous Fourier norm in the valid negative-order range. -/
theorem uniform_homogeneousFourier_time {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    {F : ℝ × Space → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ∃ C : ℝ, ∀ t, ‖NSFormalization.Source.homogeneousFourierNorm s (fun x => F (t, x))‖ ≤ C := by
  obtain ⟨C₁, hC₁, h₁⟩ := uniform_integral_norm_pow_time hF.continuous hc 1 (by norm_num)
  obtain ⟨C₂, hC₂, h₂⟩ := uniform_integral_norm_pow_time hF.continuous hc 2 (by norm_num)
  refine ⟨Real.sqrt (C₁ ^ 2 * (∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)) + C₂), ?_⟩
  intro t
  let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport (fun x => F (t, x))
    (hF.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice hc t)
  have hb (ξ : Space) : ‖𝓕 φ ξ‖ ≤ C₁ := by
    have h := SchwartzMap.norm_fourier_apply_le_toLp_one φ ξ
    rw [SchwartzMap.norm_toLp_one] at h
    exact h.trans (by simpa [φ] using h₁ t)
  have hi : Integrable (fun ξ : Space => ‖𝓕 φ ξ‖ ^ 2) :=
    ((𝓕 φ).memLp 2 volume).integrable_norm_pow (by norm_num)
  have hle := homogeneous_energy_le_bound_add_L2 hs hs0 (𝓕 φ).continuous.measurable hC₁ hb hi
  rw [SchwartzMap.integral_norm_sq_fourier] at hle
  have hfinal : (∫ ξ : Space, ‖ξ‖ ^ (2 * s) * ‖𝓕 φ ξ‖ ^ 2) ≤
      C₁ ^ 2 * (∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)) + C₂ :=
    hle.trans (by simpa [φ] using add_le_add_right (h₂ t) (C₁ ^ 2 * (∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s))))
  unfold NSFormalization.Source.homogeneousFourierNorm
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt hfinal

/-- This discharges the actual homogeneous time `L^q` condition for compact
smooth inputs, for every exponent including `q=1`, `q=2`, and infinity. -/
theorem memLp_homogeneousFourier_time {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    {F : ℝ × Space → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ≥0∞) :
    MemLp (fun t => NSFormalization.Source.homogeneousFourierNorm s (fun x => F (t, x))) q volume := by
  obtain ⟨C, hC⟩ := uniform_homogeneousFourier_time hs hs0 hF hc
  exact (compact_homogeneousFourier_time s hc).memLp_of_bound
    (stronglyMeasurable_homogeneousFourier_time s hF.continuous).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

end NSFormalization.Paper3
