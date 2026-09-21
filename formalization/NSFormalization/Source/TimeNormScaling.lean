import NSFormalization.Source.FourierScaling
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Actual time norms of parabolically concentrated forces

Time is integrated over all of `ℝ`, so the estimates include the portion of the
force after the insertion time. Restriction to positive time only decreases
these norms. The spatial norm is the square root of the explicit Fourier
integral in `FourierScaling`, and time uses Mathlib's `eLpNorm`.
-/

noncomputable section
namespace NSFormalization.Source
open NavierStokes.ProblemStatement MeasureTheory
open Filter Topology
open scoped ENNReal FourierTransform

theorem eLpNorm_parabolic_time (g : ℝ → ℝ) (hg : StronglyMeasurable g)
    (q : ℝ≥0∞) {k : ℝ} (hk : 0 < k) (t₀ : ℝ) :
    eLpNorm (fun t => g (k ^ 2 * (t - t₀))) q volume =
      ENNReal.ofReal (k ^ (-2 / q.toReal)) * eLpNorm g q volume := by
  have hmap : Measure.map (fun t : ℝ => k ^ 2 * (t - t₀)) volume =
      ENNReal.ofReal ((k ^ 2)⁻¹) • volume := by
    rw [show (fun t : ℝ => k ^ 2 * (t - t₀)) =
      (fun t : ℝ => k ^ 2 * t) ∘ (fun t : ℝ => t - t₀) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop),
      (measurePreserving_sub_right volume t₀).map_eq,
      Real.map_volume_mul_left (pow_ne_zero 2 hk.ne'),
      abs_of_pos (inv_pos.mpr (pow_pos hk 2))]
  have hm : Measurable (fun t : ℝ => k ^ 2 * (t - t₀)) := by fun_prop
  change eLpNorm (g ∘ (fun t : ℝ => k ^ 2 * (t - t₀))) q volume = _
  rw [← eLpNorm_map_measure (μ := volume) (p := q)
    hg.aestronglyMeasurable hm.aemeasurable, hmap,
    eLpNorm_smul_measure_of_ne_zero (by positivity)]
  congr 1
  rw [ENNReal.ofReal_rpow_of_pos (inv_pos.mpr (pow_pos hk 2))]
  congr 1
  rw [Real.inv_rpow (sq_nonneg k), ← Real.rpow_natCast, ← Real.rpow_mul hk.le,
    ← Real.rpow_neg hk.le]
  congr 1
  norm_num [ENNReal.toReal_div]
  ring

theorem eLpNorm_parabolic_majorant {a k : ℝ} (hk : 0 < k) (t₀ : ℝ)
    (q : ℝ≥0∞) (f g : ℝ → ℝ) (hg : StronglyMeasurable g)
    (hbound : ∀ t, ‖f t‖ ≤ k ^ a * g (k ^ 2 * (t - t₀))) :
    eLpNorm f q volume ≤
      ENNReal.ofReal (k ^ (a - 2 / q.toReal)) * eLpNorm g q volume := by
  have h := eLpNorm_mono_real (p := q) (μ := volume) hbound
  have he : (fun t => k ^ a * g (k ^ 2 * (t - t₀))) =
      k ^ a • (fun t => g (k ^ 2 * (t - t₀))) := rfl
  rw [he, eLpNorm_const_smul, eLpNorm_parabolic_time g hg q hk t₀] at h
  have hc : ‖k ^ a‖ₑ * ENNReal.ofReal (k ^ (-2 / q.toReal)) =
      ENNReal.ofReal (k ^ (a - 2 / q.toReal)) := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.rpow_pos_of_pos hk a),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hk.le a), ← Real.rpow_add hk]
    congr 2
    ring
  simpa only [← mul_assoc, hc] using h

def parabolicComplexForce (k t₀ : ℝ) (f : ℝ → Space → ℂ) : ℝ → Space → ℂ :=
  fun t => concentratedForce k (f (k ^ 2 * (t - t₀)))

def fourierSobolevNorm (s : ℝ) (f : Space → ℂ) : ℝ :=
  Real.sqrt (fourierSobolevSq s f)

def homogeneousFourierNorm (s : ℝ) (f : Space → ℂ) : ℝ :=
  Real.sqrt (∫ ξ : Space, ‖ξ‖ ^ (2 * s) * ‖𝓕 f ξ‖ ^ 2)

theorem sqrt_rpow_energy {k : ℝ} (hk : 0 < k) (s E : ℝ) :
    Real.sqrt (k ^ (3 + 2 * s) * E) =
      k ^ (3 / 2 + s) * Real.sqrt E := by
  rw [Real.sqrt_mul (Real.rpow_nonneg hk.le _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul hk.le]
  congr 2
  ring

/-- The positive-order estimate has the actual exponent
`3/2 + s - 2/q`, valid also for the time essential supremum. -/
theorem force_eLpNorm_positive {s k : ℝ} (hs : 0 ≤ s) (hk : 1 ≤ k)
    (t₀ : ℝ) (q : ℝ≥0∞) (f : ℝ → Space → ℂ)
    (hF : ∀ t, Continuous (𝓕 (f t)))
    (hint : ∀ t, Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 (f t) ξ‖ ^ 2))
    (ht : StronglyMeasurable (fun t => fourierSobolevNorm s (f t))) :
    eLpNorm (fun t => fourierSobolevNorm s (parabolicComplexForce k t₀ f t)) q volume ≤
      ENNReal.ofReal (k ^ (3 / 2 + s - 2 / q.toReal)) *
        eLpNorm (fun t => fourierSobolevNorm s (f t)) q volume := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  apply eLpNorm_parabolic_majorant hk0 t₀ q _ _ ht
  intro t
  unfold fourierSobolevNorm parabolicComplexForce
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.sqrt_le_sqrt
    (fourierSobolevSq_concentrated_le_positive hs hk _ (hF _) (hint _))).trans_eq
      (sqrt_rpow_energy hk0 s _)

/-- The negative-order bound uses the genuine homogeneous profile norm. Its
finiteness for compact smooth fields in `-3/2 < s ≤ 0` is a separate proved
spatial theorem, and temporal integrability remains explicit. -/
theorem force_eLpNorm_negative {s k : ℝ} (hs : s ≤ 0) (hk : 0 < k)
    (t₀ : ℝ) (q : ℝ≥0∞) (f : ℝ → Space → ℂ)
    (hF : ∀ t, Continuous (𝓕 (f t)))
    (hint : ∀ t, Integrable (fun ξ : Space => ‖ξ‖ ^ (2 * s) * ‖𝓕 (f t) ξ‖ ^ 2))
    (ht : StronglyMeasurable (fun t => homogeneousFourierNorm s (f t))) :
    eLpNorm (fun t => fourierSobolevNorm s (parabolicComplexForce k t₀ f t)) q volume ≤
      ENNReal.ofReal (k ^ (3 / 2 + s - 2 / q.toReal)) *
        eLpNorm (fun t => homogeneousFourierNorm s (f t)) q volume := by
  apply eLpNorm_parabolic_majorant hk t₀ q _ _ ht
  intro t
  unfold fourierSobolevNorm parabolicComplexForce homogeneousFourierNorm
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.sqrt_le_sqrt
    (fourierSobolevSq_concentrated_le_negative hs hk _ (hF _) (hint _))).trans_eq
      (sqrt_rpow_energy hk s _)

theorem force_eLpNorm_positive_epsilon {s ε : ℝ} (hs : 0 ≤ s)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (t₀ : ℝ) (q : ℝ≥0∞) (f : ℝ → Space → ℂ)
    (hF : ∀ t, Continuous (𝓕 (f t)))
    (hint : ∀ t, Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 (f t) ξ‖ ^ 2))
    (ht : StronglyMeasurable (fun t => fourierSobolevNorm s (f t))) :
    eLpNorm (fun t => fourierSobolevNorm s (parabolicComplexForce ε⁻¹ t₀ f t)) q volume ≤
      ENNReal.ofReal (ε ^ (2 / q.toReal - 3 / 2 - s)) *
        eLpNorm (fun t => fourierSobolevNorm s (f t)) q volume := by
  have h := force_eLpNorm_positive hs ((one_le_inv₀ hε).mpr hε1) t₀ q f hF hint ht
  have he : (ε⁻¹) ^ (3 / 2 + s - 2 / q.toReal) =
      ε ^ (2 / q.toReal - 3 / 2 - s) := by
    rw [Real.inv_rpow hε.le, ← Real.rpow_neg hε.le]
    congr 1
    ring
  simpa only [he] using h

theorem force_eLpNorm_negative_epsilon {s ε : ℝ} (hs : s ≤ 0)
    (hε : 0 < ε) (t₀ : ℝ) (q : ℝ≥0∞) (f : ℝ → Space → ℂ)
    (hF : ∀ t, Continuous (𝓕 (f t)))
    (hint : ∀ t, Integrable (fun ξ : Space => ‖ξ‖ ^ (2 * s) * ‖𝓕 (f t) ξ‖ ^ 2))
    (ht : StronglyMeasurable (fun t => homogeneousFourierNorm s (f t))) :
    eLpNorm (fun t => fourierSobolevNorm s (parabolicComplexForce ε⁻¹ t₀ f t)) q volume ≤
      ENNReal.ofReal (ε ^ (2 / q.toReal - 3 / 2 - s)) *
        eLpNorm (fun t => homogeneousFourierNorm s (f t)) q volume := by
  have h := force_eLpNorm_negative hs (inv_pos.mpr hε) t₀ q f hF hint ht
  have he : (ε⁻¹) ^ (3 / 2 + s - 2 / q.toReal) =
      ε ^ (2 / q.toReal - 3 / 2 - s) := by
    rw [Real.inv_rpow hε.le, ← Real.rpow_neg hε.le]
    congr 1
    ring
  simpa only [he] using h

/-- Finite profile norms turn a proved scaling inequality into convergence
of the actual extended-valued time norm. -/
theorem ennreal_tendsto_zero_of_power_bound {β : ℝ} (hβ : 0 < β)
    {C : ℝ≥0∞} (hC : C ≠ ∞) {N : ℝ → ℝ≥0∞}
    (hbound : ∀ ε, 0 < ε → ε ≤ 1 → N ε ≤ ENNReal.ofReal (ε ^ β) * C) :
    Tendsto N (𝓝[>] 0) (𝓝 0) := by
  have hr : Tendsto (fun ε : ℝ => ε ^ β) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id.rpow_const_nhds_zero hβ).mono_left nhdsWithin_le_nhds
  have he := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hr) (Or.inr hC)
  simp only [ENNReal.ofReal_zero, zero_mul] at he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with ε hε hε1
    exact hbound ε hε hε1.le

/-- Positive-order subcritical convergence of the actual time norm. The
insertion center may depend arbitrarily on epsilon. -/
theorem force_positive_tendsto_zero {s : ℝ} (hs : 0 ≤ s)
    (q : ℝ≥0∞) (hsub : s < 2 / q.toReal - 3 / 2)
    (center : ℝ → ℝ) (f : ℝ → Space → ℂ)
    (hF : ∀ t, Continuous (𝓕 (f t)))
    (hint : ∀ t, Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 (f t) ξ‖ ^ 2))
    (ht : StronglyMeasurable (fun t => fourierSobolevNorm s (f t)))
    (hfinite : eLpNorm (fun t => fourierSobolevNorm s (f t)) q volume ≠ ∞) :
    Tendsto (fun ε : ℝ => eLpNorm (fun t =>
      fourierSobolevNorm s (parabolicComplexForce ε⁻¹ (center ε) f t)) q volume)
      (𝓝[>] 0) (𝓝 0) := by
  apply ennreal_tendsto_zero_of_power_bound (sub_pos.mpr hsub) hfinite
  intro ε hε hε1
  exact force_eLpNorm_positive_epsilon hs hε hε1 (center ε) q f hF hint ht

/-- Negative-order subcritical convergence, using a finite homogeneous
profile norm within its valid low-frequency range. -/
theorem force_negative_tendsto_zero {s : ℝ} (hs : s ≤ 0)
    (q : ℝ≥0∞) (hsub : s < 2 / q.toReal - 3 / 2)
    (center : ℝ → ℝ) (f : ℝ → Space → ℂ)
    (hF : ∀ t, Continuous (𝓕 (f t)))
    (hint : ∀ t, Integrable (fun ξ : Space => ‖ξ‖ ^ (2 * s) * ‖𝓕 (f t) ξ‖ ^ 2))
    (ht : StronglyMeasurable (fun t => homogeneousFourierNorm s (f t)))
    (hfinite : eLpNorm (fun t => homogeneousFourierNorm s (f t)) q volume ≠ ∞) :
    Tendsto (fun ε : ℝ => eLpNorm (fun t =>
      fourierSobolevNorm s (parabolicComplexForce ε⁻¹ (center ε) f t)) q volume)
      (𝓝[>] 0) (𝓝 0) := by
  apply ennreal_tendsto_zero_of_power_bound (sub_pos.mpr hsub) hfinite
  intro ε hε _
  exact force_eLpNorm_negative_epsilon hs hε (center ε) q f hF hint ht

end NSFormalization.Source
