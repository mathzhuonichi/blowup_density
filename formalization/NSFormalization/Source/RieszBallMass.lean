import NSFormalization.Source.RieszPotentialNearField
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Layercake

/-! # Genuine near-field Riesz control from all centered ball masses -/
noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace NSFormalization.RieszBallMass
abbrev Space := NSFormalization.RieszPotentialNearField.Space

/-- The elementary singular primitive is evaluated only above a positive radius. -/
theorem radial_primitive {a ρ R : ℝ} (ha : a < 3) (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    ρ ^ (a - 3) = R ^ (a - 3) + (3 - a) * ∫ r in ρ..R, r ^ (a - 4) := by
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [uIcc_of_le hρR]
    exact fun h => (not_le_of_gt hρ) h.1⟩)]
  rw [show a - 4 + 1 = a - 3 by ring]
  field_simp [show a - 3 ≠ 0 by linarith]
  ring

/-- Tonelli's radial layer identity; no finiteness assumption is needed. -/
theorem radial_layer_tonelli (R : ℝ) {H : Space → ℝ≥0∞} (hH : Measurable H)
    {q : ℝ → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ y in Metric.ball (0 : Space) R, (∫⁻ r in Ioo ‖y‖ R, q r) * H y) =
      ∫⁻ r in Ioo 0 R, q r * ∫⁻ y in Metric.ball (0 : Space) r, H y := by
  let F : Space → ℝ → ℝ≥0∞ := fun y r =>
    (Ioi ‖y‖).indicator (fun r => q r * H y) r
  have hF : Measurable (Function.uncurry F) := by
    change Measurable ({p : Space × ℝ | ‖p.1‖ < p.2}.indicator
      (fun p => q p.2 * H p.1))
    exact ((hq.comp measurable_snd).mul (hH.comp measurable_fst)).indicator
      (measurableSet_lt (measurable_fst.norm) measurable_snd)
  have hleft (y : Space) :
      (∫⁻ r in Ioo 0 R, F y r) = (∫⁻ r in Ioo ‖y‖ R, q r) * H y := by
    rw [show (fun r => F y r) = (Ioi ‖y‖).indicator (fun r => q r * H y) by rfl,
      setLIntegral_indicator measurableSet_Ioi]
    have hs : Ioi ‖y‖ ∩ Ioo 0 R = Ioo ‖y‖ R := by
      ext r
      simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
      constructor
      · tauto
      · intro hr
        exact ⟨hr.1, lt_of_le_of_lt (norm_nonneg _) hr.1, hr.2⟩
    rw [hs, lintegral_mul_const _ hq]
  simp_rw [← hleft]
  rw [lintegral_lintegral_swap hF.aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro r hr
  have he : (fun y => F y r) =
      (Metric.ball (0 : Space) r).indicator (fun y => q r * H y) := by
    funext y
    by_cases hy : ‖y‖ < r <;> simp [F, hy, Metric.mem_ball]
  dsimp only
  rw [he, setLIntegral_indicator measurableSet_ball,
    inter_eq_left.mpr (Metric.ball_subset_ball hr.2.le), lintegral_const_mul _ hH]

/-- The positive-radius primitive expressed as a nonnegative extended integral. -/
theorem radial_primitive_lintegral {a ρ R : ℝ} (ha : a < 3) (hρ : 0 < ρ)
    (hρR : ρ ≤ R) :
    ENNReal.ofReal (ρ ^ (a - 3)) = ENNReal.ofReal (R ^ (a - 3)) +
      ENNReal.ofReal (3 - a) * ∫⁻ r in Ioo ρ R, ENNReal.ofReal (r ^ (a - 4)) := by
  have hi : IntervalIntegrable (fun r : ℝ => r ^ (a - 4)) volume ρ R := by
    apply intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)
    rw [uIcc_of_le hρR]
    exact fun h => (not_le_of_gt hρ) h.1
  have hn : 0 ≤ᵐ[volume.restrict (Ioc ρ R)] (fun r : ℝ => r ^ (a - 4)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    exact Real.rpow_nonneg (le_of_lt (hρ.trans hr.1)) _
  have he := ofReal_integral_eq_lintegral_ofReal hi.1 hn
  rw [← restrict_Ioo_eq_restrict_Ioc] at he
  rw [← he, restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hρR]
  rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ 3 - a),
    ← ENNReal.ofReal_add (Real.rpow_nonneg (hρ.trans_le hρR).le _) (by
      apply mul_nonneg (by linarith)
      exact intervalIntegral.integral_nonneg hρR (fun r hr =>
        Real.rpow_nonneg (by linarith [hr.1]) _)), ← radial_primitive ha hρ hρR]

/-- Exact nonnegative identity behind the ball-mass estimate. -/
theorem nearField_layer_identity {a R : ℝ} (ha : a < 3)
    {h : Space → ℝ} (hh : Measurable h) :
    (∫⁻ y in Metric.ball (0 : Space) R, ENNReal.ofReal (‖y‖ ^ (a - 3)) * ENNReal.ofReal (h y)) =
      ENNReal.ofReal (R ^ (a - 3)) * (∫⁻ y in Metric.ball (0 : Space) R, ENNReal.ofReal (h y)) +
      ENNReal.ofReal (3 - a) *
        ∫⁻ r in Ioo 0 R, ENNReal.ofReal (r ^ (a - 4)) *
          ∫⁻ y in Metric.ball (0 : Space) r, ENNReal.ofReal (h y) := by
  have hq : Measurable (fun r : ℝ => ENNReal.ofReal (r ^ (a - 4))) := by fun_prop
  have he : (fun y : Space => ENNReal.ofReal (‖y‖ ^ (a - 3)) * ENNReal.ofReal (h y)) =ᵐ[
      volume.restrict (Metric.ball (0 : Space) R)]
      (fun y => ENNReal.ofReal (R ^ (a - 3)) * ENNReal.ofReal (h y) +
        ENNReal.ofReal (3 - a) *
          ((∫⁻ r in Ioo ‖y‖ R, ENNReal.ofReal (r ^ (a - 4))) * ENNReal.ofReal (h y))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_ball,
      ae_restrict_of_ae (show ∀ᵐ y : Space ∂volume, y ≠ 0 from volume.ae_ne 0)] with y hy hy0
    rw [radial_primitive_lintegral ha (norm_pos_iff.mpr hy0)
      (by simpa [Metric.mem_ball] using (show dist y 0 ≤ R from le_of_lt hy)), add_mul, mul_assoc]
  rw [lintegral_congr_ae he, lintegral_add_left (by fun_prop),
    lintegral_const_mul _ hh.ennreal_ofReal,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    radial_layer_tonelli R hh.ennreal_ofReal hq]

/-- The final radial power is integrable at the origin because `a > 0`. -/
theorem radial_lintegral {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    (∫⁻ r in Ioo 0 R, ENNReal.ofReal (r ^ (a - 1))) = ENNReal.ofReal (R ^ a / a) := by
  have hi := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R)
    (show -1 < a - 1 by linarith)
  have hn : 0 ≤ᵐ[volume.restrict (Ioc 0 R)] (fun r : ℝ => r ^ (a - 1)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    exact Real.rpow_nonneg hr.1.le _
  rw [restrict_Ioo_eq_restrict_Ioc, ← ofReal_integral_eq_lintegral_ofReal hi.1 hn,
    ← intervalIntegral.integral_of_le hR.le, integral_rpow (Or.inl (by linarith))]
  simp [show a - 1 + 1 = a by ring, Real.zero_rpow ha.ne']

/-- Ball-mass control gives the sharp elementary near-field constant. -/
theorem nearField_lintegral_bound {a R M : ℝ} (ha : 0 < a) (ha3 : a < 3)
    (hR : 0 < R) (hM : 0 ≤ M) {h : Space → ℝ} (hh : Measurable h)
    (hmass : ∀ r : ℝ, 0 < r → r ≤ R →
      (∫⁻ y in Metric.ball (0 : Space) r, ENNReal.ofReal (h y)) ≤
        ENNReal.ofReal (M * (4 * Real.pi / 3) * r ^ 3)) :
    (∫⁻ y in Metric.ball (0 : Space) R, ENNReal.ofReal (‖y‖ ^ (a - 3) * h y)) ≤
      ENNReal.ofReal ((4 * Real.pi / a) * M * R ^ a) := by
  let C : ℝ := M * (4 * Real.pi / 3)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hq : Measurable (fun r : ℝ => ENNReal.ofReal (r ^ (a - 1))) := by fun_prop
  have hpow (r : ℝ) (hr : 0 < r) : r ^ (a - 4) * r ^ 3 = r ^ (a - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr]
    congr 1
    ring
  have hrad :
      (∫⁻ r in Ioo 0 R, ENNReal.ofReal (r ^ (a - 4)) *
        ∫⁻ y in Metric.ball (0 : Space) r, ENNReal.ofReal (h y)) ≤
      ENNReal.ofReal C * ENNReal.ofReal (R ^ a / a) := by
    calc
      _ ≤ ∫⁻ r in Ioo 0 R, ENNReal.ofReal (r ^ (a - 4)) * ENNReal.ofReal (C * r ^ 3) := by
        apply setLIntegral_mono' measurableSet_Ioo
        intro r hr
        exact mul_le_mul_right (hmass r hr.1 hr.2.le) _
      _ = ∫⁻ r in Ioo 0 R, ENNReal.ofReal C * ENNReal.ofReal (r ^ (a - 1)) := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro r hr
        dsimp only
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.1.le _),
          ← ENNReal.ofReal_mul hC]
        congr 1
        calc
          _ = C * (r ^ (a - 4) * r ^ 3) := by ring
          _ = _ := by rw [hpow r hr.1]
      _ = _ := by rw [lintegral_const_mul _ hq, radial_lintegral ha hR]
  simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [nearField_layer_identity ha3 hh]
  calc
    _ ≤ ENNReal.ofReal (R ^ (a - 3)) * ENNReal.ofReal (C * R ^ 3) +
        ENNReal.ofReal (3 - a) * (ENNReal.ofReal C * ENNReal.ofReal (R ^ a / a)) :=
      add_le_add (mul_le_mul_right (hmass R hR le_rfl) _) (mul_le_mul_right hrad _)
    _ = ENNReal.ofReal ((4 * Real.pi / a) * M * R ^ a) := by
      rw [← ENNReal.ofReal_mul hC,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _),
        ← ENNReal.ofReal_mul (by linarith : 0 ≤ 3 - a),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      have hp : R ^ (a - 3) * R ^ 3 = R ^ a := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hR]
        congr 1
        ring
      calc
        _ = C * (R ^ (a - 3) * R ^ 3) + (3 - a) * (C * (R ^ a / a)) := by ring
        _ = _ := by rw [hp]; dsimp [C]; field_simp; ring

/-- The ball-mass hypotheses imply genuine integrability of the singular product. -/
theorem nearField_integrable {a R M : ℝ} (ha : 0 < a) (ha3 : a < 3)
    (hR : 0 < R) (hM : 0 ≤ M) {h : Space → ℝ} (hh : Measurable h)
    (hn : ∀ y, 0 ≤ h y)
    (hmass : ∀ r : ℝ, 0 < r → r ≤ R →
      (∫⁻ y in Metric.ball (0 : Space) r, ENNReal.ofReal (h y)) ≤
        ENNReal.ofReal (M * (4 * Real.pi / 3) * r ^ 3)) :
    IntegrableOn (fun y : Space => ‖y‖ ^ (a - 3) * h y) (Metric.ball (0 : Space) R) := by
  refine ⟨(show Measurable (fun y : Space => ‖y‖ ^ (a - 3) * h y) by fun_prop).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_enorm_of_nonneg (fun y =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg y) _) (hn y))]
  exact lt_of_le_of_lt (nearField_lintegral_bound ha ha3 hR hM hh hmass) ENNReal.ofReal_lt_top

/-- The ordinary near-field integral has the same exact bound, with integrability proved. -/
theorem nearField_integral_bound {a R M : ℝ} (ha : 0 < a) (ha3 : a < 3)
    (hR : 0 < R) (hM : 0 ≤ M) {h : Space → ℝ} (hh : Measurable h)
    (hn : ∀ y, 0 ≤ h y)
    (hmass : ∀ r : ℝ, 0 < r → r ≤ R →
      (∫⁻ y in Metric.ball (0 : Space) r, ENNReal.ofReal (h y)) ≤
        ENNReal.ofReal (M * (4 * Real.pi / 3) * r ^ 3)) :
    (∫ y in Metric.ball (0 : Space) R, ‖y‖ ^ (a - 3) * h y) ≤
      (4 * Real.pi / a) * M * R ^ a := by
  have hi := nearField_integrable ha ha3 hR hM hh hn hmass
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun y =>
      mul_nonneg (Real.rpow_nonneg (norm_nonneg y) _) (hn y)))
  have hb := nearField_lintegral_bound ha ha3 hR hM hh hmass
  rw [← he] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

end NSFormalization.RieszBallMass
