import NSFormalization.Source.CenteredMaximal
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.L2Space

/-! # Strong L2 control of the actual centered maximal operator -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NSFormalization.CenteredMaximal

theorem centeredMaximal_mono {H K : Space → ℝ≥0∞} (hHK : ∀ x, H x ≤ K x) (x : Space) :
    centeredMaximal H x ≤ centeredMaximal K x := by
  apply iSup_mono
  intro q
  exact ENNReal.div_le_div_right (lintegral_mono hHK) _

theorem centeredMaximal_add_le (H K : Space → ℝ≥0∞) (hK : Measurable K) (x : Space) :
    centeredMaximal (H + K) x ≤ centeredMaximal H x + centeredMaximal K x := by
  apply iSup_le
  intro q
  change (∫⁻ y in Metric.ball x (q : ℚ), H y + K y) / ballVolume (q : ℚ) ≤ _
  rw [lintegral_add_right _ hK, ENNReal.add_div]
  exact add_le_add (le_iSup (fun q : PositiveRadius => ballAverage H (q : ℚ) x) q)
    (le_iSup (fun q : PositiveRadius => ballAverage K (q : ℚ) x) q)

theorem centeredMaximal_const_le (c : ℝ≥0∞) (x : Space) :
    centeredMaximal (fun _ => c) x ≤ c := by
  apply iSup_le
  intro q
  change (∫⁻ y in Metric.ball x (q : ℚ), c) / ballVolume (q : ℚ) ≤ c
  rw [lintegral_const, Measure.restrict_apply_univ, ← ballVolume_eq]
  have hp : 0 < ballVolume (q : ℚ) := ballVolume_pos (by exact_mod_cast q.property)
  rw [ENNReal.mul_div_cancel_right hp.ne' (ballVolume_ne_top _)]

/-- The high part of a real density at a positive level. -/
def highDensity (h : Space → ℝ) (t : ℝ) : Space → ℝ≥0∞ :=
  {x | t / 2 < h x}.indicator (fun x => ENNReal.ofReal (h x))

theorem measurable_highDensity {h : Space → ℝ} (hh : Measurable h) (t : ℝ) :
    Measurable (highDensity h t) := hh.ennreal_ofReal.indicator (measurableSet_lt measurable_const hh)

/-- Low values contribute at most half the level to the maximal operator. -/
theorem maximal_le_high_add {h : Space → ℝ} (_hh : Measurable h) (t : ℝ) (_ht : 0 ≤ t) (x : Space) :
    centeredMaximal (fun y => ENNReal.ofReal (h y)) x ≤
      centeredMaximal (highDensity h t) x + ENNReal.ofReal (t / 2) := by
  calc
    _ ≤ centeredMaximal (highDensity h t + fun _ => ENNReal.ofReal (t / 2)) x := by
      apply centeredMaximal_mono
      intro y
      by_cases hy : t / 2 < h y
      · simp [highDensity, hy]
      · simpa [Pi.add_apply, highDensity, hy] using ENNReal.ofReal_le_ofReal (le_of_not_gt hy)
    _ ≤ centeredMaximal (highDensity h t) x + centeredMaximal (fun _ => ENNReal.ofReal (t / 2)) x :=
      centeredMaximal_add_le _ _ measurable_const x
    _ ≤ _ := add_le_add le_rfl (centeredMaximal_const_le _ x)

/-- Refined weak control by the actual high-level tail mass. -/
theorem maximal_refined_level {h : Space → ℝ} (hh : Measurable h) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal t * volume {x | ENNReal.ofReal t < centeredMaximal (fun y => ENNReal.ofReal (h y)) x} ≤
      128 * ∫⁻ x, highDensity h t x := by
  have hs : {x | ENNReal.ofReal t < centeredMaximal (fun y => ENNReal.ofReal (h y)) x} ⊆
      {x | ENNReal.ofReal (t / 2) < centeredMaximal (highDensity h t) x} := by
    intro x hx
    by_contra hn
    have hb := maximal_le_high_add hh t ht.le x
    have hl : centeredMaximal (highDensity h t) x ≤ ENNReal.ofReal (t/2) := le_of_not_gt hn
    have hsum : ENNReal.ofReal (t/2) + ENNReal.ofReal (t/2) = ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    exact (not_le_of_gt hx) (hb.trans (by simpa [hsum] using add_le_add hl (le_rfl : ENNReal.ofReal (t/2) ≤ ENNReal.ofReal (t/2))))
  have hw := centeredMaximal_weak (highDensity h t) (t/2) (by positivity)
  have hhalf : ENNReal.ofReal t = 2 * ENNReal.ofReal (t/2) := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  calc
    _ ≤ ENNReal.ofReal t * volume {x | ENNReal.ofReal (t / 2) < centeredMaximal (highDensity h t) x} := by gcongr
    _ = 2 * (ENNReal.ofReal (t/2) * volume {x | ENNReal.ofReal (t / 2) < centeredMaximal (highDensity h t) x}) := by rw [hhalf]; ring
    _ ≤ 2 * (64 * ∫⁻ x, highDensity h t x) := by gcongr
    _ = _ := by ring

/-- Tonelli evaluates the integral of all high-level tail masses exactly. -/
theorem highDensity_layer_integral {h : Space → ℝ} (hh : Measurable h) (hn : ∀ x, 0 ≤ h x) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, highDensity h t x) =
      2 * ∫⁻ x, ENNReal.ofReal (h x ^ 2) := by
  have hf : Measurable (Function.uncurry (fun t x => highDensity h t x)) := by
    change Measurable ({p : ℝ × Space | p.1 / 2 < h p.2}.indicator
      (fun p => ENNReal.ofReal (h p.2)))
    exact (hh.ennreal_ofReal.comp measurable_snd).indicator
      (measurableSet_lt (measurable_fst.div_const 2) (hh.comp measurable_snd))
  rw [lintegral_lintegral_swap hf.aemeasurable, ← lintegral_const_mul _ (hh.pow_const 2).ennreal_ofReal]
  apply lintegral_congr
  intro x
  have he : (fun t => highDensity h t x) =
      (Iio (2 * h x)).indicator (fun _ => ENNReal.ofReal (h x)) := by
    funext t
    by_cases ht : t / 2 < h x
    · have ht' : t < 2 * h x := by linarith
      simp [highDensity, ht, ht']
    · have ht' : ¬ t < 2 * h x := by linarith
      simp [highDensity, ht, ht']
  rw [he, setLIntegral_indicator measurableSet_Iio]
  have hs : Iio (2 * h x) ∩ Ioi 0 = Ioo 0 (2 * h x) := by ext t; simp [and_comm]
  rw [hs, lintegral_const]
  simp only [Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_pow (hn x)]
  norm_num
  ring

/-- Finite real cap, used before any finite-a.e. statement about the maximal value. -/
def cappedMaximal (h : Space → ℝ) (L : ℝ) (x : Space) : ℝ :=
  (min (centeredMaximal (fun y => ENNReal.ofReal (h y)) x) (ENNReal.ofReal L)).toReal

theorem cappedMaximal_measurable {h : Space → ℝ} (hh : Measurable h) (L : ℝ) :
    Measurable (cappedMaximal h L) :=
  ((measurable_centeredMaximal hh.ennreal_ofReal).min measurable_const).ennreal_toReal

/-- Uniform square-integral estimate for every finite cap. -/
theorem cappedMaximal_square_bound {h : Space → ℝ} (hh : Measurable h) (hn : ∀ x, 0 ≤ h x)
    (L : ℝ) :
    (∫⁻ x, ENNReal.ofReal (cappedMaximal h L x ^ 2)) ≤
      512 * ∫⁻ x, ENNReal.ofReal (h x ^ 2) := by
  have hf : ∀ x, 0 ≤ cappedMaximal h L x := fun _ => ENNReal.toReal_nonneg
  have he := lintegral_rpow_eq_lintegral_meas_lt_mul volume
    (Filter.Eventually.of_forall hf) (cappedMaximal_measurable hh L).aemeasurable (by norm_num : (0:ℝ) < 2)
  simp only [Real.rpow_two, show (2:ℝ)-1=1 by norm_num, Real.rpow_one, ENNReal.ofReal_ofNat] at he
  rw [he]
  calc
    _ ≤ 2 * ∫⁻ t in Ioi (0:ℝ), 128 * ∫⁻ x, highDensity h t x := by
      apply mul_le_mul_right
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      have hs : {x | t < cappedMaximal h L x} ⊆
          {x | ENNReal.ofReal t < centeredMaximal (fun y => ENNReal.ofReal (h y)) x} := by
        intro x hx
        have hc : ENNReal.ofReal (cappedMaximal h L x) ≤
            centeredMaximal (fun y => ENNReal.ofReal (h y)) x := by
          exact ENNReal.ofReal_toReal_le.trans (min_le_left _ _)
        exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans ht hx)).mpr hx |>.trans_le hc
      calc
        _ ≤ volume {x | ENNReal.ofReal t < centeredMaximal (fun y => ENNReal.ofReal (h y)) x} * ENNReal.ofReal t := by gcongr
        _ ≤ _ := by simpa [mul_comm] using maximal_refined_level hh t ht
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by norm_num : (128:ℝ≥0∞) ≠ ⊤), highDensity_layer_integral hh hn]
      ring

/-- Strong square-integral bound for the actual ENNReal maximal value. -/
theorem centeredMaximal_square_bound {h : Space → ℝ} (hh : Measurable h) (hn : ∀ x, 0 ≤ h x) :
    (∫⁻ x, centeredMaximal (fun y => ENNReal.ofReal (h y)) x ^ 2) ≤
      512 * ∫⁻ x, ENNReal.ofReal (h x ^ 2) := by
  let F := centeredMaximal (fun y => ENNReal.ofReal (h y))
  have hF : Measurable F := measurable_centeredMaximal hh.ennreal_ofReal
  have hc (n : ℕ) (x : Space) : ENNReal.ofReal (cappedMaximal h (n : ℝ) x ^ 2) =
      min (F x) (n : ℝ≥0∞) ^ 2 := by
    unfold cappedMaximal
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg]
    simp only [ENNReal.ofReal_natCast]
    congr 1
    exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by simp) (min_le_right _ _))
  have hm : ∀ᵐ x : Space ∂volume, Monotone (fun n : ℕ => min (F x) (n : ℝ≥0∞) ^ 2) := by
    apply Filter.Eventually.of_forall
    intro x n k hnk
    dsimp only
    gcongr
  have ht : ∀ᵐ x : Space ∂volume,
      Filter.Tendsto (fun n : ℕ => min (F x) (n : ℝ≥0∞) ^ 2) Filter.atTop (nhds (F x ^ 2)) := by
    apply Filter.Eventually.of_forall
    intro x
    have ht := (tendsto_const_nhds (x := F x)).min ENNReal.tendsto_nat_nhds_top
    simpa only [min_eq_left (le_top : F x ≤ ⊤)] using (ENNReal.Tendsto.pow (n := 2) ht)
  have hi := lintegral_tendsto_of_tendsto_of_monotone
    (fun n => ((hF.min measurable_const).pow_const 2).aemeasurable) hm ht
  apply le_of_tendsto' hi
  intro n
  simpa only [hc] using cappedMaximal_square_bound hh hn (n : ℝ)

/-- Finite L2 input forces the maximal value to be finite almost everywhere. -/
theorem centeredMaximal_ae_lt_top {h : Space → ℝ} (hh : Measurable h) (hn : ∀ x, 0 ≤ h x)
    (h2 : MemLp h 2 volume) :
    ∀ᵐ x : Space ∂volume, centeredMaximal (fun y => ENNReal.ofReal (h y)) x < ⊤ := by
  have hi : (∫⁻ x, centeredMaximal (fun y => ENNReal.ofReal (h y)) x ^ 2) < ⊤ :=
    lt_of_le_of_lt (centeredMaximal_square_bound hh hn)
      (ENNReal.mul_lt_top (by norm_num) h2.integrable_sq.lintegral_lt_top)
  have ha := ae_lt_top ((measurable_centeredMaximal hh.ennreal_ofReal).pow_const 2) hi.ne
  filter_upwards [ha] with x hx
  by_contra ht
  have ht' : centeredMaximal (fun y => ENNReal.ofReal (h y)) x = ⊤ := le_antisymm le_top (not_lt.mp ht)
  simp [ht'] at hx

/-- The real maximal representative is used only after its a.e. finiteness is established. -/
theorem centeredMaximal_toReal_memLp {h : Space → ℝ} (hh : Measurable h) (hn : ∀ x, 0 ≤ h x)
    (h2 : MemLp h 2 volume) :
    MemLp (fun x => (centeredMaximal (fun y => ENNReal.ofReal (h y)) x).toReal) 2 volume := by
  have hf := centeredMaximal_ae_lt_top hh hn h2
  apply (memLp_two_iff_integrable_sq
    (measurable_centeredMaximal hh.ennreal_ofReal).ennreal_toReal.aestronglyMeasurable).mpr
  refine ⟨((measurable_centeredMaximal hh.ennreal_ofReal).ennreal_toReal.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_enorm_of_nonneg (fun _ => sq_nonneg _)]
  have he : (fun x => ENNReal.ofReal ((centeredMaximal (fun y => ENNReal.ofReal (h y)) x).toReal ^ 2)) =ᵐ[volume]
      (fun x => centeredMaximal (fun y => ENNReal.ofReal (h y)) x ^ 2) := by
    filter_upwards [hf] with x hx
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  rw [lintegral_congr_ae he]
  exact lt_of_le_of_lt (centeredMaximal_square_bound hh hn)
    (ENNReal.mul_lt_top (by norm_num) h2.integrable_sq.lintegral_lt_top)

private theorem realLp_norm_sq {f : Space → ℝ} (h2 : MemLp f 2 volume) :
    ‖h2.toLp f‖ ^ 2 = (∫⁻ x, ENNReal.ofReal (f x ^ 2)).toReal := by
  calc
    _ = inner ℝ (h2.toLp f) (h2.toLp f) := (real_inner_self_eq_norm_sq _).symm
    _ = ∫ x, inner ℝ (h2.toLp f x) (h2.toLp f x) := L2.inner_def _ _
    _ = ∫ x, f x ^ 2 := by
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp] with x hx
      simp [hx, pow_two]
    _ = _ := integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x => sq_nonneg (f x))) h2.integrable_sq.aestronglyMeasurable

/-- The actual L2 norm of the real maximal representative is bounded by sqrt(512). -/
theorem centeredMaximal_toLp_norm_le {h : Space → ℝ} (hh : Measurable h) (hn : ∀ x, 0 ≤ h x)
    (h2 : MemLp h 2 volume) :
    ‖(centeredMaximal_toReal_memLp hh hn h2).toLp _‖ ≤ Real.sqrt 512 * ‖h2.toLp h‖ := by
  have hf := centeredMaximal_ae_lt_top hh hn h2
  have he : (fun x => ENNReal.ofReal ((centeredMaximal (fun y => ENNReal.ofReal (h y)) x).toReal ^ 2)) =ᵐ[volume]
      (fun x => centeredMaximal (fun y => ENNReal.ofReal (h y)) x ^ 2) := by
    filter_upwards [hf] with x hx
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  have hb := ENNReal.toReal_mono
    (ENNReal.mul_lt_top (by norm_num : (512:ℝ≥0∞) < ⊤) h2.integrable_sq.lintegral_lt_top).ne
    (centeredMaximal_square_bound hh hn)
  rw [← lintegral_congr_ae he, ← realLp_norm_sq (centeredMaximal_toReal_memLp hh hn h2),
    ENNReal.toReal_mul, ← realLp_norm_sq h2] at hb
  norm_num only [ENNReal.toReal_ofNat] at hb
  have hs : (Real.sqrt 512 * ‖h2.toLp h‖) ^ 2 = 512 * ‖h2.toLp h‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have hn' : 0 ≤ Real.sqrt 512 * ‖h2.toLp h‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg ((centeredMaximal_toReal_memLp hh hn h2).toLp _)]

end NSFormalization.CenteredMaximal
