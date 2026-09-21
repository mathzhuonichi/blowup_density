import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The unnormalized Riesz far-field estimate in three dimensions

The square-kernel tail integral is proved by radial integration, and the
sharp product estimate follows from L2 Holder and measure-preserving
subtraction. The far-field argument requires only `a < 3/2`; in particular
it covers the Riesz range `0 < a < 3/2`. This module is one component of
the shared critical embedding argument, not the complete embedding.
-/

open MeasureTheory Set Real
open scoped ENNReal

namespace NSFormalization.RieszPotentialTail

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The radial scalar integrability input for the far-field square kernel. -/
theorem radial_power_integrable {a R : ℝ} (ha : a < 3 / 2) (hR : 0 < R) :
    IntegrableOn (fun r : ℝ => r ^ (2 * a - 4)) (Ioi R) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) hR

/-- Exact radial integral before multiplication by the unit-sphere area. -/
theorem radial_power_integral {a R : ℝ} (ha : a < 3 / 2) (hR : 0 < R) :
    (∫ r : ℝ in Ioi R, r ^ (2 * a - 4)) = R ^ (2 * a - 3) / (3 - 2 * a) := by
  rw [integral_Ioi_rpow_of_lt (by linarith : 2 * a - 4 < -1) hR]
  rw [show 2 * a - 4 + 1 = 2 * a - 3 by ring]
  have hd : 2 * a - 3 ≠ 0 := by linarith
  have hd' : 3 - 2 * a ≠ 0 := by linarith
  field_simp
  ring

/-- The squared kernel is genuinely integrable outside a positive radius. -/
theorem tail_power_integrable {a R : ℝ} (ha : a < 3 / 2) (hR : 0 < R) :
    Integrable (fun y : Space => (Ioi R).indicator (fun r : ℝ => r ^ (2 * a - 6)) ‖y‖) := by
  rw [integrable_fun_norm_addHaar]
  have heq : (fun r : ℝ => r ^ (Module.finrank ℝ Space - 1) •
      (Ioi R).indicator (fun r : ℝ => r ^ (2 * a - 6)) r) =
      (Ioi R).indicator (fun r : ℝ => r ^ (2 * a - 4)) := by
    funext r
    by_cases hr : r ∈ Ioi R
    · simp only [Set.indicator_of_mem hr, smul_eq_mul]
      have hp : 0 < r := hR.trans hr
      simp only [Space, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub]
      rw [← Real.rpow_natCast, ← Real.rpow_add hp]
      congr 1
      ring
    · simp [Set.indicator_of_notMem hr]
  rw [heq]
  exact ((integrable_indicator_iff measurableSet_Ioi).2 (radial_power_integrable ha hR)).integrableOn

/-- Exact three-dimensional squared-kernel tail integral. -/
theorem tail_power_integral {a R : ℝ} (ha : a < 3 / 2) (hR : 0 < R) :
    (∫ y : Space, (Ioi R).indicator (fun r : ℝ => r ^ (2 * a - 6)) ‖y‖) =
      (4 * Real.pi / (3 - 2 * a)) * R ^ (2 * a - 3) := by
  rw [integral_fun_norm_addHaar]
  have heq : (fun r : ℝ => r ^ (Module.finrank ℝ Space - 1) •
      (Ioi R).indicator (fun r : ℝ => r ^ (2 * a - 6)) r) =
      (Ioi R).indicator (fun r : ℝ => r ^ (2 * a - 4)) := by
    funext r
    by_cases hr : r ∈ Ioi R
    · simp only [Set.indicator_of_mem hr, smul_eq_mul]
      have hp : 0 < r := hR.trans hr
      simp only [Space, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub]
      rw [← Real.rpow_natCast, ← Real.rpow_add hp]
      congr 1
      ring
    · simp [Set.indicator_of_notMem hr]
  rw [heq, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  rw [show Ioi R ∩ Ioi (0 : ℝ) = Ioi R from Set.inter_eq_left.mpr (fun _ hr => hR.trans hr), radial_power_integral ha hR]
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul,
    Measure.real, EuclideanSpace.volume_ball_fin_three]
  norm_num
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

/-- The unnormalized far-field Riesz kernel, extended by zero. -/
noncomputable def tailKernel (a R : ℝ) (y : Space) : ℝ :=
  (Ioi R).indicator (fun r : ℝ => r ^ (a - 3)) ‖y‖

lemma tailKernel_sq (a R : ℝ) (y : Space) :
    tailKernel a R y ^ 2 = (Ioi R).indicator (fun r : ℝ => r ^ (2 * a - 6)) ‖y‖ := by
  by_cases hy : ‖y‖ ∈ Ioi R
  · simp only [tailKernel, Set.indicator_of_mem hy]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg y)]
    congr 1
    ring
  · simp [tailKernel, Set.indicator_of_notMem hy]

/-- Actual L2 membership, obtained from the finite radial integral. -/
theorem tailKernel_memLp {a R : ℝ} (ha : a < 3 / 2) (hR : 0 < R) :
    MemLp (tailKernel a R) 2 volume := by
  apply (memLp_two_iff_integrable_sq ?_).2
  · simpa only [tailKernel_sq] using tail_power_integrable ha hR
  · unfold tailKernel
    exact ((measurable_id.pow_const _).indicator measurableSet_Ioi).comp
      continuous_norm.measurable |>.aestronglyMeasurable

theorem translated_memLp {g : Space → ℂ} (hg : MemLp g 2 volume) (x : Space) :
    MemLp (fun y => g (x - y)) 2 volume :=
  hg.comp_measurePreserving (volume.measurePreserving_sub_left x)

/-- Absolute integrability follows from L2 Holder, with no tail-integral assumption. -/
theorem tail_product_integrable {a R : ℝ} (ha : a < 3 / 2) (hR : 0 < R)
    {g : Space → ℂ} (hg : MemLp g 2 volume) (x : Space) :
    Integrable (fun y => tailKernel a R y * ‖g (x - y)‖) := by
  exact memLp_one_iff_integrable.mp ((translated_memLp hg x).norm.mul' (tailKernel_memLp ha hR))

lemma tailKernel_nonneg (a R : ℝ) (y : Space) : 0 ≤ tailKernel a R y := by
  unfold tailKernel
  by_cases hy : ‖y‖ ∈ Ioi R
  · simpa only [Set.indicator_of_mem hy] using Real.rpow_nonneg (norm_nonneg y) (a - 3)
  · simp [Set.indicator_of_notMem hy]

/-- Sharp far-field bound for the zero-extended kernel. -/
theorem tail_product_bound {a R : ℝ} (ha : a < 3 / 2) (hR : 0 < R)
    {g : Space → ℂ} (hg : MemLp g 2 volume) (x : Space) :
    (∫ y, tailKernel a R y * ‖g (x - y)‖) ≤
      Real.sqrt (4 * Real.pi / (3 - 2 * a)) * (eLpNorm g 2 volume).toReal *
        R ^ (a - 3 / 2) := by
  have hk := tailKernel_memLp ha hR
  have ht := translated_memLp hg x
  have hn : (∫ y, ‖g (x - y)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
      (eLpNorm g 2 volume).toReal := by
    have he := eLpNorm_comp_measurePreserving hg.aestronglyMeasurable
      (volume.measurePreserving_sub_left x) (p := (2 : ℝ≥0∞))
    rw [← he]
    simp only [Function.comp_def]
    rw [ht.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, inv_eq_one_div]
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hb := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (tailKernel_nonneg a R))
    (Filter.Eventually.of_forall (fun y => norm_nonneg (g (x - y))))
    (by simpa using hk) (by simpa using ht.norm)
  have hs : (∫ y, tailKernel a R y ^ (2 : ℝ)) =
      (4 * Real.pi / (3 - 2 * a)) * R ^ (2 * a - 3) := by
    simpa only [Real.rpow_two, tailKernel_sq] using tail_power_integral ha hR
  rw [hs, hn] at hb
  have hd : 0 < 3 - 2 * a := by linarith
  have hc : 0 ≤ 4 * Real.pi / (3 - 2 * a) := by positivity
  rw [Real.mul_rpow hc (Real.rpow_nonneg hR.le _), ← Real.sqrt_eq_rpow, ← Real.rpow_mul hR.le,
    show (2 * a - 3) * (1 / 2) = a - 3 / 2 by ring] at hb
  nlinarith [hb]

lemma closedTail_indicator_ae (a R : ℝ) (g : Space → ℂ) (x : Space) :
    {y : Space | R ≤ ‖y‖}.indicator (fun y => ‖y‖ ^ (a - 3) * ‖g (x - y)‖)
      =ᵐ[volume] (fun y => tailKernel a R y * ‖g (x - y)‖) := by
  have hz : ∀ᵐ y : Space ∂volume, y ∉ Metric.sphere (0 : Space) R :=
    (ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using Measure.addHaar_sphere volume (0 : Space) R))
  filter_upwards [hz] with y hy
  have hne : ‖y‖ ≠ R := by simpa [Metric.mem_sphere, dist_zero_right] using hy
  by_cases hr : R ≤ ‖y‖
  · have hr' : ‖y‖ ∈ Ioi R := lt_of_le_of_ne hr (Ne.symm hne)
    simp [Set.indicator, hr, tailKernel, hr']
  · have hr' : ‖y‖ ∉ Ioi R := fun h => hr h.le
    simp [Set.indicator, hr, tailKernel, hr']

/-- Absolute integrability on the closed far-field region. -/
theorem closedTail_integrable {a R : ℝ} (ha : a < 3 / 2) (hR : 0 < R)
    {g : Space → ℂ} (hg : MemLp g 2 volume) (x : Space) :
    IntegrableOn (fun y => ‖y‖ ^ (a - 3) * ‖g (x - y)‖) {y : Space | R ≤ ‖y‖} := by
  apply (integrable_indicator_iff (measurableSet_le measurable_const continuous_norm.measurable)).1
  exact (tail_product_integrable ha hR hg x).congr (closedTail_indicator_ae a R g x).symm

/-- The sharp unnormalized Riesz far-field estimate in three dimensions. -/
theorem closedTail_bound {a R : ℝ} (ha : a < 3 / 2) (hR : 0 < R)
    {g : Space → ℂ} (hg : MemLp g 2 volume) (x : Space) :
    (∫ y in {y : Space | R ≤ ‖y‖}, ‖y‖ ^ (a - 3) * ‖g (x - y)‖) ≤
      Real.sqrt (4 * Real.pi / (3 - 2 * a)) * (eLpNorm g 2 volume).toReal *
        R ^ (a - 3 / 2) := by
  rw [← integral_indicator (measurableSet_le measurable_const continuous_norm.measurable),
    integral_congr_ae (closedTail_indicator_ae a R g x)]
  exact tail_product_bound ha hR hg x

/-- The half-order endpoint of the shared critical analysis. -/
theorem closedTail_half_bound {R : ℝ} (hR : 0 < R)
    {g : Space → ℂ} (hg : MemLp g 2 volume) (x : Space) :
    (∫ y in {y : Space | R ≤ ‖y‖}, ‖y‖ ^ (-(5 : ℝ) / 2) * ‖g (x - y)‖) ≤
      Real.sqrt (2 * Real.pi) * (eLpNorm g 2 volume).toReal * R ^ (-(1 : ℝ)) := by
  have hc : 4 * Real.pi / (3 - 2 * ((1 : ℝ) / 2)) = 2 * Real.pi := by ring
  simpa only [hc, show (1 : ℝ) / 2 - 3 = -5 / 2 by norm_num,
    show (1 : ℝ) / 2 - 3 / 2 = -1 by norm_num] using
    closedTail_bound (a := (1 : ℝ) / 2) (by norm_num) hR hg x

/-- The order-one endpoint of the shared critical analysis. -/
theorem closedTail_one_bound {R : ℝ} (hR : 0 < R)
    {g : Space → ℂ} (hg : MemLp g 2 volume) (x : Space) :
    (∫ y in {y : Space | R ≤ ‖y‖}, ‖y‖ ^ (-(2 : ℝ)) * ‖g (x - y)‖) ≤
      Real.sqrt (4 * Real.pi) * (eLpNorm g 2 volume).toReal * R ^ (-(1 : ℝ) / 2) := by
  convert closedTail_bound (a := (1 : ℝ)) (by norm_num) hR hg x using 1 <;> norm_num

end NSFormalization.RieszPotentialTail
