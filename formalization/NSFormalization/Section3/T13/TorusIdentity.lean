import NSFormalization.Section3.T13.Localization
import NSFormalization.Section3.T10.FourierCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# T13 torus Gagliardo identity

Proof of the `torus_identity` field of the reconciled `LocalizationAPI`
(`research/T13/probes/api_on_canonical.lean`), following the paper's own proof
in `paper/sections/03-torus.tex:53-72`.
-/

noncomputable section

namespace NSFormalization.Section3.T13

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open NavierStokes.PeriodicIntegration (Coords toSpace cube cubeMeasure cubeIntegral
  cubeIntegral_sum)
open scoped ContDiff ENNReal BigOperators Topology RealInnerProductSpace

/-! ## 1. The directional whole-space kernel integral -/

/-- `03-torus.tex:35-39,60-66`: the whole-space difference integral in the
direction `ξ`.  `cFrac s` is its value at the first unit coordinate vector. -/
def kernelIntegral (s : ℝ) (ξ : Space) : ℝ≥0∞ :=
  ∫⁻ h : Space, ENNReal.ofReal (‖Complex.exp (Complex.I * ((⟪ξ, h⟫ : ℝ) : ℂ)) - 1‖ ^ 2) *
    fractionalRadialKernel s h

theorem measurable_fractionalRadialKernel (s : ℝ) :
    Measurable (fractionalRadialKernel s) := by
  unfold fractionalRadialKernel
  fun_prop

theorem measurable_kernelIntegrand (s : ℝ) (ξ : Space) :
    Measurable (fun h : Space ↦
      ENNReal.ofReal (‖Complex.exp (Complex.I * ((⟪ξ, h⟫ : ℝ) : ℂ)) - 1‖ ^ 2) *
        fractionalRadialKernel s h) := by
  refine Measurable.mul ?_ (measurable_fractionalRadialKernel s)
  apply ENNReal.measurable_ofReal.comp
  fun_prop

theorem cFrac_eq_kernelIntegral (s : ℝ) :
    cFrac s = kernelIntegral s (coordinateVector 0) := by
  unfold cFrac kernelIntegral
  refine lintegral_congr fun h ↦ ?_
  have : (⟪coordinateVector 0, h⟫ : ℝ) = h 0 := by
    rw [coordinateVector, EuclideanSpace.inner_single_left]
    simp
  rw [this]

/-- Whole-space rotation invariance of the directional integral. -/
theorem kernelIntegral_isometry (s : ℝ) (R : Space ≃ₗᵢ[ℝ] Space) (ξ : Space) :
    kernelIntegral s (R ξ) = kernelIntegral s ξ := by
  have hmp : MeasurePreserving (⇑R) (volume : Measure Space) volume := R.measurePreserving
  have h := hmp.lintegral_comp (measurable_kernelIntegrand s (R ξ))
  rw [kernelIntegral, ← h]
  refine lintegral_congr fun h ↦ ?_
  have hi : (⟪R ξ, R h⟫ : ℝ) = (⟪ξ, h⟫ : ℝ) := R.inner_map_map ξ h
  have hn : ‖R h‖ = ‖h‖ := R.norm_map h
  rw [hi]
  unfold fractionalRadialKernel
  rw [hn]

/-- Change of variables `h ↦ r • h` for the Lebesgue integral on `Space`. -/
theorem lintegral_comp_smul_space (F : Space → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    ∫⁻ h : Space, F (r • h) = ENNReal.ofReal |(r ^ 3)⁻¹| * ∫⁻ h : Space, F h := by
  have h1 : ∫⁻ h : Space, F (r • h)
      = ∫⁻ a : Space, F a ∂(Measure.map (fun x : Space ↦ r • x) volume) :=
    (lintegral_map_equiv F
      (Homeomorph.smul (isUnit_iff_ne_zero.2 hr).unit).toMeasurableEquiv).symm
  rw [h1, Measure.map_addHaar_smul volume hr, lintegral_smul_measure]
  norm_num [finrank_euclideanSpace_fin]

/-- Dilation of the directional integral. -/
theorem kernelIntegral_smul (s : ℝ) {r : ℝ} (hr : 0 < r) (ξ : Space) :
    kernelIntegral s (r • ξ) = ENNReal.ofReal (r ^ (2 * s)) * kernelIntegral s ξ := by
  have hrne : (ENNReal.ofReal r) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]
    exact not_le.2 hr
  have hker : ∀ h : Space,
      fractionalRadialKernel s h =
        ENNReal.ofReal (r ^ (3 + 2 * s)) * fractionalRadialKernel s (r • h) := by
    intro h
    unfold fractionalRadialKernel
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, ENNReal.ofReal_mul hr.le,
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ← ENNReal.ofReal_rpow_of_pos hr, ← mul_assoc,
      ← ENNReal.rpow_add _ _ hrne ENNReal.ofReal_ne_top]
    simp
  have hphase : ∀ h : Space, ((⟪r • ξ, h⟫ : ℝ)) = ((⟪ξ, r • h⟫ : ℝ)) := by
    intro h
    rw [real_inner_smul_left, real_inner_smul_right]
  have h1 : kernelIntegral s (r • ξ) =
      ∫⁻ h : Space, ENNReal.ofReal (r ^ (3 + 2 * s)) *
        (ENNReal.ofReal (‖Complex.exp (Complex.I * ((⟪ξ, r • h⟫ : ℝ) : ℂ)) - 1‖ ^ 2) *
          fractionalRadialKernel s (r • h)) := by
    refine lintegral_congr fun h ↦ ?_
    rw [hphase h]
    conv_lhs => rw [hker h]
    ring
  have hmeas : Measurable (fun h : Space ↦
      ENNReal.ofReal (‖Complex.exp (Complex.I * ((⟪ξ, r • h⟫ : ℝ) : ℂ)) - 1‖ ^ 2) *
        fractionalRadialKernel s (r • h)) :=
    (measurable_kernelIntegrand s ξ).comp (measurable_const_smul r)
  have h2 := lintegral_comp_smul_space
      (fun u : Space ↦ ENNReal.ofReal (‖Complex.exp (Complex.I * ((⟪ξ, u⟫ : ℝ) : ℂ)) - 1‖ ^ 2) *
        fractionalRadialKernel s u) hr.ne'
  rw [h1, lintegral_const_mul _ hmeas,
    show (∫⁻ h : Space,
        ENNReal.ofReal (‖Complex.exp (Complex.I * ((⟪ξ, r • h⟫ : ℝ) : ℂ)) - 1‖ ^ 2) *
          fractionalRadialKernel s (r • h))
        = ENNReal.ofReal |(r ^ 3)⁻¹| * kernelIntegral s ξ from h2,
    ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
  congr 2
  rw [abs_of_pos (by positivity), ← Real.rpow_natCast r 3, ← Real.rpow_neg hr.le,
    ← Real.rpow_add hr]
  norm_num

/-- `03-torus.tex:66-67`: rotation and dilation identify the directional
integral with `c_s |ξ|^{2s}`. -/
theorem kernelIntegral_eq (s : ℝ) (hs : 0 < s) (ξ : Space) :
    kernelIntegral s ξ = ENNReal.ofReal (‖ξ‖ ^ (2 * s)) * cFrac s := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have hzero : kernelIntegral s 0 = 0 := by
      unfold kernelIntegral
      refine (lintegral_eq_zero_iff (measurable_kernelIntegrand s 0)).2 ?_
      filter_upwards with h
      simp
    rw [hzero, norm_zero, Real.zero_rpow (by positivity), ENNReal.ofReal_zero, zero_mul]
  · have hr : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hnorm : ‖(‖ξ‖ : ℝ) • coordinateVector 0‖ = ‖ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, coordinateVector,
        PiLp.norm_single]
      simp
    have hrefl : ((ℝ ∙ ((‖ξ‖ : ℝ) • coordinateVector 0 - ξ))ᗮ).reflection
        ((‖ξ‖ : ℝ) • coordinateVector 0) = ξ := Submodule.reflection_sub hnorm
    calc kernelIntegral s ξ
        = kernelIntegral s
            (((ℝ ∙ ((‖ξ‖ : ℝ) • coordinateVector 0 - ξ))ᗮ).reflection
              ((‖ξ‖ : ℝ) • coordinateVector 0)) := by
          rw [hrefl]
      _ = kernelIntegral s ((‖ξ‖ : ℝ) • coordinateVector 0) := kernelIntegral_isometry _ _ _
      _ = ENNReal.ofReal (‖ξ‖ ^ (2 * s)) * kernelIntegral s (coordinateVector 0) :=
          kernelIntegral_smul s hr _
      _ = ENNReal.ofReal (‖ξ‖ ^ (2 * s)) * cFrac s := by rw [cFrac_eq_kernelIntegral]

/-! ## 2. Finiteness of the constant -/

theorem norm_exp_I_mul_sub_one_le_two (t : ℝ) :
    ‖Complex.exp (Complex.I * (t : ℂ)) - 1‖ ≤ 2 := by
  have h1 : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  calc ‖Complex.exp (Complex.I * (t : ℂ)) - 1‖
      ≤ ‖Complex.exp (Complex.I * (t : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [h1]; norm_num

theorem norm_exp_I_mul_sub_one_le_norm {h : Space} (hh : ‖h‖ ≤ 1) :
    ‖Complex.exp (Complex.I * ((h 0 : ℝ) : ℂ)) - 1‖ ≤ 2 * ‖h‖ := by
  have hc : ‖h 0‖ ≤ ‖h‖ := PiLp.norm_apply_le h 0
  have hb : ‖Complex.I * ((h 0 : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    exact hc.trans hh
  have hcomp := Complex.norm_exp_sub_one_le hb
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real] at hcomp
  exact hcomp.trans (by linarith)

theorem kernel_integrand_le_near (s : ℝ) {h : Space} (hh : ‖h‖ ≤ 1) :
    ENNReal.ofReal (‖Complex.exp (Complex.I * ((h 0 : ℝ) : ℂ)) - 1‖ ^ 2) *
      fractionalRadialKernel s h ≤ ENNReal.ofReal (4 * ‖h‖ ^ (-(1 + 2 * s))) := by
  rcases eq_or_lt_of_le (norm_nonneg h) with h0 | hpos
  · have hz : h = 0 := norm_eq_zero.1 h0.symm
    subst hz
    simp
  · unfold fractionalRadialKernel
    rw [ENNReal.ofReal_rpow_of_pos hpos, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb := norm_exp_I_mul_sub_one_le_norm hh
    have hsq : ‖Complex.exp (Complex.I * ((h 0 : ℝ) : ℂ)) - 1‖ ^ 2 ≤ 4 * ‖h‖ ^ (2 : ℕ) := by
      have := mul_self_le_mul_self (norm_nonneg _) hb
      nlinarith [norm_nonneg (Complex.exp (Complex.I * ((h 0 : ℝ) : ℂ)) - 1), norm_nonneg h]
    have hker : (0 : ℝ) < ‖h‖ ^ (-(3 + 2 * s)) := Real.rpow_pos_of_pos hpos _
    calc ‖Complex.exp (Complex.I * ((h 0 : ℝ) : ℂ)) - 1‖ ^ 2 * ‖h‖ ^ (-(3 + 2 * s))
        ≤ (4 * ‖h‖ ^ (2 : ℕ)) * ‖h‖ ^ (-(3 + 2 * s)) := by
          exact mul_le_mul_of_nonneg_right hsq hker.le
      _ = 4 * ‖h‖ ^ (-(1 + 2 * s)) := by
          rw [mul_assoc, ← Real.rpow_natCast ‖h‖ 2, ← Real.rpow_add hpos]
          norm_num
          congr 1
          ring

theorem kernel_integrand_le_far (s : ℝ) (hs : 0 < s) {h : Space} (hh : 1 ≤ ‖h‖) :
    ENNReal.ofReal (‖Complex.exp (Complex.I * ((h 0 : ℝ) : ℂ)) - 1‖ ^ 2) *
      fractionalRadialKernel s h ≤
      ENNReal.ofReal (4 * 2 ^ (3 + 2 * s) * (1 + ‖h‖) ^ (-(3 + 2 * s))) := by
  have hpos : (0 : ℝ) < ‖h‖ := lt_of_lt_of_le zero_lt_one hh
  have ha : (0 : ℝ) < 3 + 2 * s := by linarith
  unfold fractionalRadialKernel
  rw [ENNReal.ofReal_rpow_of_pos hpos, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq : ‖Complex.exp (Complex.I * ((h 0 : ℝ) : ℂ)) - 1‖ ^ 2 ≤ 4 := by
    have hb := norm_exp_I_mul_sub_one_le_two (h 0)
    nlinarith [norm_nonneg (Complex.exp (Complex.I * ((h 0 : ℝ) : ℂ)) - 1)]
  have hker : (0 : ℝ) < ‖h‖ ^ (-(3 + 2 * s)) := Real.rpow_pos_of_pos hpos _
  have hhalf : (1 + ‖h‖) / 2 ≤ ‖h‖ := by linarith
  have hhalfpos : (0 : ℝ) < (1 + ‖h‖) / 2 := by linarith
  have hmono : ‖h‖ ^ (-(3 + 2 * s)) ≤ ((1 + ‖h‖) / 2) ^ (-(3 + 2 * s)) :=
    Real.rpow_le_rpow_of_nonpos hhalfpos hhalf (by linarith)
  have h2a : ((2 : ℝ)⁻¹) ^ (-(3 + 2 * s)) = 2 ^ (3 + 2 * s) := by
    rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
  have hsplit : ((1 + ‖h‖) / 2) ^ (-(3 + 2 * s)) =
      2 ^ (3 + 2 * s) * (1 + ‖h‖) ^ (-(3 + 2 * s)) := by
    rw [div_eq_mul_inv, Real.mul_rpow (by linarith) (by norm_num), h2a]
    ring
  calc ‖Complex.exp (Complex.I * ((h 0 : ℝ) : ℂ)) - 1‖ ^ 2 * ‖h‖ ^ (-(3 + 2 * s))
      ≤ 4 * ‖h‖ ^ (-(3 + 2 * s)) := mul_le_mul_of_nonneg_right hsq hker.le
    _ ≤ 4 * (2 ^ (3 + 2 * s) * (1 + ‖h‖) ^ (-(3 + 2 * s))) := by
        rw [← hsplit]
        exact mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = 4 * 2 ^ (3 + 2 * s) * (1 + ‖h‖) ^ (-(3 + 2 * s)) := by ring

/-- `03-torus.tex:36-39`: the paper constant is finite for `0 < s < 1`. -/
theorem cFrac_lt_top (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : cFrac s < ⊤ := by
  have hmeasA : MeasurableSet (Metric.ball (0 : Space) 1) := measurableSet_ball
  have hsplit := lintegral_add_compl (μ := (volume : Measure Space))
    (fun h : Space ↦ ENNReal.ofReal (‖Complex.exp (Complex.I * ((h 0 : ℝ) : ℂ)) - 1‖ ^ 2) *
      fractionalRadialKernel s h) hmeasA
  rw [cFrac, ← hsplit]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · have hbound : ∫⁻ h in Metric.ball (0 : Space) 1,
        ENNReal.ofReal (‖Complex.exp (Complex.I * ((h 0 : ℝ) : ℂ)) - 1‖ ^ 2) *
          fractionalRadialKernel s h ≤
        ∫⁻ h in Metric.ball (0 : Space) 1, ENNReal.ofReal (4 * ‖h‖ ^ (-(1 + 2 * s))) := by
      refine setLIntegral_mono_ae (Measurable.aemeasurable (by measurability)) ?_
      filter_upwards with h hh
      exact kernel_integrand_le_near s (mem_ball_zero_iff.1 hh).le
    refine lt_of_le_of_lt hbound ?_
    have hint : IntegrableOn (fun h : Space ↦ 4 * ‖h‖ ^ (-(1 + 2 * s)))
        (Metric.ball (0 : Space) 1) volume := by
      refine integrableOn_ball_of_norm_le_rpow (μ := (volume : Measure Space))
        (by simp) (C := 4) (α := 1 + 2 * s)
        (by rw [finrank_euclideanSpace_fin]; push_cast; linarith) ?_
        (Measurable.aestronglyMeasurable (by measurability))
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hfin := hint.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm,
      lintegral_enorm_of_nonneg (fun x ↦ by positivity)] at hfin
    exact hfin
  · have hbound : ∫⁻ h in (Metric.ball (0 : Space) 1)ᶜ,
        ENNReal.ofReal (‖Complex.exp (Complex.I * ((h 0 : ℝ) : ℂ)) - 1‖ ^ 2) *
          fractionalRadialKernel s h ≤
        ∫⁻ h : Space, ENNReal.ofReal
          (4 * 2 ^ (3 + 2 * s) * (1 + ‖h‖) ^ (-(3 + 2 * s))) := by
      refine le_trans (setLIntegral_mono_ae (Measurable.aemeasurable (by measurability)) ?_)
        (setLIntegral_le_lintegral _ _)
      filter_upwards with h hh
      refine kernel_integrand_le_far s hs0 ?_
      have hnb : ¬ ‖h‖ < 1 := by simpa [mem_ball_zero_iff] using hh
      exact not_lt.1 hnb
    refine lt_of_le_of_lt hbound ?_
    have hc : (0 : ℝ) ≤ 4 * 2 ^ (3 + 2 * s) := by positivity
    have hrw : ∀ h : Space, ENNReal.ofReal (4 * 2 ^ (3 + 2 * s) * (1 + ‖h‖) ^ (-(3 + 2 * s))) =
        ENNReal.ofReal (4 * 2 ^ (3 + 2 * s)) *
          ENNReal.ofReal ((1 + ‖h‖) ^ (-(3 + 2 * s))) := fun h ↦ ENNReal.ofReal_mul hc
    rw [lintegral_congr hrw, lintegral_const_mul _ (by measurability)]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact finite_integral_one_add_norm (E := Space) (μ := (volume : Measure Space))
      (by rw [finrank_euclideanSpace_fin]; push_cast; linarith)

/-! ## 3. The half-open representative of the fundamental cube tiles space -/

/-- `03-torus.tex:57-59`: the half-open representative of `fundamentalCube`.
It differs from `fundamentalCube` by a Lebesgue null set and tiles `R^3`
exactly under the unit lattice. -/
def halfOpenCube : Set Space := {x : Space | ∀ i : Fin 3, x i ∈ Ico (0 : ℝ) 1}

theorem latticeVector_apply (n : PeriodicFrequency) (i : Fin 3) :
    latticeVector n i = (n i : ℝ) := rfl

theorem measurableSet_halfOpenCube : MeasurableSet halfOpenCube := by
  have hset : halfOpenCube = ⋂ i : Fin 3, (fun x : Space ↦ x i) ⁻¹' Ico (0 : ℝ) 1 := by
    ext x
    simp [halfOpenCube]
  rw [hset]
  refine MeasurableSet.iInter fun i ↦ ?_
  exact measurableSet_Ico.preimage (by measurability)

/-- Exactly one lattice translate of the half-open cube contains each point. -/
theorem mem_halfOpenCube_iff (x : Space) (n : PeriodicFrequency) :
    x - latticeVector n ∈ halfOpenCube ↔ n = fun i ↦ ⌊x i⌋ := by
  constructor
  · intro h
    funext i
    have hi := h i
    rw [mem_Ico] at hi
    have h1 : ((n i : ℤ) : ℝ) ≤ x i := by
      have := hi.1
      have hv : (x - latticeVector n) i = x i - (n i : ℝ) := by
        simp [latticeVector_apply]
      rw [hv] at this
      linarith
    have h2 : x i < ((n i : ℤ) : ℝ) + 1 := by
      have := hi.2
      have hv : (x - latticeVector n) i = x i - (n i : ℝ) := by
        simp [latticeVector_apply]
      rw [hv] at this
      linarith
    exact (Int.floor_eq_iff.2 ⟨h1, h2⟩).symm
  · rintro rfl
    intro i
    have hv : (x - latticeVector fun i ↦ ⌊x i⌋) i = x i - ((⌊x i⌋ : ℤ) : ℝ) := by
      simp [latticeVector_apply]
    rw [hv, mem_Ico]
    exact ⟨by linarith [Int.floor_le (x i)], by linarith [Int.lt_floor_add_one (x i)]⟩

theorem tsum_indicator_halfOpenCube (x : Space) :
    ∑' n : PeriodicFrequency,
      halfOpenCube.indicator (fun _ ↦ (1 : ℝ≥0∞)) (x - latticeVector n) = 1 := by
  classical
  have hsingle : ∀ n : PeriodicFrequency, n ≠ (fun i ↦ ⌊x i⌋) →
      halfOpenCube.indicator (fun _ ↦ (1 : ℝ≥0∞)) (x - latticeVector n) = 0 := by
    intro n hn
    rw [Set.indicator_apply_eq_zero]
    intro hmem
    exact absurd ((mem_halfOpenCube_iff x n).1 hmem) hn
  rw [tsum_eq_single (fun i ↦ ⌊x i⌋) hsingle,
    Set.indicator_of_mem ((mem_halfOpenCube_iff x _).2 rfl)]

theorem measurable_indicator_shift (n : PeriodicFrequency) :
    Measurable (fun x : Space ↦
      halfOpenCube.indicator (fun _ ↦ (1 : ℝ≥0∞)) (x - latticeVector n)) :=
  (measurable_const.indicator measurableSet_halfOpenCube).comp
    (measurable_id.sub_const (latticeVector n))

/-- Single-copy unfolding: the whole-space integral of a nonnegative function
is the lattice sum of its integrals over the fundamental cube. -/
theorem lintegral_eq_tsum_halfOpenCube {g : Space → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x : Space, g x
      = ∑' n : PeriodicFrequency, ∫⁻ x in halfOpenCube, g (x + latticeVector n) := by
  have key : ∀ n : PeriodicFrequency,
      ∫⁻ x in halfOpenCube, g (x + latticeVector n)
        = ∫⁻ x : Space,
            halfOpenCube.indicator (fun _ ↦ (1 : ℝ≥0∞)) (x - latticeVector n) * g x := by
    intro n
    rw [← lintegral_indicator measurableSet_halfOpenCube]
    have h1 := lintegral_add_right_eq_self (μ := (volume : Measure Space))
      (fun x : Space ↦
        halfOpenCube.indicator (fun _ ↦ (1 : ℝ≥0∞)) (x - latticeVector n) * g x)
      (latticeVector n)
    rw [← h1]
    refine lintegral_congr fun y ↦ ?_
    simp only [add_sub_cancel_right]
    by_cases hy : y ∈ halfOpenCube <;> simp [hy]
  calc ∫⁻ x : Space, g x
      = ∫⁻ x : Space, (∑' n : PeriodicFrequency,
          halfOpenCube.indicator (fun _ ↦ (1 : ℝ≥0∞)) (x - latticeVector n)) * g x := by
        refine lintegral_congr fun x ↦ ?_
        rw [tsum_indicator_halfOpenCube x, one_mul]
    _ = ∫⁻ x : Space, ∑' n : PeriodicFrequency,
          halfOpenCube.indicator (fun _ ↦ (1 : ℝ≥0∞)) (x - latticeVector n) * g x := by
        refine lintegral_congr fun x ↦ ?_
        rw [ENNReal.tsum_mul_right]
    _ = ∑' n : PeriodicFrequency, ∫⁻ x : Space,
          halfOpenCube.indicator (fun _ ↦ (1 : ℝ≥0∞)) (x - latticeVector n) * g x :=
        lintegral_tsum fun n ↦ ((measurable_indicator_shift n).mul hg).aemeasurable
    _ = ∑' n : PeriodicFrequency, ∫⁻ x in halfOpenCube, g (x + latticeVector n) :=
        tsum_congr fun n ↦ (key n).symm

/-! ## 4. Cube, Haar, and Fourier bridges -/

theorem toSpace_preimage_fundamentalCube :
    (toSpace : Coords → Space) ⁻¹' fundamentalCube = Icc (0 : Coords) 1 := by
  ext y
  constructor
  · intro hy
    refine ⟨fun i ↦ (hy i).1, fun i ↦ (hy i).2⟩
  · intro hy i
    exact ⟨hy.1 i, hy.2 i⟩

theorem ofLp_preimage_fundamentalCube :
    (WithLp.ofLp : Space → Coords) ⁻¹' (Icc (0 : Coords) 1) = fundamentalCube := by
  ext x
  constructor
  · intro hx i
    exact ⟨hx.1 i, hx.2 i⟩
  · intro hx
    exact ⟨fun i ↦ (hx i).1, fun i ↦ (hx i).2⟩

theorem ofLp_preimage_halfOpenCube :
    (WithLp.ofLp : Space → Coords) ⁻¹' (univ.pi fun _ : Fin 3 ↦ Ico (0 : ℝ) 1) =
      halfOpenCube := by
  ext x
  simp [halfOpenCube]

/-- The closed and half-open representatives of the fundamental cube agree a.e. -/
theorem fundamentalCube_ae_eq_halfOpenCube :
    fundamentalCube =ᵐ[(volume : Measure Space)] halfOpenCube := by
  have hqmp : Measure.QuasiMeasurePreserving (WithLp.ofLp : Space → Coords) volume volume :=
    (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving
  have hpi : (univ.pi fun _ : Fin 3 ↦ Ico (0 : ℝ) 1) =ᵐ[(volume : Measure Coords)]
      Icc (0 : Coords) 1 := by
    have h := Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin 3 ↦ (volume : Measure ℝ))
      (f := (0 : Coords)) (g := (1 : Coords))
    simp only [Pi.zero_apply, Pi.one_apply] at h
    rw [volume_pi]
    exact h
  have hae := hqmp.preimage_ae_eq hpi
  rw [ofLp_preimage_halfOpenCube, ofLp_preimage_fundamentalCube] at hae
  exact hae.symm

/-- Integration of a continuous nonnegative field over the fixed cube is the
`ENNReal` form of the existing physical cube integral. -/
theorem lintegral_fundamentalCube_ofReal {F : Space → ℝ} (hF : Continuous F)
    (hpos : ∀ x, 0 ≤ F x) :
    ∫⁻ x in fundamentalCube, ENNReal.ofReal (F x) ∂(volume : Measure Space)
      = ENNReal.ofReal (cubeIntegral F) := by
  have hmp : MeasurePreserving (toSpace : Coords → Space) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have hemb : MeasurableEmbedding (toSpace : Coords → Space) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
  have h1 := hmp.setLIntegral_comp_preimage_emb hemb
    (fun x ↦ ENNReal.ofReal (F x)) fundamentalCube
  have hcont : Continuous fun y : Coords ↦ F (toSpace y) := hF.comp toSpace.continuous
  have hInt : Integrable (fun y : Coords ↦ F (toSpace y))
      (volume.restrict (Icc (0 : Coords) 1)) :=
    ContinuousOn.integrableOn_compact isCompact_Icc hcont.continuousOn
  rw [← h1, toSpace_preimage_fundamentalCube,
    ← ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun y ↦ hpos _)]
  rfl

/-- The same integral over the half-open representative. -/
theorem lintegral_halfOpenCube_ofReal {F : Space → ℝ} (hF : Continuous F)
    (hpos : ∀ x, 0 ≤ F x) :
    ∫⁻ x in halfOpenCube, ENNReal.ofReal (F x) ∂(volume : Measure Space)
      = ENNReal.ofReal (cubeIntegral F) := by
  rw [← setLIntegral_congr fundamentalCube_ae_eq_halfOpenCube]
  exact lintegral_fundamentalCube_ofReal hF hpos

/-! ## 5. Fourier coefficients of a translate -/

theorem periodicTorusMeasure_isAddRightInvariant :
    (periodicTorusMeasure).IsAddRightInvariant := by
  change (Measure.pi fun _ : Fin 3 ↦ AddCircle.haarAddCircle).IsAddRightInvariant
  infer_instance

/-- The quotient projection of a physical point to the unit torus. -/
def torusPoint (x : Space) : PeriodicTorus := fun i ↦ ((x i : ℝ) : UnitAddCircle)

theorem torusPoint_sub (x a : Space) :
    torusPoint (x - a) = torusPoint x - torusPoint a := rfl

theorem torusLift_torusPoint {E : Type*} [Add E] {g : Space → E}
    (hg : IsPeriodicSpatial g) (x : Space) : torusLift g (torusPoint x) = g x :=
  torusLift_apply_of_periodic hg x

theorem torusPoint_torusRepr (z : PeriodicTorus) :
    torusPoint (toSpace ((UnitAddTorus.measurableEquivPiIoc (0 : Coords)) z).val) = z :=
  (UnitAddTorus.measurableEquivPiIoc (0 : Coords)).symm_apply_apply z

theorem torusLift_sub_shift {E : Type*} [Add E] {g : Space → E}
    (hg : IsPeriodicSpatial g) (a : Space) (z : PeriodicTorus) :
    torusLift (fun x ↦ g (x - a)) z = torusLift g (z - torusPoint a) := by
  have h1 : z - torusPoint a =
      torusPoint (toSpace ((UnitAddTorus.measurableEquivPiIoc (0 : Coords)) z).val - a) := by
    rw [torusPoint_sub, torusPoint_torusRepr]
  rw [h1, torusLift_torusPoint hg]
  rfl

theorem mFourier_add_point (n : PeriodicFrequency) (w v : PeriodicTorus) :
    UnitAddTorus.mFourier n (w + v) =
      UnitAddTorus.mFourier n w * UnitAddTorus.mFourier n v := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simp [fourier_apply, ← Circle.coe_mul, ← AddCircle.toCircle_add, smul_add]

/-- `03-torus.tex:60-64`: translating a periodic field multiplies its Fourier
coefficients by the corresponding character. -/
theorem periodicFourierCoeff_shift {g : Space → ℂ} (hg : IsPeriodicSpatial g)
    (a : Space) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ g (x - a)) k =
      NSFormalization.Paper1.periodicCharacter (-k) a * periodicFourierCoeff g k := by
  have _hinv := periodicTorusMeasure_isAddRightInvariant
  have hchar : NSFormalization.Paper1.periodicCharacter (-k) a
      = UnitAddTorus.mFourier (-k) (torusPoint a) :=
    NSFormalization.Paper1.periodicCharacter_eq_mFourier (-k) a
  change UnitAddTorus.mFourierCoeff (torusLift (fun x ↦ g (x - a))) k =
    _ * UnitAddTorus.mFourierCoeff (torusLift g) k
  unfold UnitAddTorus.mFourierCoeff
  rw [hchar]
  calc ∫ z : PeriodicTorus, UnitAddTorus.mFourier (-k) z • torusLift (fun x ↦ g (x - a)) z
        ∂periodicTorusMeasure
      = ∫ z : PeriodicTorus, UnitAddTorus.mFourier (-k) z • torusLift g (z - torusPoint a)
        ∂periodicTorusMeasure := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
        dsimp only
        rw [torusLift_sub_shift hg]
    _ = ∫ w : PeriodicTorus, UnitAddTorus.mFourier (-k) (w + torusPoint a) •
          torusLift g (w + torusPoint a - torusPoint a) ∂periodicTorusMeasure :=
        (integral_add_right_eq_self
          (fun z : PeriodicTorus ↦ UnitAddTorus.mFourier (-k) z • torusLift g (z - torusPoint a))
          (torusPoint a)).symm
    _ = ∫ w : PeriodicTorus, UnitAddTorus.mFourier (-k) (torusPoint a) •
          (UnitAddTorus.mFourier (-k) w • torusLift g w) ∂periodicTorusMeasure := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
        dsimp only
        rw [mFourier_add_point, add_sub_cancel_right, smul_smul, mul_comm]
    _ = UnitAddTorus.mFourier (-k) (torusPoint a) *
          ∫ w : PeriodicTorus, UnitAddTorus.mFourier (-k) w • torusLift g w
            ∂periodicTorusMeasure := by
        rw [integral_smul]
        rfl

/-! ## 6. Parseval for the difference field -/

theorem continuous_component {v : SpatialField} (hv : Continuous v) (i : Fin 3) :
    Continuous (fun x : Space ↦ ((v x i : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).comp hv)

theorem integrable_torusLift_component {v : SpatialField} (hv : Continuous v) (i : Fin 3) :
    Integrable (torusLift (fun x : Space ↦ ((v x i : ℝ) : ℂ))) periodicTorusMeasure :=
  (NSFormalization.Paper1.memLp_torusLift (continuous_component hv i) 1).integrable le_rfl

/-- Vector Parseval on the fixed cube. -/
theorem cubeIntegral_norm_sq_eq_tsum {v : SpatialField} (hv : Continuous v) :
    cubeIntegral (fun x ↦ ‖v x‖ ^ 2)
      = ∑' k : PeriodicFrequency, ∑ i : Fin 3,
          ‖periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k‖ ^ 2 := by
  have hsum : ∀ i : Fin 3, HasSum
      (fun k ↦ ‖periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k‖ ^ 2)
      (cubeIntegral (fun x ↦ ‖((v x i : ℝ) : ℂ)‖ ^ 2)) := fun i ↦
    NSFormalization.Paper1.hasSum_sq_periodicFourierCoeff _ (continuous_component hv i)
  have htot := hasSum_sum (f := fun (i : Fin 3) (k : PeriodicFrequency) ↦
      ‖periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k‖ ^ 2)
    (s := (Finset.univ : Finset (Fin 3))) (fun i _ ↦ hsum i)
  have hcube : ∑ i : Fin 3, cubeIntegral (fun x ↦ ‖((v x i : ℝ) : ℂ)‖ ^ 2)
      = cubeIntegral (fun x ↦ ‖v x‖ ^ 2) := by
    rw [← cubeIntegral_sum]
    · refine congrArg cubeIntegral ?_
      funext x
      rw [PiLp.norm_sq_eq_of_L2]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [Complex.norm_real]
    · intro i _
      exact ((continuous_component hv i).norm.pow 2)
  rw [← hcube, ← htot.tsum_eq]

/-- `03-torus.tex:60-64`: Parseval for the shifted difference of a smooth
periodic field. -/
theorem cubeIntegral_diff_norm_sq {f : SpatialField} (hf : IsPeriodicSpatial f)
    (hfc : Continuous f) (h : Space) :
    cubeIntegral (fun x ↦ ‖f x - f (x - h)‖ ^ 2)
      = ∑' k : PeriodicFrequency,
          ‖1 - NSFormalization.Paper1.periodicCharacter (-k) h‖ ^ 2 *
            ∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2 := by
  have hvc : Continuous (fun x : Space ↦ f x - f (x - h)) :=
    hfc.sub (hfc.comp (continuous_id.sub continuous_const))
  rw [cubeIntegral_norm_sq_eq_tsum (v := fun x : Space ↦ f x - f (x - h)) hvc]
  refine tsum_congr fun k ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hgp : IsPeriodicSpatial (fun x : Space ↦ ((f x i : ℝ) : ℂ)) := by
    intro x j
    dsimp only
    rw [hf x j]
  have hcoeff : periodicFourierCoeff
      (fun x ↦ (((fun y : Space ↦ f y - f (y - h)) x i : ℝ) : ℂ)) k
      = (1 - NSFormalization.Paper1.periodicCharacter (-k) h) *
        periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k := by
    have hsub : periodicFourierCoeff
        (fun x ↦ (((fun y : Space ↦ f y - f (y - h)) x i : ℝ) : ℂ)) k
        = periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k -
          periodicFourierCoeff (fun x ↦ ((f (x - h) i : ℝ) : ℂ)) k := by
      have := periodicFourierCoeff_sub
        (f := fun x : Space ↦ ((f x i : ℝ) : ℂ))
        (g := fun x : Space ↦ ((f (x - h) i : ℝ) : ℂ))
        (integrable_torusLift_component hfc i)
        (integrable_torusLift_component
          (hfc.comp (continuous_id.sub continuous_const)) i) k
      rw [← this]
      refine congrArg (fun F ↦ periodicFourierCoeff F k) ?_
      funext x
      have hx : ((fun y : Space ↦ f y - f (y - h)) x) i = f x i - f (x - h) i := rfl
      rw [hx]
      push_cast
      ring
    rw [hsub, periodicFourierCoeff_shift (g := fun x : Space ↦ ((f x i : ℝ) : ℂ)) hgp h k]
    ring
  rw [hcoeff, norm_mul, mul_pow]

/-! ## 7. The homogeneous datum of a smooth periodic field -/

theorem measurable_torusLift_space {v : SpatialField} (hv : Continuous v) :
    Measurable (torusLift v) :=
  (hv.comp toSpace.continuous).measurable.comp
    (measurable_subtype_coe.comp (UnitAddTorus.measurableEquivPiIoc (0 : Coords)).measurable)

theorem memLp_torusLift_space {v : SpatialField} (hv : Continuous v) (q : ℝ≥0∞) :
    MemLp (torusLift v) q periodicTorusMeasure := by
  obtain ⟨M, hM⟩ := ((isCompact_Icc : IsCompact (Icc (0 : Coords) 1)).image
    (hv.comp toSpace.continuous)).isBounded.exists_norm_le
  apply MemLp.of_bound (measurable_torusLift_space hv).aestronglyMeasurable M
  refine Filter.Eventually.of_forall fun z ↦ ?_
  apply hM
  refine ⟨((UnitAddTorus.measurableEquivPiIoc (0 : Coords)) z).val, ?_, rfl⟩
  constructor <;> intro i
  · exact (((UnitAddTorus.measurableEquivPiIoc (0 : Coords)) z).property i).1.le
  · simpa using (((UnitAddTorus.measurableEquivPiIoc (0 : Coords)) z).property i).2

theorem integrable_torusLift_space {v : SpatialField} (hv : Continuous v) :
    Integrable (torusLift v) periodicTorusMeasure :=
  (memLp_torusLift_space hv 1).integrable le_rfl

/-- `01-introduction.tex:105-107`: the angular frequency vector `2πk`. -/
def angularVector (k : PeriodicFrequency) : Space := (2 * Real.pi) • latticeVector k

theorem norm_latticeVector_sq (k : PeriodicFrequency) :
    ‖latticeVector k‖ ^ 2 = ∑ i : Fin 3, ((k i : ℤ) : ℝ) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show ((latticeVector k).ofLp i) = ((k i : ℤ) : ℝ) from rfl, Real.norm_eq_abs, sq_abs]

theorem norm_angularVector_sq (k : PeriodicFrequency) :
    ‖angularVector k‖ ^ 2 = periodicAngularFrequencySq k := by
  unfold angularVector periodicAngularFrequencySq
  rw [norm_smul, Real.norm_eq_abs, mul_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi), norm_latticeVector_sq]
  ring

theorem homogeneousDatumWeight_nonneg (s : ℝ) (k : PeriodicFrequency) :
    0 ≤ homogeneousDatumWeight s k := by
  unfold homogeneousDatumWeight
  split_ifs with hk
  · exact le_rfl
  · exact Real.rpow_nonneg (by unfold periodicAngularFrequencySq; positivity) _

theorem homogeneousDatumWeight_neg (s : ℝ) (k : PeriodicFrequency) :
    homogeneousDatumWeight s (-k) = homogeneousDatumWeight s k := by
  have hsum : periodicAngularFrequencySq (-k) = periodicAngularFrequencySq k := by
    unfold periodicAngularFrequencySq
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have : ((-k) i : ℤ) = -(k i) := rfl
    rw [this]
    push_cast
    ring
  unfold homogeneousDatumWeight
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (neg_eq_zero.1 h1) h2
  · exact absurd (by rw [h2]; simp) h1
  · rw [hsum]

theorem homogeneousDatumWeight_sq_of_ne (s : ℝ) {k : PeriodicFrequency} (hk : k ≠ 0) :
    homogeneousDatumWeight s k ^ 2 = ‖angularVector k‖ ^ (2 * s) := by
  have hP : (0 : ℝ) ≤ periodicAngularFrequencySq k := by
    unfold periodicAngularFrequencySq; positivity
  have h1 : homogeneousDatumWeight s k = (periodicAngularFrequencySq k) ^ (s / 2) := by
    unfold homogeneousDatumWeight
    split_ifs with h
    · exact absurd h hk
    · rfl
  calc homogeneousDatumWeight s k ^ 2
      = ((periodicAngularFrequencySq k) ^ (s / 2)) ^ (2 : ℕ) := by rw [h1]
    _ = (periodicAngularFrequencySq k) ^ s := by
        rw [← Real.rpow_natCast ((periodicAngularFrequencySq k) ^ (s / 2)) 2,
          ← Real.rpow_mul hP]
        norm_num
    _ = (‖angularVector k‖ ^ (2 : ℕ)) ^ s := by rw [norm_angularVector_sq]
    _ = ‖angularVector k‖ ^ (2 * s) := by
        rw [Real.rpow_mul (norm_nonneg _) 2 s]
        norm_num

theorem contDiff_component {f : SpatialField} (hfs : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x : Space ↦ ((f x i : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hfs)

theorem isPeriodicSpatial_component {f : SpatialField} (hfp : IsPeriodicSpatial f) (i : Fin 3) :
    IsPeriodicSpatial (fun x : Space ↦ ((f x i : ℝ) : ℂ)) := by
  intro x j
  dsimp only
  rw [hfp x j]

theorem summable_homogeneous_sq {s : ℝ} (hs : 0 ≤ s) {f : SpatialField}
    (hfp : IsPeriodicSpatial f) (hfs : ContDiff ℝ ∞ f) (i : Fin 3) :
    Summable (fun k : PeriodicFrequency ↦
      homogeneousDatumWeight s k ^ 2 *
        ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2) := by
  have hmaj := summable_weighted_periodicFourierCoeff
    (isPeriodicSpatial_component hfp i) (contDiff_component hfs i) s
  refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_) hmaj
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  by_cases hk : k = 0
  · subst hk
    have : homogeneousDatumWeight s (0 : PeriodicFrequency) = 0 := by
      unfold homogeneousDatumWeight
      split_ifs with h
      · rfl
      · exact absurd rfl h
    rw [this]
    have hw : (1 : ℝ) ≤ periodicFrequencyWeight (0 : PeriodicFrequency) := by
      unfold periodicFrequencyWeight
      simp
    simpa using Real.rpow_nonneg (by linarith : (0:ℝ) ≤ periodicFrequencyWeight
      (0 : PeriodicFrequency)) s
  · rw [homogeneousDatumWeight_sq_of_ne s hk]
    have hxx : ‖angularVector k‖ ^ (2 * s) = (periodicAngularFrequencySq k) ^ s := by
      rw [← norm_angularVector_sq, ← Real.rpow_natCast ‖angularVector k‖ 2,
        ← Real.rpow_mul (norm_nonneg _)]
      norm_num
    rw [hxx]
    refine Real.rpow_le_rpow ?_ ?_ hs
    · unfold periodicAngularFrequencySq; positivity
    · unfold periodicAngularFrequencySq periodicFrequencyWeight; linarith

theorem homogeneousDatumWeight_zero (s : ℝ) :
    homogeneousDatumWeight s (0 : PeriodicFrequency) = 0 := by
  unfold homogeneousDatumWeight
  split_ifs with h
  · rfl
  · exact absurd rfl h

theorem periodicFourierCoeff_meanZeroPart {f : SpatialField} (hfc : Continuous f)
    (i : Fin 3) {k : PeriodicFrequency} (hk : k ≠ 0) :
    periodicFourierCoeff (fun x ↦ ((meanZeroPartT f x i : ℝ) : ℂ)) k
      = periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k := by
  have hEq : (fun x : Space ↦ ((meanZeroPartT f x i : ℝ) : ℂ))
      = fun x : Space ↦ ((f x i : ℝ) : ℂ) - (((meanT f) i : ℝ) : ℂ) := by
    funext x
    have hx : (meanZeroPartT f x) i = f x i - (meanT f) i := rfl
    rw [hx]
    push_cast
    ring
  rw [hEq, periodicFourierCoeff_sub (integrable_torusLift_component hfc i)
    (integrable_const _) k, periodicFourierCoeff_const]
  simp [hk]

theorem summable_homogeneous_total {s : ℝ} (hs : 0 ≤ s) {f : SpatialField}
    (hfp : IsPeriodicSpatial f) (hfs : ContDiff ℝ ∞ f) :
    Summable (fun k : PeriodicFrequency ↦ homogeneousDatumWeight s k ^ 2 *
      ∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2) := by
  have hsum := summable_sum (f := fun (i : Fin 3) (k : PeriodicFrequency) ↦
      homogeneousDatumWeight s k ^ 2 *
        ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2)
    (s := (Finset.univ : Finset (Fin 3))) (fun i _ ↦ summable_homogeneous_sq hs hfp hfs i)
  refine hsum.congr fun k ↦ ?_
  rw [Finset.mul_sum]

/-- Homogeneous data of the same field coincide. -/
theorem homogeneousDatum_unique {s : ℝ} {z : SpatialField} (A B : PeriodicSobolev s)
    (hA : IsPeriodicHomogeneousDatum s z A) (hB : IsPeriodicHomogeneousDatum s z B) : A = B := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  ext k
  rw [hA.2.2.2 i k, hB.2.2.2 i k]

/-- The squared norm of any datum with the explicit homogeneous coefficients. -/
theorem homogeneousDatum_norm_sq {s : ℝ} {f : SpatialField} (A : PeriodicSobolev s)
    (hA : ∀ (i : Fin 3) (k : PeriodicFrequency),
      A.1 i k = ((homogeneousDatumWeight s k : ℝ) : ℂ) *
        periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k)
    (hsumm : ∀ i : Fin 3, Summable (fun k : PeriodicFrequency ↦
      homogeneousDatumWeight s k ^ 2 *
        ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2)) :
    ‖A‖ ^ 2 = ∑' k : PeriodicFrequency, homogeneousDatumWeight s k ^ 2 *
      ∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2 := by
  have h1 : ‖A‖ ^ 2 = ∑ i : Fin 3, ‖A.1 i‖ ^ 2 := by
    change ‖A.1‖ ^ 2 = _
    exact PiLp.norm_sq_eq_of_L2 _ A.1
  have h2 : ∀ i : Fin 3, ‖A.1 i‖ ^ 2 = ∑' k : PeriodicFrequency, ‖A.1 i k‖ ^ 2 := by
    intro i
    have h3 := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (A.1 i)
    simpa using h3
  have hns : ∀ (i : Fin 3) (k : PeriodicFrequency), ‖A.1 i k‖ ^ 2 =
      homogeneousDatumWeight s k ^ 2 *
        ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2 := by
    intro i k
    rw [hA i k, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (homogeneousDatumWeight_nonneg s k)]
  rw [h1]
  simp_rw [h2, hns]
  rw [← Summable.tsum_finsetSum (fun i (_ : i ∈ Finset.univ) ↦ hsumm i)]
  refine tsum_congr fun k ↦ ?_
  rw [Finset.mul_sum]

set_option maxHeartbeats 400000 in
/-- `03-torus.tex:67-71`: the explicit homogeneous datum of the mean-free part
of a smooth periodic field, together with its squared norm. -/
theorem exists_homogeneous_datum {s : ℝ} (hs : 0 < s) {f : SpatialField}
    (hfp : IsPeriodicSpatial f) (hfs : ContDiff ℝ ∞ f) :
    ∃ A : PeriodicSobolev s, IsPeriodicHomogeneousDatum s (meanZeroPartT f) A ∧
      ‖A‖ ^ 2 = ∑' k : PeriodicFrequency, homogeneousDatumWeight s k ^ 2 *
        ∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2 := by
  classical
  have hfc : Continuous f := hfs.continuous
  have hzp : IsPeriodicSpatial (meanZeroPartT f) := by
    intro x j
    show f (x + coordinateVector j) - meanT f = f x - meanT f
    rw [hfp x j]
  have hzc : Continuous (meanZeroPartT f) := hfc.sub continuous_const
  have hzint : Integrable (torusLift (meanZeroPartT f)) periodicTorusMeasure :=
    integrable_torusLift_space hzc
  have hz0 : IsMeanZeroT (meanZeroPartT f) :=
    (mean_decomposition f hfp (integrable_torusLift_space hfc)).2
  have hcoeff : ∀ (i : Fin 3) (k : PeriodicFrequency),
      ((homogeneousDatumWeight s k : ℝ) : ℂ) *
          periodicFourierCoeff (fun x ↦ ((meanZeroPartT f x i : ℝ) : ℂ)) k
        = ((homogeneousDatumWeight s k : ℝ) : ℂ) *
          periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k := by
    intro i k
    by_cases hk : k = 0
    · subst hk
      rw [homogeneousDatumWeight_zero]
      simp
    · rw [periodicFourierCoeff_meanZeroPart hfc i hk]
  have hmem : ∀ i : Fin 3, Memℓp (fun k : PeriodicFrequency ↦
      ((homogeneousDatumWeight s k : ℝ) : ℂ) *
        periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k) 2 := by
    intro i
    have hsq : ∀ k : PeriodicFrequency,
        ‖((homogeneousDatumWeight s k : ℝ) : ℂ) *
            periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2 =
          homogeneousDatumWeight s k ^ 2 *
            ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2 := by
      intro k
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (homogeneousDatumWeight_nonneg s k)]
    have hsum2 : Summable (fun k : PeriodicFrequency ↦
        ‖((homogeneousDatumWeight s k : ℝ) : ℂ) *
          periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2) := by
      simpa only [← hsq] using summable_homogeneous_sq hs.le hfp hfs i
    apply memℓp_gen
    simpa using hsum2
  have hreal : (WithLp.toLp 2 (fun i ↦
      (⟨fun k : PeriodicFrequency ↦ ((homogeneousDatumWeight s k : ℝ) : ℂ) *
        periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k, hmem i⟩ : PeriodicScalarData)) :
      PeriodicVectorData) ∈ realPeriodicSubmodule := by
    intro i k
    show ((homogeneousDatumWeight s (-k) : ℝ) : ℂ) *
        periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) (-k) =
      star (((homogeneousDatumWeight s k : ℝ) : ℂ) *
        periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k)
    rw [homogeneousDatumWeight_neg, periodicFourierCoeff_real_neg (fun x ↦ f x i) k, star_mul']
    congr 1
    rw [Complex.star_def]
    exact (Complex.conj_ofReal _).symm
  refine ⟨⟨_, hreal⟩, ⟨hzp, hzint, hz0, ?_⟩,
    homogeneousDatum_norm_sq _ (fun i k ↦ rfl) (fun i ↦ summable_homogeneous_sq hs.le hfp hfs i)⟩
  intro i k
  show ((homogeneousDatumWeight s k : ℝ) : ℂ) *
      periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k = _
  rw [← hcoeff i k]
  rfl

set_option maxHeartbeats 400000 in
/-- `03-torus.tex:67-71`: the squared homogeneous `Ḣ^s(T³)` norm of the
mean-free part of a smooth periodic field in terms of its Fourier data. -/
theorem periodicHomogeneousENorm_sq_smooth {s : ℝ} (hs : 0 < s) {f : SpatialField}
    (hfp : IsPeriodicSpatial f) (hfs : ContDiff ℝ ∞ f) :
    periodicHomogeneousENorm s (meanZeroPartT f) ^ (2 : ℕ)
      = ∑' k : PeriodicFrequency, ENNReal.ofReal (homogeneousDatumWeight s k ^ 2 *
          ∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2) := by
  obtain ⟨A, hA, hAnorm⟩ := exists_homogeneous_datum hs hfp hfs
  have hnorm : periodicHomogeneousENorm s (meanZeroPartT f) = ‖A‖ₑ := by
    apply le_antisymm
    · exact iInf_le (fun B : {B : PeriodicSobolev s //
        IsPeriodicHomogeneousDatum s (meanZeroPartT f) B} ↦ ‖B.1‖ₑ) ⟨A, hA⟩
    · refine le_iInf fun B ↦ ?_
      rw [homogeneousDatum_unique B.1 A B.2 hA]
  rw [hnorm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), hAnorm]
  exact ENNReal.ofReal_tsum_of_nonneg (fun k ↦ by positivity)
    (summable_homogeneous_total hs.le hfp hfs)

/-! ## 8. The torus Gagliardo identity -/

theorem periodic_latticeVector {E : Type*} [Add E] {g : Space → E} (hg : IsPeriodicSpatial g)
    (x : Space) (n : PeriodicFrequency) : g (x + latticeVector n) = g x := by
  have h := periodic_shift_int hg x n
  have hvec : (∑ i : Fin 3, ((n i : ℤ) : ℝ) • coordinateVector i) = latticeVector n := by
    ext j
    simp [coordinateVector, latticeVector, Pi.single_apply]
  rwa [hvec] at h

theorem latticeVector_neg (n : PeriodicFrequency) :
    latticeVector (-n) = -latticeVector n := by
  ext j
  show (((-n) j : ℤ) : ℝ) = -(((n j : ℤ)) : ℝ)
  simp

theorem measurable_diffKernel {s : ℝ} {f : SpatialField} (hfc : Continuous f)
    (x a : Space) :
    Measurable (fun y : Space ↦ ENNReal.ofReal (‖f x - f y‖ ^ 2) *
      fractionalRadialKernel s ((x - y) + a)) := by
  refine Measurable.mul ?_ ((measurable_fractionalRadialKernel s).comp
    ((measurable_const.sub measurable_id).add_const a))
  exact ENNReal.measurable_ofReal.comp (((continuous_const.sub hfc).norm.pow 2).measurable)

/-- Single-copy unfolding of the periodized kernel in the inner integral. -/
theorem lintegral_cube_periodicKernel {s : ℝ} {f : SpatialField}
    (hfp : IsPeriodicSpatial f) (hfc : Continuous f) (x : Space) :
    ∫⁻ y in halfOpenCube, ENNReal.ofReal (‖f x - f y‖ ^ 2) * periodicKernel s (x - y)
      = ∫⁻ u : Space, ENNReal.ofReal (‖f x - f u‖ ^ 2) * fractionalRadialKernel s (x - u) := by
  have hmeas : Measurable (fun u : Space ↦
      ENNReal.ofReal (‖f x - f u‖ ^ 2) * fractionalRadialKernel s (x - u)) := by
    refine Measurable.mul ?_ ((measurable_fractionalRadialKernel s).comp
      (measurable_const.sub measurable_id))
    exact ENNReal.measurable_ofReal.comp (((continuous_const.sub hfc).norm.pow 2).measurable)
  calc ∫⁻ y in halfOpenCube, ENNReal.ofReal (‖f x - f y‖ ^ 2) * periodicKernel s (x - y)
      = ∫⁻ y in halfOpenCube, ∑' n : PeriodicFrequency,
          ENNReal.ofReal (‖f x - f y‖ ^ 2) *
            fractionalRadialKernel s ((x - y) + latticeVector n) := by
        refine lintegral_congr fun y ↦ ?_
        rw [periodicKernel, ENNReal.tsum_mul_left]
    _ = ∑' n : PeriodicFrequency, ∫⁻ y in halfOpenCube,
          ENNReal.ofReal (‖f x - f y‖ ^ 2) *
            fractionalRadialKernel s ((x - y) + latticeVector n) :=
        lintegral_tsum fun n ↦ (measurable_diffKernel hfc x (latticeVector n)).aemeasurable
    _ = ∑' n : PeriodicFrequency, ∫⁻ y in halfOpenCube,
          ENNReal.ofReal (‖f x - f y‖ ^ 2) *
            fractionalRadialKernel s ((x - y) + latticeVector (-n)) :=
        ((Equiv.neg PeriodicFrequency).tsum_eq (fun n ↦ ∫⁻ y in halfOpenCube,
          ENNReal.ofReal (‖f x - f y‖ ^ 2) *
            fractionalRadialKernel s ((x - y) + latticeVector n))).symm
    _ = ∑' n : PeriodicFrequency, ∫⁻ y in halfOpenCube,
          ENNReal.ofReal (‖f x - f (y + latticeVector n)‖ ^ 2) *
            fractionalRadialKernel s (x - (y + latticeVector n)) := by
        refine tsum_congr fun n ↦ lintegral_congr fun y ↦ ?_
        rw [periodic_latticeVector hfp y n, latticeVector_neg]
        congr 2
        abel
    _ = ∫⁻ u : Space, ENNReal.ofReal (‖f x - f u‖ ^ 2) *
          fractionalRadialKernel s (x - u) := (lintegral_eq_tsum_halfOpenCube hmeas).symm

theorem lintegral_whole_shift {s : ℝ} {f : SpatialField} (x : Space) :
    ∫⁻ u : Space, ENNReal.ofReal (‖f x - f u‖ ^ 2) * fractionalRadialKernel s (x - u)
      = ∫⁻ h : Space, ENNReal.ofReal (‖f x - f (x - h)‖ ^ 2) * fractionalRadialKernel s h := by
  have h1 := lintegral_sub_left_eq_self (μ := (volume : Measure Space))
    (fun u : Space ↦ ENNReal.ofReal (‖f x - f u‖ ^ 2) * fractionalRadialKernel s (x - u)) x
  rw [← h1]
  refine lintegral_congr fun h ↦ ?_
  rw [sub_sub_cancel]

theorem measurable_prod_diff {s : ℝ} {f : SpatialField} (hfc : Continuous f) :
    Measurable (fun p : Space × Space ↦
      ENNReal.ofReal (‖f p.1 - f (p.1 - p.2)‖ ^ 2) * fractionalRadialKernel s p.2) := by
  refine Measurable.mul ?_ ((measurable_fractionalRadialKernel s).comp measurable_snd)
  refine ENNReal.measurable_ofReal.comp ?_
  exact (((hfc.comp continuous_fst).sub
    (hfc.comp (continuous_fst.sub continuous_snd))).norm.pow 2).measurable

theorem measurable_diff_sq {f : SpatialField} (hfc : Continuous f) (h : Space) :
    Measurable (fun x : Space ↦ ENNReal.ofReal (‖f x - f (x - h)‖ ^ 2)) :=
  ENNReal.measurable_ofReal.comp
    ((hfc.sub (hfc.comp (continuous_id.sub continuous_const))).norm.pow 2).measurable

theorem lintegral_swap_diff {s : ℝ} {f : SpatialField} (hfc : Continuous f) :
    ∫⁻ x in halfOpenCube, ∫⁻ h : Space,
        ENNReal.ofReal (‖f x - f (x - h)‖ ^ 2) * fractionalRadialKernel s h
      = ∫⁻ h : Space, (∫⁻ x in halfOpenCube,
          ENNReal.ofReal (‖f x - f (x - h)‖ ^ 2)) * fractionalRadialKernel s h := by
  rw [lintegral_lintegral_swap (measurable_prod_diff hfc).aemeasurable]
  exact lintegral_congr fun h ↦ lintegral_mul_const _ (measurable_diff_sq hfc h)

theorem norm_periodicCharacter (k : PeriodicFrequency) (x : Space) :
    ‖NSFormalization.Paper1.periodicCharacter k x‖ = 1 := by
  rw [NSFormalization.Paper1.periodicCharacter_eq_mFourier]
  change ‖∏ i : Fin 3, fourier (k i) (((x i : ℝ) : UnitAddCircle))‖ = 1
  simp only [norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]

theorem norm_one_sub_periodicCharacter_le (k : PeriodicFrequency) (x : Space) :
    ‖1 - NSFormalization.Paper1.periodicCharacter (-k) x‖ ^ 2 ≤ 4 := by
  have hb : ‖1 - NSFormalization.Paper1.periodicCharacter (-k) x‖ ≤ 2 := by
    calc ‖1 - NSFormalization.Paper1.periodicCharacter (-k) x‖
        ≤ ‖(1 : ℂ)‖ + ‖NSFormalization.Paper1.periodicCharacter (-k) x‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_periodicCharacter]; norm_num
  nlinarith [norm_nonneg (1 - NSFormalization.Paper1.periodicCharacter (-k) x)]

theorem summable_coeffSq {f : SpatialField} (hfc : Continuous f) :
    Summable (fun k : PeriodicFrequency ↦
      ∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2) :=
  (hasSum_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦
    NSFormalization.Paper1.hasSum_sq_periodicFourierCoeff _ (continuous_component hfc i))).summable

theorem lintegral_cube_diff_sq {f : SpatialField} (hfp : IsPeriodicSpatial f)
    (hfc : Continuous f) (h : Space) :
    ∫⁻ x in halfOpenCube, ENNReal.ofReal (‖f x - f (x - h)‖ ^ 2)
      = ∑' k : PeriodicFrequency, ENNReal.ofReal
          (‖1 - NSFormalization.Paper1.periodicCharacter (-k) h‖ ^ 2 *
            ∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2) := by
  have hcont : Continuous fun x : Space ↦ ‖f x - f (x - h)‖ ^ 2 :=
    (hfc.sub (hfc.comp (continuous_id.sub continuous_const))).norm.pow 2
  have hsummable : Summable (fun k : PeriodicFrequency ↦
      ‖1 - NSFormalization.Paper1.periodicCharacter (-k) h‖ ^ 2 *
        ∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_)
      ((summable_coeffSq hfc).mul_left 4)
    exact mul_le_mul_of_nonneg_right (norm_one_sub_periodicCharacter_le k h)
      (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
  rw [lintegral_halfOpenCube_ofReal hcont (fun x ↦ by positivity),
    cubeIntegral_diff_norm_sq hfp hfc h]
  exact ENNReal.ofReal_tsum_of_nonneg (fun k ↦ by positivity) hsummable

theorem inner_latticeVector (k : PeriodicFrequency) (h : Space) :
    (⟪latticeVector k, h⟫ : ℝ) = ∑ i : Fin 3, ((k i : ℤ) : ℝ) * h i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  show h i * (latticeVector k) i = ((k i : ℤ) : ℝ) * h i
  rw [latticeVector_apply, mul_comm]

theorem inner_angularVector (k : PeriodicFrequency) (h : Space) :
    (⟪angularVector k, h⟫ : ℝ) = 2 * Real.pi * ∑ i : Fin 3, ((k i : ℤ) : ℝ) * h i := by
  unfold angularVector
  rw [real_inner_smul_left, inner_latticeVector]

theorem periodicCharacter_neg_eq (k : PeriodicFrequency) (h : Space) :
    NSFormalization.Paper1.periodicCharacter (-k) h =
      Complex.exp (-(Complex.I * ((⟪angularVector k, h⟫ : ℝ) : ℂ))) := by
  unfold NSFormalization.Paper1.periodicCharacter
  congr 1
  rw [NSFormalization.Paper1.periodicPhase_apply, inner_angularVector]
  have hsum : ∑ i : Fin 3, ((((-k) i : ℤ)) : ℂ) * ((h i : ℝ) : ℂ)
      = -∑ i : Fin 3, (((k i : ℤ)) : ℂ) * ((h i : ℝ) : ℂ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hneg : ((-k) i : ℤ) = -(k i) := rfl
    rw [hneg]
    push_cast
    ring
  rw [hsum]
  push_cast
  ring

theorem norm_one_sub_periodicCharacter_eq (k : PeriodicFrequency) (h : Space) :
    ‖1 - NSFormalization.Paper1.periodicCharacter (-k) h‖
      = ‖Complex.exp (Complex.I * ((⟪angularVector k, h⟫ : ℝ) : ℂ)) - 1‖ := by
  rw [periodicCharacter_neg_eq]
  have hnorm : ‖Complex.exp (Complex.I * ((⟪angularVector k, h⟫ : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hfac : Complex.exp (Complex.I * ((⟪angularVector k, h⟫ : ℝ) : ℂ)) - 1
      = Complex.exp (Complex.I * ((⟪angularVector k, h⟫ : ℝ) : ℂ)) *
        (1 - Complex.exp (-(Complex.I * ((⟪angularVector k, h⟫ : ℝ) : ℂ)))) := by
    rw [mul_sub, mul_one, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  rw [hfac, norm_mul, hnorm, one_mul]

theorem lintegral_character_kernel {s : ℝ} (hs : 0 < s) (k : PeriodicFrequency) :
    ∫⁻ h : Space, ENNReal.ofReal (‖1 - NSFormalization.Paper1.periodicCharacter (-k) h‖ ^ 2) *
        fractionalRadialKernel s h
      = ENNReal.ofReal (‖angularVector k‖ ^ (2 * s)) * cFrac s := by
  rw [← kernelIntegral_eq s hs (angularVector k)]
  refine lintegral_congr fun h ↦ ?_
  rw [norm_one_sub_periodicCharacter_eq]

theorem measurable_characterKernel {s : ℝ} (k : PeriodicFrequency) :
    Measurable (fun h : Space ↦
      ENNReal.ofReal (‖1 - NSFormalization.Paper1.periodicCharacter (-k) h‖ ^ 2) *
        fractionalRadialKernel s h) := by
  refine Measurable.mul ?_ (measurable_fractionalRadialKernel s)
  refine ENNReal.measurable_ofReal.comp ?_
  exact ((continuous_const.sub
    (NSFormalization.Paper1.periodicCharacter_smooth (-k)).continuous).norm.pow 2).measurable

theorem angularVector_zero : angularVector (0 : PeriodicFrequency) = 0 := by
  unfold angularVector
  have : latticeVector (0 : PeriodicFrequency) = 0 := by
    ext j
    show (((0 : PeriodicFrequency) j : ℤ) : ℝ) = (0 : Space) j
    simp
  rw [this, smul_zero]

theorem term_identity {s : ℝ} (hs : 0 < s) (k : PeriodicFrequency) {A : ℝ} (_hA : 0 ≤ A) :
    ENNReal.ofReal A * (ENNReal.ofReal (‖angularVector k‖ ^ (2 * s)) * cFrac s)
      = cFrac s * ENNReal.ofReal (homogeneousDatumWeight s k ^ 2 * A) := by
  by_cases hk : k = 0
  · subst hk
    rw [angularVector_zero, norm_zero, Real.zero_rpow (by positivity),
      homogeneousDatumWeight_zero]
    simp
  · rw [homogeneousDatumWeight_sq_of_ne s hk,
      ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
    ring

theorem periodicHomogeneousENorm_lt_top {s : ℝ} (hs : 0 < s) {f : SpatialField}
    (hfp : IsPeriodicSpatial f) (hfs : ContDiff ℝ ∞ f) :
    periodicHomogeneousENorm s (meanZeroPartT f) < ⊤ := by
  obtain ⟨A, hA, -⟩ := exists_homogeneous_datum hs hfp hfs
  calc periodicHomogeneousENorm s (meanZeroPartT f)
      ≤ ‖A‖ₑ := iInf_le (fun B : {B : PeriodicSobolev s //
        IsPeriodicHomogeneousDatum s (meanZeroPartT f) B} ↦ ‖B.1‖ₑ) ⟨A, hA⟩
    _ < ⊤ := by rw [← ofReal_norm]; exact ENNReal.ofReal_lt_top

set_option maxHeartbeats 400000 in
/-- `03-torus.tex:53-72`: the torus Gagliardo identity. -/
theorem torus_identity_smooth {s : ℝ} (hs0 : 0 < s) {f : SpatialField}
    (hfs : ContDiff ℝ ∞ f) (hfp : IsPeriodicSpatial f) :
    ITorus s f = cFrac s * periodicHomogeneousENorm s (meanZeroPartT f) ^ (2 : ℕ) := by
  have hfc : Continuous f := hfs.continuous
  calc ITorus s f
      = ∫⁻ x in halfOpenCube, ∫⁻ y in fundamentalCube,
          ENNReal.ofReal (‖f x - f y‖ ^ 2) * periodicKernel s (x - y) :=
        setLIntegral_congr fundamentalCube_ae_eq_halfOpenCube
    _ = ∫⁻ x in halfOpenCube, ∫⁻ y in halfOpenCube,
          ENNReal.ofReal (‖f x - f y‖ ^ 2) * periodicKernel s (x - y) :=
        lintegral_congr fun x ↦ setLIntegral_congr fundamentalCube_ae_eq_halfOpenCube
    _ = ∫⁻ x in halfOpenCube, ∫⁻ h : Space,
          ENNReal.ofReal (‖f x - f (x - h)‖ ^ 2) * fractionalRadialKernel s h :=
        lintegral_congr fun x ↦
          (lintegral_cube_periodicKernel hfp hfc x).trans (lintegral_whole_shift x)
    _ = ∫⁻ h : Space, (∫⁻ x in halfOpenCube,
          ENNReal.ofReal (‖f x - f (x - h)‖ ^ 2)) * fractionalRadialKernel s h :=
        lintegral_swap_diff hfc
    _ = ∫⁻ h : Space, (∑' k : PeriodicFrequency, ENNReal.ofReal
          (‖1 - NSFormalization.Paper1.periodicCharacter (-k) h‖ ^ 2 *
            ∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2)) *
          fractionalRadialKernel s h :=
        lintegral_congr fun h ↦ by rw [lintegral_cube_diff_sq hfp hfc h]
    _ = ∫⁻ h : Space, ∑' k : PeriodicFrequency,
          ENNReal.ofReal (∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2) *
            (ENNReal.ofReal (‖1 - NSFormalization.Paper1.periodicCharacter (-k) h‖ ^ 2) *
              fractionalRadialKernel s h) := by
        refine lintegral_congr fun h ↦ ?_
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun k ↦ ?_
        rw [ENNReal.ofReal_mul (sq_nonneg _)]
        ring
    _ = ∑' k : PeriodicFrequency, ∫⁻ h : Space,
          ENNReal.ofReal (∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2) *
            (ENNReal.ofReal (‖1 - NSFormalization.Paper1.periodicCharacter (-k) h‖ ^ 2) *
              fractionalRadialKernel s h) :=
        lintegral_tsum fun k ↦ ((measurable_characterKernel k).const_mul _).aemeasurable
    _ = ∑' k : PeriodicFrequency,
          ENNReal.ofReal (∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2) *
            (ENNReal.ofReal (‖angularVector k‖ ^ (2 * s)) * cFrac s) := by
        refine tsum_congr fun k ↦ ?_
        rw [lintegral_const_mul _ (measurable_characterKernel k),
          lintegral_character_kernel hs0 k]
    _ = ∑' k : PeriodicFrequency, cFrac s * ENNReal.ofReal (homogeneousDatumWeight s k ^ 2 *
          ∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2) :=
        tsum_congr fun k ↦ term_identity hs0 k (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
    _ = cFrac s * ∑' k : PeriodicFrequency,
          ENNReal.ofReal (homogeneousDatumWeight s k ^ 2 *
            ∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ ((f x i : ℝ) : ℂ)) k‖ ^ 2) :=
        ENNReal.tsum_mul_left
    _ = cFrac s * periodicHomogeneousENorm s (meanZeroPartT f) ^ (2 : ℕ) := by
        rw [periodicHomogeneousENorm_sq_smooth hs0 hfp hfs]

/-! ## 9. Named aliases for the reusable kernel lemmas -/

/-- Rotation invariance of the whole-space directional difference integral
(`03-torus.tex:66-67`). -/
theorem kernel_rotation (s : ℝ) (R : Space ≃ₗᵢ[ℝ] Space) (ξ : Space) :
    kernelIntegral s (R ξ) = kernelIntegral s ξ := kernelIntegral_isometry s R ξ

/-- Dilation of the whole-space directional difference integral
(`03-torus.tex:66-67`). -/
theorem kernel_scaling (s : ℝ) {r : ℝ} (hr : 0 < r) (ξ : Space) :
    kernelIntegral s (r • ξ) = ENNReal.ofReal (r ^ (2 * s)) * kernelIntegral s ξ :=
  kernelIntegral_smul s hr ξ

/-- Single-copy unfolding of the periodized kernel (`03-torus.tex:57-63`). -/
theorem periodicKernel_unfold {s : ℝ} {f : SpatialField}
    (hfp : IsPeriodicSpatial f) (hfc : Continuous f) (x : Space) :
    ∫⁻ y in halfOpenCube, ENNReal.ofReal (‖f x - f y‖ ^ 2) * periodicKernel s (x - y)
      = ∫⁻ u : Space, ENNReal.ofReal (‖f x - f u‖ ^ 2) * fractionalRadialKernel s (x - u) :=
  lintegral_cube_periodicKernel hfp hfc x

/-- `03-torus.tex:53-72`: the `torus_identity` field of `LocalizationAPI`. -/
theorem torus_identity {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {f : SpatialField}
    (hfs : ContDiff ℝ ∞ f) (hfp : IsPeriodicSpatial f) :
    ITorus s f < ⊤ ∧
      ITorus s f = cFrac s * periodicHomogeneousENorm s (meanZeroPartT f) ^ (2 : ℕ) := by
  refine ⟨?_, torus_identity_smooth hs0 hfs hfp⟩
  rw [torus_identity_smooth hs0 hfs hfp]
  exact ENNReal.mul_lt_top (cFrac_lt_top s hs0 hs1)
    (ENNReal.pow_lt_top (periodicHomogeneousENorm_lt_top hs0 hfp hfs))

end NSFormalization.Section3.T13
