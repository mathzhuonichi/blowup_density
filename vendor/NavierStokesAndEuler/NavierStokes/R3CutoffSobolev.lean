import NavierStokes.R3WeightedLp
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Spatial cutoffs and the localized Sobolev estimate

The same explicit smooth cutoffs supply the pressure commutator, localized
energy, and the `L⁶` estimate of the fourth-power weighted velocity.
-/

noncomputable section
namespace NavierStokes.R3CutoffSobolev

open Set Filter MeasureTheory ProblemStatement
open scoped ENNReal NNReal Topology ContDiff

def baseBump : ContDiffBump (0 : Space) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def cutoff (R : ℝ) (x : Space) : ℝ := baseBump (R⁻¹ • x)

theorem cutoff_contDiff (R : ℝ) : ContDiff ℝ ∞ (cutoff R) := by
  apply (baseBump.contDiff (n := (⊤ : ℕ∞))).comp
  fun_prop

theorem cutoff_compact {R : ℝ} (hR : R ≠ 0) : HasCompactSupport (cutoff R) :=
  baseBump.hasCompactSupport.comp_smul (G₀ := ℝ) (c := R⁻¹) (inv_ne_zero hR)

theorem cutoff_range (R : ℝ) (x : Space) : cutoff R x ∈ Icc (0 : ℝ) 1 :=
  ⟨baseBump.nonneg, baseBump.le_one⟩

theorem cutoff_one {R : ℝ} (hR : 0 < R) {x : Space} (hx : ‖x‖ ≤ R) : cutoff R x = 1 := by
  apply baseBump.one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR)]
  change R⁻¹ * ‖x‖ ≤ 1
  exact (inv_mul_le_iff₀ hR).mpr (by simpa using hx)

theorem cutoff_temperate {R : ℝ} (hR : R ≠ 0) : (cutoff R).HasTemperateGrowth :=
  (cutoff_compact hR).hasTemperateGrowth (cutoff_contDiff R)

theorem scaled_derivative_bound {L R : ℝ} (_hL : 0 ≤ L) (hR : 0 < R)
    (hb : ∀ x : Space, ‖fderiv ℝ (baseBump : Space → ℝ) x‖ ≤ L) (x : Space) :
    ‖fderiv ℝ (cutoff R) x‖ ≤ L / R := by
  let S : Space →L[ℝ] Space := R⁻¹ • ContinuousLinearMap.id ℝ Space
  have hd := (((baseBump.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp)) (S x)).hasFDerivAt.comp x S.hasFDerivAt
  change ‖fderiv ℝ ((baseBump : Space → ℝ) ∘ S) x‖ ≤ _
  rw [hd.fderiv]
  calc
    _ ≤ ‖fderiv ℝ (baseBump : Space → ℝ) (S x)‖ * ‖S‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ L * R⁻¹ := by
      have hn : ‖S‖ = R⁻¹ := by simp [S, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
      rw [hn]
      exact mul_le_mul_of_nonneg_right (hb _) (inv_nonneg.mpr hR.le)
    _ = _ := (div_eq_mul_inv _ _).symm

/-- A single scale-independent constant controls all cutoffs. -/
theorem exists_cutoff_constant : ∃ L : ℝ, 1 ≤ L ∧ ∀ R, 0 < R →
    R3PressureCommutator.Cutoff R L (cutoff R) ∧
      ∀ x : Space, ‖fderiv ℝ (cutoff R) x‖ ≤ L / R := by
  have hc : Continuous (fderiv ℝ (baseBump : Space → ℝ)) :=
    (baseBump.contDiff (n := (⊤ : ℕ∞))).continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := (baseBump.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous hc
  let L := max C 1
  have hL : 1 ≤ L := le_max_right _ _
  have hb : ∀ x : Space, ‖fderiv ℝ (baseBump : Space → ℝ) x‖ ≤ L :=
    fun x => (hC x).trans (le_max_left _ _)
  refine ⟨L, hL, fun R hR => ?_⟩
  have hD := scaled_derivative_bound (zero_le_one.trans hL) hR hb
  refine ⟨⟨hR, hL, (cutoff_contDiff R).continuous.measurable, cutoff_range R, ?_⟩, hD⟩
  intro x y
  have hm := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := cutoff R)
    (s := univ) (x := y) (y := x)
    (fun z _ => (cutoff_contDiff R).differentiable (by simp) z) (fun z _ => hD z)
    convex_univ (mem_univ _) (mem_univ _)
  simpa only [Real.norm_eq_abs, div_mul_eq_mul_div, mul_div_assoc] using hm

theorem cutoff_tendsto (x : Space) : Tendsto (fun n : ℕ => cutoff ((n : ℝ) + 1) x) atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_add
      (tendsto_const_nhds (x := (1 : ℝ)))
  apply tendsto_const_nhds.congr'
  filter_upwards [hn.eventually (eventually_ge_atTop ‖x‖)] with n hnx
  exact (cutoff_one (by positivity) hnx).symm

def energyCutoff (n : ℕ) (x : Space) : ℝ := cutoff ((n : ℝ) + 1) x ^ 8

theorem energyCutoff_continuous (n : ℕ) : Continuous (energyCutoff n) :=
  (cutoff_contDiff _).continuous.pow 8

theorem energyCutoff_range (n : ℕ) (x : Space) : energyCutoff n x ∈ Icc (0 : ℝ) 1 :=
  ⟨pow_nonneg (cutoff_range _ x).1 8, pow_le_one₀ (cutoff_range _ x).1 (cutoff_range _ x).2⟩

theorem energyCutoff_tendsto (x : Space) : Tendsto (fun n => energyCutoff n x) atTop (𝓝 1) := by
  simpa only [energyCutoff, one_pow] using (cutoff_tendsto x).pow 8

def sobolevConstant : ℝ := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) (2 : ℝ≥0)

theorem sobolevConstant_nonneg : 0 ≤ sobolevConstant := NNReal.coe_nonneg _

theorem sobolev_six {v : Space → Space} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) :
    lpNorm v 6 volume ≤ sobolevConstant * lpNorm (fderiv ℝ v) 2 volume := by
  have hm : MemLp (fderiv ℝ v) 2 :=
    (hv.continuous_fderiv (by norm_num)).memLp_of_hasCompactSupport (hc.fderiv ℝ)
  have hh := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure Space) hv hc
    (p := 2) (p' := 6) (by norm_num) (by norm_num : 0 < Module.finrank ℝ Space) (by norm_num)
  have ht := ENNReal.toReal_mono (by finiteness) hh
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, toReal_eLpNorm hv.continuous.aestronglyMeasurable,
    toReal_eLpNorm hm.1, ENNReal.coe_ofNat, sobolevConstant] using ht

def weightedVector (φ : Space → ℝ) (w : Space → Space) (x : Space) : Space := φ x ^ 4 • w x

def weightedDerivativeNorm (φ : Space → ℝ) (w : Space → Space) (x : Space) : ℝ :=
  φ x ^ 4 * ‖fderiv ℝ w x‖

theorem weightedVector_contDiff {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ 1 φ) (hw : ContDiff ℝ 1 w) : ContDiff ℝ 1 (weightedVector φ w) :=
  (hφ.pow 4).smul hw

theorem weightedVector_compact {φ : Space → ℝ} (hφ : HasCompactSupport φ) (w : Space → Space) :
    HasCompactSupport (weightedVector φ w) := by
  have hp : HasCompactSupport (fun x => φ x ^ 4) := hφ.comp_left (g := fun r : ℝ => r ^ 4) (by norm_num)
  exact hp.smul_right (f' := w)

theorem weightedDerivativeNorm_memLp {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hw : ContDiff ℝ 1 w) :
    MemLp (weightedDerivativeNorm φ w) 2 := by
  have hp : HasCompactSupport (fun x => φ x ^ 4) := hc.comp_left (g := fun r : ℝ => r ^ 4) (by norm_num)
  have ht : Continuous (fun x => φ x ^ 4 * ‖fderiv ℝ w x‖) :=
    (hφ.continuous.pow 4).mul (hw.continuous_fderiv (by norm_num)).norm
  exact ht.memLp_of_hasCompactSupport (hp.mul_right (f' := fun x => ‖fderiv ℝ w x‖))

theorem weightedVector_derivative_bound {φ : Space → ℝ} {w : Space → Space} {D : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hw : ContDiff ℝ 1 w)
    (hr : ∀ x, φ x ∈ Icc (0 : ℝ) 1) (hD : 0 ≤ D) (hb : ∀ x, ‖fderiv ℝ φ x‖ ≤ D) (x : Space) :
    ‖fderiv ℝ (weightedVector φ w) x‖ ≤ weightedDerivativeNorm φ w x + 4 * D * ‖w x‖ := by
  have hφd := hφ.differentiable (by norm_num) x
  have hwd := hw.differentiable (by norm_num) x
  have hp4 : 0 ≤ φ x ^ 4 := pow_nonneg (hr x).1 4
  have hp3 : 0 ≤ φ x ^ 3 := pow_nonneg (hr x).1 3
  have hle3 : φ x ^ 3 ≤ 1 := pow_le_one₀ (hr x).1 (hr x).2
  have hp : HasFDerivAt (fun y => φ y ^ 4) ((4 * φ x ^ 3 : ℝ) • fderiv ℝ φ x) x := by
    convert! hφd.hasFDerivAt.pow 4 using 1
    norm_num [nsmul_eq_mul]
  have hv : HasFDerivAt (weightedVector φ w)
      (φ x ^ 4 • fderiv ℝ w x + ((4 * φ x ^ 3 : ℝ) • fderiv ℝ φ x).smulRight (w x)) x :=
    hp.smul hwd.hasFDerivAt
  have hbn : ‖((4 * φ x ^ 3 : ℝ) • fderiv ℝ φ x).smulRight (w x)‖ ≤ 4 * D * ‖w x‖ := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by norm_num) hp3)]
    have hh : φ x ^ 3 * ‖fderiv ℝ φ x‖ ≤ D :=
      (mul_le_mul_of_nonneg_left (hb x) hp3).trans (mul_le_of_le_one_left hD hle3)
    nlinarith [mul_le_mul_of_nonneg_right hh (norm_nonneg (w x))]
  rw [hv.fderiv]
  apply (norm_add_le _ _).trans
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp4]
  exact add_le_add le_rfl hbn

/-- The weighted `L⁶` velocity is controlled by the localized derivative
and the `R⁻¹` cutoff error, here parameterized by the derivative bound `D`. -/
theorem weighted_sobolev {φ : Space → ℝ} {w : Space → Space} {D : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hw : ContDiff ℝ 1 w)
    (hr : ∀ x, φ x ∈ Icc (0 : ℝ) 1) (hD : 0 ≤ D) (hb : ∀ x, ‖fderiv ℝ φ x‖ ≤ D)
    (hw₂ : MemLp w 2) :
    lpNorm (R3WeightedLp.fourthWeight φ (fun x => ‖w x‖)) 6 volume ≤
      sobolevConstant * (lpNorm (weightedDerivativeNorm φ w) 2 volume + 4 * D * lpNorm w 2 volume) := by
  have hv := weightedVector_contDiff hφ hw
  have hvc := weightedVector_compact hc w
  have hA := weightedDerivativeNorm_memLp hφ hc hw
  have hB : MemLp (fun x => weightedDerivativeNorm φ w x + (4 * D) * ‖w x‖) 2 :=
    hA.add (hw₂.norm.const_mul (4 * D))
  have hn := lpNorm_mono_real hB (weightedVector_derivative_bound hφ hw hr hD hb)
  have ht := lpNorm_add_le (g := (4 * D) • (fun x => ‖w x‖)) hA (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (by positivity), lpNorm_norm hw₂.1] at ht
  have he : lpNorm (R3WeightedLp.fourthWeight φ (fun x => ‖w x‖)) 6 volume =
      lpNorm (weightedVector φ w) 6 volume := by
    rw [← lpNorm_norm hv.continuous.aestronglyMeasurable]
    congr 1
    funext x
    simp only [R3WeightedLp.fourthWeight, weightedVector, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (hr x).1 4)]
  rw [he]
  exact (sobolev_six hv hvc).trans (mul_le_mul_of_nonneg_left (hn.trans ht) sobolevConstant_nonneg)


/-- A coordinate bound relating the operator norm to the dissipation sum. -/
theorem operator_norm_sq_le (A : Space →L[ℝ] Space) :
    ‖A‖ ^ 2 ≤ 3 * ∑ i : Fin 3, ‖A (coordinateVector i)‖ ^ 2 := by
  have hrepr (v : Space) : ∑ i : Fin 3, v i • coordinateVector i = v := by
    ext j
    simp [coordinateVector, Pi.single_apply]
  have hn : ‖A‖ ≤ ∑ i : Fin 3, ‖A (coordinateVector i)‖ := by
    apply A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    intro v
    calc
      ‖A v‖ = ‖A (∑ i : Fin 3, v i • coordinateVector i)‖ := by rw [hrepr]
      _ = ‖∑ i : Fin 3, v i • A (coordinateVector i)‖ := by simp only [map_sum, map_smul]
      _ ≤ ∑ i : Fin 3, ‖v i • A (coordinateVector i)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ‖v‖ * ‖A (coordinateVector i)‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg _)
      _ = (∑ i : Fin 3, ‖A (coordinateVector i)‖) * ‖v‖ := by rw [← Finset.mul_sum, mul_comm]
  have hs := sq_le_sq₀ (norm_nonneg A) (Finset.sum_nonneg fun _ _ => norm_nonneg (A (coordinateVector _))) |>.mpr hn
  rw [Fin.sum_univ_three] at hs ⊢
  nlinarith [sq_nonneg (‖A (coordinateVector 0)‖ - ‖A (coordinateVector 1)‖),
    sq_nonneg (‖A (coordinateVector 1)‖ - ‖A (coordinateVector 2)‖),
    sq_nonneg (‖A (coordinateVector 2)‖ - ‖A (coordinateVector 0)‖)]

end NavierStokes.R3CutoffSobolev
