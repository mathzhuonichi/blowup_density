import NavierStokes.R3ConvolutionYoung
import NavierStokes.R3PressureNearKernel

/-!
# The pressure commutator with a sixth-power cutoff

A kernel bounded by `C |x|⁻³` away from the origin has an absolutely
convergent cutoff commutator almost everywhere. Splitting its majorant into
near and remainder convolutions gives an `L²` estimate using only weighted
`L^(3/2)` and unweighted `L¹` norms of its input.
-/

noncomputable section
namespace NavierStokes.R3PressureCommutator

open Set Filter MeasureTheory ProblemStatement R3ConvolutionYoung R3PressureNearKernel
open scoped ENNReal Topology

structure Cutoff (R L : ℝ) (φ : Space → ℝ) : Prop where
  radius_pos : 0 < R
  constant_ge_one : 1 ≤ L
  measurable : Measurable φ
  range : ∀ x, φ x ∈ Icc (0 : ℝ) 1
  difference : ∀ x y, |φ x - φ y| ≤ L * (‖x - y‖ / R)

structure KernelBound (C : ℝ) (K : Space → ℂ) : Prop where
  constant_nonneg : 0 ≤ C
  measurable : Measurable K
  bound : ∀ z, z ≠ 0 → ‖K z‖ ≤ C * ‖z‖ ^ (-3 : ℝ)

def weightedNorm (φ : Space → ℝ) (g : Space → ℂ) (x : Space) : ℝ := φ x ^ 5 * ‖g x‖

def integrand (φ : Space → ℝ) (K g : Space → ℂ) (x z : Space) : ℂ :=
  ((φ x ^ 6 - φ (x - z) ^ 6 : ℝ) : ℂ) * K z * g (x - z)

def commutator (φ : Space → ℝ) (K g : Space → ℂ) (x : Space) : ℂ :=
  ∫ z : Space, integrand φ K g x z

def majorizingFunction (R L C : ℝ) (φ : Space → ℝ) (g : Space → ℂ) (x : Space) : ℝ :=
  (C * (96 * L ^ 6)) *
    (scalarConvolution (nearKernel R) (weightedNorm φ g) x +
      scalarConvolution (remainderKernel R) (fun y => ‖g y‖) x)

theorem integrand_bound {R L C : ℝ} {φ : Space → ℝ} {K g : Space → ℂ}
    (hφ : Cutoff R L φ) (hK : KernelBound C K) (x z : Space) :
    ‖integrand φ K g x z‖ ≤ (C * (96 * L ^ 6)) *
      (nearKernel R z * weightedNorm φ g (x - z) + remainderKernel R z * ‖g (x - z)‖) := by
  have hn := scaled_nonneg hφ.radius_pos nearBase_nonneg z
  have hr := scaled_nonneg hφ.radius_pos (radialProfile_nonneg 3 (-3)) z
  change 0 ≤ nearKernel R z at hn
  change 0 ≤ remainderKernel R z at hr
  by_cases hz : z = 0
  · subst z
    simp only [integrand, sub_zero, sub_self, Complex.ofReal_zero, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg hK.constant_nonneg (by positivity))
      (add_nonneg (mul_nonneg hn (mul_nonneg (pow_nonneg (hφ.range x).1 _) (norm_nonneg _)))
        (mul_nonneg hr (norm_nonneg _)))
  have hd : |φ x - φ (x - z)| ≤ L * (‖z‖ / R) := by
    simpa only [sub_sub_cancel] using hφ.difference x (x - z)
  have hb := cutoff_kernel_bound hφ.radius_pos hφ.constant_ge_one
    (hφ.range x) (hφ.range (x - z)) z hd
  simp only [integrand, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |φ x ^ 6 - φ (x - z) ^ 6| * (C * ‖z‖ ^ (-3 : ℝ)) * ‖g (x - z)‖ := by
      gcongr
      exact hK.bound z hz
    _ = C * (‖z‖ ^ (-3 : ℝ) * |φ x ^ 6 - φ (x - z) ^ 6|) * ‖g (x - z)‖ := by ring
    _ ≤ C * ((96 * L ^ 6) * (nearKernel R z * φ (x - z) ^ 5 + remainderKernel R z)) *
        ‖g (x - z)‖ := by
          gcongr
          exact hK.constant_nonneg
    _ = _ := by unfold weightedNorm; ring

theorem commutator_aestronglyMeasurable {R L C : ℝ} {φ : Space → ℝ} {K g : Space → ℂ}
    (hφ : Cutoff R L φ) (hK : KernelBound C K) (hg : Measurable g) :
    AEStronglyMeasurable (commutator φ K g) := by
  unfold commutator
  apply AEStronglyMeasurable.integral_prod_right' (f := fun p : Space × Space => integrand φ K g p.1 p.2)
  unfold integrand
  have hφm := hφ.measurable
  have hKm := hK.measurable
  exact (by fun_prop : Measurable (fun p : Space × Space =>
    ((φ p.1 ^ 6 - φ (p.1 - p.2) ^ 6 : ℝ) : ℂ) * K p.2 * g (p.1 - p.2))).aestronglyMeasurable

theorem ae_integrable_and_bound {R L C : ℝ} {φ : Space → ℝ} {K g : Space → ℂ}
    (hφ : Cutoff R L φ) (hK : KernelBound C K) (hg : Measurable g)
    (hg₁ : MemLp g 1) (hw : MemLp (weightedNorm φ g) (3 / 2)) :
    ∀ᵐ x ∂volume, Integrable (integrand φ K g x) ∧
      ‖commutator φ K g x‖ ≤ majorizingFunction R L C φ g x := by
  have hnm : Measurable (nearKernel R) := scaled_measurable R nearBase_measurable
  have hrm : Measurable (remainderKernel R) := scaled_measurable R (radialProfile_measurable 3 (-3))
  have hwm : Measurable (weightedNorm φ g) := (hφ.measurable.pow_const 5).mul hg.norm
  have hnear := ae_integrable_six_fifths_three_halves hnm hwm
    (nearKernel_memLp hφ.radius_pos) hw
  have hfar := ae_integrable_two_one hrm hg.norm (remainderKernel_memLp hφ.radius_pos) hg₁.norm
  filter_upwards [hnear, hfar] with x hnx hrx
  have hsum := (hnx.add hrx).const_mul (C * (96 * L ^ 6))
  have hφm := hφ.measurable
  have hKm := hK.measurable
  have him : AEStronglyMeasurable (integrand φ K g x) := by
    unfold integrand
    fun_prop
  refine ⟨hsum.mono' him (Eventually.of_forall (integrand_bound hφ hK x)), ?_⟩
  have hb := norm_integral_le_of_norm_le hsum (Eventually.of_forall (integrand_bound hφ hK x))
  simpa only [commutator, majorizingFunction, integral_const_mul, Pi.add_apply, integral_add hnx hrx,
    scalarConvolution] using hb

theorem majorizingFunction_memLp {R L C : ℝ} {φ : Space → ℝ} {g : Space → ℂ}
    (hφ : Cutoff R L φ) (hg : Measurable g)
    (hg₁ : MemLp g 1) (hw : MemLp (weightedNorm φ g) (3 / 2)) :
    MemLp (majorizingFunction R L C φ g) 2 := by
  have hn := scalarConvolution_memLp_six_fifths_three_halves
    (scaled_measurable R nearBase_measurable) ((hφ.measurable.pow_const 5).mul hg.norm)
    (nearKernel_memLp hφ.radius_pos) hw
  have hr := scalarConvolution_memLp_two_one
    (scaled_measurable R (radialProfile_measurable 3 (-3))) hg.norm
    (remainderKernel_memLp hφ.radius_pos) hg₁.norm
  exact (hn.add hr).const_mul _

theorem commutator_memLp {R L C : ℝ} {φ : Space → ℝ} {K g : Space → ℂ}
    (hφ : Cutoff R L φ) (hK : KernelBound C K) (hg : Measurable g)
    (hg₁ : MemLp g 1) (hw : MemLp (weightedNorm φ g) (3 / 2)) :
    MemLp (commutator φ K g) 2 :=
  (majorizingFunction_memLp (C := C) hφ hg hg₁ hw).mono'
    (commutator_aestronglyMeasurable hφ hK hg)
    ((ae_integrable_and_bound hφ hK hg hg₁ hw).mono fun _ h => h.2)

theorem majorizingFunction_lpNorm {R L C : ℝ} {φ : Space → ℝ} {g : Space → ℂ}
    (hφ : Cutoff R L φ) (hC : 0 ≤ C) (hg : Measurable g)
    (hg₁ : MemLp g 1) (hw : MemLp (weightedNorm φ g) (3 / 2)) :
    lpNorm (majorizingFunction R L C φ g) 2 volume ≤ (C * (96 * L ^ 6)) *
      (R ^ (-1 / 2 : ℝ) * lpNorm nearBase (6 / 5) volume * lpNorm (weightedNorm φ g) (3 / 2) volume +
        R ^ (-3 / 2 : ℝ) * lpNorm remainderBase 2 volume * lpNorm g 1 volume) := by
  have hnm : Measurable (nearKernel R) := scaled_measurable R nearBase_measurable
  have hrm : Measurable (remainderKernel R) := scaled_measurable R (radialProfile_measurable 3 (-3))
  have hwm : Measurable (weightedNorm φ g) := (hφ.measurable.pow_const 5).mul hg.norm
  have hn := scalarConvolution_memLp_six_fifths_three_halves hnm hwm
    (nearKernel_memLp hφ.radius_pos) hw
  have hb₁ := lpNorm_scalarConvolution_six_fifths_three_halves hnm hwm
    (nearKernel_memLp hφ.radius_pos) hw
  have hb₂ := lpNorm_scalarConvolution_two_one hrm hg.norm
    (remainderKernel_memLp hφ.radius_pos) hg₁.norm
  rw [nearKernel_lpNorm hφ.radius_pos] at hb₁
  rw [remainderKernel_lpNorm hφ.radius_pos, lpNorm_norm hg₁.1] at hb₂
  have hc : 0 ≤ C * (96 * L ^ 6) := mul_nonneg hC (by positivity)
  change lpNorm ((C * (96 * L ^ 6)) •
    (scalarConvolution (nearKernel R) (weightedNorm φ g) +
      scalarConvolution (remainderKernel R) (fun y => ‖g y‖))) 2 volume ≤ _
  rw [lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  exact (lpNorm_add_le hn (by norm_num)).trans (add_le_add hb₁ hb₂)

/-- The pressure commutator estimate, including both powers of the cutoff radius. -/
theorem commutator_lpNorm {R L C : ℝ} {φ : Space → ℝ} {K g : Space → ℂ}
    (hφ : Cutoff R L φ) (hK : KernelBound C K) (hg : Measurable g)
    (hg₁ : MemLp g 1) (hw : MemLp (weightedNorm φ g) (3 / 2)) :
    lpNorm (commutator φ K g) 2 volume ≤ (C * (96 * L ^ 6)) *
      (R ^ (-1 / 2 : ℝ) * lpNorm nearBase (6 / 5) volume * lpNorm (weightedNorm φ g) (3 / 2) volume +
        R ^ (-3 / 2 : ℝ) * lpNorm remainderBase 2 volume * lpNorm g 1 volume) := by
  have hm := majorizingFunction_memLp (C := C) hφ hg hg₁ hw
  have hb := ENNReal.toReal_mono hm.2.ne (eLpNorm_mono_ae_real
    ((ae_integrable_and_bound hφ hK hg hg₁ hw).mono fun _ h => h.2) (p := 2))
  rw [toReal_eLpNorm (commutator_aestronglyMeasurable hφ hK hg), toReal_eLpNorm hm.1] at hb
  exact hb.trans (majorizingFunction_lpNorm hφ hK.constant_nonneg hg hg₁ hw)


/-- Pointwise convergence away from the singularity passes through the
absolutely convergent commutator integral. -/
theorem commutator_tendsto_ae {R L C : ℝ} {φ : Space → ℝ}
    {K : ℕ → Space → ℂ} {K₀ g : Space → ℂ}
    (hφ : Cutoff R L φ) (hK : ∀ n, KernelBound C (K n))
    (hg : Measurable g) (hg₁ : MemLp g 1) (hw : MemLp (weightedNorm φ g) (3 / 2))
    (hlim : ∀ z, z ≠ 0 → Tendsto (fun n => K n z) atTop (𝓝 (K₀ z))) :
    ∀ᵐ x ∂volume, Tendsto (fun n => commutator φ (K n) g x) atTop
      (𝓝 (commutator φ K₀ g x)) := by
  have hnm : Measurable (nearKernel R) := scaled_measurable R nearBase_measurable
  have hrm : Measurable (remainderKernel R) := scaled_measurable R (radialProfile_measurable 3 (-3))
  have hwm : Measurable (weightedNorm φ g) := (hφ.measurable.pow_const 5).mul hg.norm
  have hnear := ae_integrable_six_fifths_three_halves hnm hwm
    (nearKernel_memLp hφ.radius_pos) hw
  have hfar := ae_integrable_two_one hrm hg.norm (remainderKernel_memLp hφ.radius_pos) hg₁.norm
  filter_upwards [hnear, hfar] with x hnx hrx
  apply tendsto_integral_of_dominated_convergence
    (fun z => (C * (96 * L ^ 6)) *
      (nearKernel R z * weightedNorm φ g (x - z) + remainderKernel R z * ‖g (x - z)‖))
  · intro n
    have hφm := hφ.measurable
    have hKm := (hK n).measurable
    unfold integrand
    fun_prop
  · exact (hnx.add hrx).const_mul _
  · intro n
    exact Eventually.of_forall (integrand_bound hφ (hK n) x)
  · apply Eventually.of_forall
    intro z
    by_cases hz : z = 0
    · subst z
      simpa only [integrand, sub_zero, sub_self, Complex.ofReal_zero, zero_mul] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    · exact (tendsto_const_nhds.mul (hlim z hz)).mul tendsto_const_nhds

/-- A dominated convergence lemma at the exact exponent used by the
pressure operator. The common bound is an actual `L²` function. -/
theorem tendsto_lpNorm_two_of_dominated {F : ℕ → Space → ℂ} {f : Space → ℂ} {B : Space → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n)) (hf : AEStronglyMeasurable f)
    (hB : MemLp B 2)
    (hFB : ∀ n, ∀ᵐ x ∂volume, ‖F n x‖ ≤ B x) (hfB : ∀ᵐ x ∂volume, ‖f x‖ ≤ B x)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => lpNorm (fun x => F n x - f x) 2 volume) atTop (𝓝 0) := by
  have hBsq : Integrable (fun x => B x ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using (memLp_two_iff_integrable_sq_norm hB.1).mp hB
  have hint := tendsto_integral_of_dominated_convergence
    (fun x => 4 * B x ^ 2)
    (F := fun n x => ‖F n x - f x‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun n => ((hF n).sub hf).norm.pow 2) (hBsq.const_mul 4)
  have hh : ∀ n, ∀ᵐ x ∂volume, ‖‖F n x - f x‖ ^ 2‖ ≤ 4 * B x ^ 2 := by
    intro n
    filter_upwards [hFB n, hfB] with x hx hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hnorm := norm_sub_le (F n x) (f x)
    have hpos := norm_nonneg (F n x - f x)
    nlinarith [sq_nonneg (2 * B x - ‖F n x - f x‖)]
  have hz : ∀ᵐ x ∂volume, Tendsto (fun n => ‖F n x - f x‖ ^ 2) atTop (𝓝 0) := by
    filter_upwards [hlim] with x hx
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (hx.sub (tendsto_const_nhds (x := f x))).norm.pow 2
  have ht : Tendsto (fun n => ∫ x : Space, ‖F n x - f x‖ ^ 2) atTop (𝓝 0) := by
    simpa only [integral_zero] using hint hh hz
  have hp := ht.rpow_const (p := (1 / 2 : ℝ)) (Or.inr (by norm_num))
  have he (n : ℕ) : lpNorm (fun x => F n x - f x) 2 volume =
      (∫ x : Space, ‖F n x - f x‖ ^ 2) ^ (1 / 2 : ℝ) := by
    change lpNorm (F n - f) 2 volume = _
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ((hF n).sub hf)]
    norm_num [Pi.sub_apply]
  simpa only [he, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using hp


/-- The commutators converge strongly in `L²` under a uniform kernel bound. -/
theorem commutator_tendsto_lpNorm {R L C : ℝ} {φ : Space → ℝ}
    {K : ℕ → Space → ℂ} {K₀ g : Space → ℂ}
    (hφ : Cutoff R L φ) (hK : ∀ n, KernelBound C (K n)) (hK₀ : KernelBound C K₀)
    (hg : Measurable g) (hg₁ : MemLp g 1) (hw : MemLp (weightedNorm φ g) (3 / 2))
    (hlim : ∀ z, z ≠ 0 → Tendsto (fun n => K n z) atTop (𝓝 (K₀ z))) :
    Tendsto (fun n => lpNorm (fun x => commutator φ (K n) g x - commutator φ K₀ g x) 2 volume)
      atTop (𝓝 0) :=
  tendsto_lpNorm_two_of_dominated
    (fun n => commutator_aestronglyMeasurable hφ (hK n) hg)
    (commutator_aestronglyMeasurable hφ hK₀ hg)
    (majorizingFunction_memLp hφ hg hg₁ hw)
    (fun n => (ae_integrable_and_bound hφ (hK n) hg hg₁ hw).mono fun _ h => h.2)
    ((ae_integrable_and_bound hφ hK₀ hg hg₁ hw).mono fun _ h => h.2)
    (commutator_tendsto_ae hφ hK hg hg₁ hw hlim)

end NavierStokes.R3PressureCommutator
