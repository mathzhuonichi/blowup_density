import NSFormalization.Source.RieszPotentialLp

/-! Complex unnormalized Riesz convolution from the checked positive potential.
The norm estimate is reused; no Fourier multiplier identification is assumed. -/
noncomputable section
namespace NSFormalization.RieszComplexPotential
open MeasureTheory Set
open NSFormalization.RieszPotentialAssembly NSFormalization.RieszPotentialLp
open scoped ENNReal
abbrev Space := NSFormalization.RieszPotentialAssembly.Space

def complexPotential (a : ℝ) (g : Space → ℂ) (x : Space) : ℂ :=
  ∫ y : Space, ‖y‖ ^ (a - 3) • g (x - y)

theorem complexPotential_congr_ae {g h : Space → ℂ} (he : g =ᵐ[volume] h) (a : ℝ) :
    complexPotential a g = complexPotential a h := by
  funext x
  apply integral_congr_ae
  filter_upwards [(volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae_eq_comp he] with y hy
  change g (x-y) = h (x-y) at hy
  rw [hy]

theorem measurable_complexPotential (a : ℝ) {g : Space → ℂ} (hg : Measurable g) :
    Measurable (complexPotential a g) := by
  have hm : Measurable (fun p : Space × Space => ‖p.2‖ ^ (a-3) • g (p.1-p.2)) := by
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem norm_complexPotential_le (a : ℝ) {g : Space → ℂ} (hg : Measurable g) (x : Space) :
    ‖complexPotential a g x‖ ≤ realPotential a g x := by
  have he : (∫ y : Space, ‖y‖ ^ (a-3) * ‖g (x-y)‖) = realPotential a g x := by
    apply integral_eq_lintegral_of_nonneg_ae
    · exact Filter.Eventually.of_forall (fun y =>
        mul_nonneg (Real.rpow_nonneg (norm_nonneg y) _) (norm_nonneg _))
    · exact (by fun_prop : Measurable (fun y : Space => ‖y‖ ^ (a-3) * ‖g (x-y)‖)).aestronglyMeasurable
  calc
    ‖complexPotential a g x‖ ≤ ∫ y : Space, ‖‖y‖ ^ (a-3) • g (x-y)‖ := norm_integral_le_integral_norm _
    _ = realPotential a g x := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact he

theorem measurable_complexPotential_of_memLp (a : ℝ) {g : Space → ℂ} (h2 : MemLp g 2 volume) :
    Measurable (complexPotential a g) := by
  rw [complexPotential_congr_ae h2.1.ae_eq_mk a]
  exact measurable_complexPotential a h2.1.measurable_mk

theorem ae_integrable {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (h2 : MemLp g 2 volume) :
    ∀ᵐ x : Space ∂volume, Integrable (fun y : Space => ‖y‖ ^ (a-3) • g (x-y)) := by
  filter_upwards [ae_full_integrable_of_memLp ha ha3 h2] with x hx
  have hg := h2.1.comp_measurePreserving (volume.measurePreserving_sub_left x)
  apply hx.mono' (((by fun_prop : Measurable (fun y : Space => ‖y‖ ^ (a-3))).aestronglyMeasurable).smul hg)
  filter_upwards with y
  change ‖‖y‖ ^ (a-3) • g (x-y)‖ ≤ ‖y‖ ^ (a-3) * ‖g (x-y)‖
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), le_refl]

theorem eLpNorm_complexPotential_le {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (h2 : MemLp g 2 volume) :
    eLpNorm (complexPotential a g) (ENNReal.ofReal (targetExponent a)) volume ≤
      ENNReal.ofReal (potentialConstant a * (512:ℝ)^(1/targetExponent a) * (eLpNorm g 2 volume).toReal) := by
  have he := h2.1.ae_eq_mk
  have hmajor (x : Space) : ‖complexPotential a g x‖ ≤ realPotential a g x := by
    rw [complexPotential_congr_ae he a, realPotential_congr_ae he a]
    exact norm_complexPotential_le a h2.1.measurable_mk x
  exact (eLpNorm_mono_ae_real (Filter.Eventually.of_forall hmajor)).trans
    (eLpNorm_realPotential_le ha ha3 h2)

theorem complexPotential_memLp {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (h2 : MemLp g 2 volume) :
    MemLp (complexPotential a g) (ENNReal.ofReal (targetExponent a)) volume :=
  ⟨(measurable_complexPotential_of_memLp a h2).aestronglyMeasurable,
    lt_of_le_of_lt (eLpNorm_complexPotential_le ha ha3 h2) ENNReal.ofReal_lt_top⟩

end NSFormalization.RieszComplexPotential
