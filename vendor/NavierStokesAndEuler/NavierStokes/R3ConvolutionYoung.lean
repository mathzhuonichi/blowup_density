import NavierStokes.ComparatorR3Bridge
import Mathlib.Analysis.Convolution

/-!
# Convolution estimates used by the whole-space pressure commutator

The two exponent pairs required by the refined cutoff estimate are
`L² * L¹ → L²` and `L^(6/5) * L^(3/2) → L²`. We prove their
nonnegative integral bounds from Hölder and Tonelli, retaining control of
integrability rather than relying on the zero value of an undefined integral.
-/

noncomputable section

namespace NavierStokes.R3ConvolutionYoung

open Set Filter MeasureTheory ProblemStatement
open scoped ENNReal Topology

def majorant (f g : Space → ℝ≥0∞) (x : Space) : ℝ≥0∞ :=
  ∫⁻ y : Space, f y * g (x - y)

theorem majorant_measurable {f g : Space → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    Measurable (majorant f g) := by
  apply Measurable.lintegral_prod_right
  exact (hf.comp measurable_snd).mul (hg.comp (measurable_fst.sub measurable_snd))

theorem integral_majorant {f g : Space → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x : Space, majorant f g x) = (∫⁻ y : Space, f y) * (∫⁻ z : Space, g z) := by
  unfold majorant
  rw [lintegral_lintegral_swap
    ((hf.comp measurable_snd).mul (hg.comp (measurable_fst.sub measurable_snd))).aemeasurable]
  have hy (y : Space) : (∫⁻ x : Space, f y * g (x - y)) = f y * (∫⁻ x : Space, g x) := by
    rw [lintegral_const_mul (μ := volume) (f := fun x : Space => g (x - y)) (f y) (by fun_prop),
      lintegral_sub_right_eq_self g]
  simp_rw [hy]
  exact lintegral_mul_const _ hf

theorem half_power_sq (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
  rw [← ENNReal.rpow_mul_natCast]
  norm_num

theorem half_power_mul_self (a : ℝ≥0∞) : a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) = a := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * g x ∂μ) ^ 2 ≤ (∫⁻ x, f x ^ 2 ∂μ) * (∫⁻ x, g x ^ 2 ∂μ) := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hf.aemeasurable hg.aemeasurable
  have hs := pow_le_pow_left' hh 2
  simpa only [Pi.mul_apply, ENNReal.rpow_two, mul_pow, half_power_sq] using hs

theorem majorant_sq_le_two_one {f g : Space → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (x : Space) :
    majorant f g x ^ 2 ≤ majorant (fun y => f y ^ 2) g x * (∫⁻ y : Space, g y) := by
  have hh := lintegral_mul_sq_le (volume : Measure Space)
    (f := fun y => f y * g (x - y) ^ (1 / 2 : ℝ))
    (g := fun y => g (x - y) ^ (1 / 2 : ℝ)) (by fun_prop) (by fun_prop)
  have hprod (a b : ℝ≥0∞) : (a * b ^ (1 / 2 : ℝ)) * b ^ (1 / 2 : ℝ) = a * b := by
    rw [mul_assoc, half_power_mul_self]
  simpa only [hprod, mul_pow, half_power_sq, lintegral_sub_left_eq_self, majorant] using hh

/-- The `L² * L¹ → L²` squared integral estimate, valid for extended
nonnegative functions without additional finiteness assumptions. -/
theorem majorant_young_two_one {f g : Space → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x : Space, majorant f g x ^ 2) ≤
      (∫⁻ y : Space, f y ^ 2) * (∫⁻ z : Space, g z) ^ 2 := by
  calc
    _ ≤ ∫⁻ x : Space, majorant (fun y => f y ^ 2) g x * (∫⁻ y : Space, g y) :=
      lintegral_mono (majorant_sq_le_two_one hf hg)
    _ = (∫⁻ x : Space, majorant (fun y => f y ^ 2) g x) * (∫⁻ y : Space, g y) :=
      lintegral_mul_const _ (majorant_measurable (hf.pow_const 2) hg)
    _ = _ := by
      rw [integral_majorant (hf.pow_const 2) hg]
      ring

theorem young_split (a b : ℝ≥0∞) :
    (a ^ (3 / 5 : ℝ) * b ^ (3 / 4 : ℝ)) *
      (a ^ (2 / 5 : ℝ) * b ^ (1 / 4 : ℝ)) = a * b := by
  calc
    _ = (a ^ (3 / 5 : ℝ) * a ^ (2 / 5 : ℝ)) *
        (b ^ (3 / 4 : ℝ) * b ^ (1 / 4 : ℝ)) := by ac_rfl
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
        ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num

theorem majorant_sq_le_six_fifths_three_halves {f g : Space → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (x : Space) :
    majorant f g x ^ 2 ≤
      majorant (fun y => f y ^ (6 / 5 : ℝ)) (fun y => g y ^ (3 / 2 : ℝ)) x *
        ((∫⁻ y : Space, f y ^ (6 / 5 : ℝ)) ^ (2 / 3 : ℝ) *
          (∫⁻ y : Space, g y ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ)) := by
  have hcs := lintegral_mul_sq_le (volume : Measure Space)
    (f := fun y => f y ^ (3 / 5 : ℝ) * g (x - y) ^ (3 / 4 : ℝ))
    (g := fun y => f y ^ (2 / 5 : ℝ) * g (x - y) ^ (1 / 4 : ℝ))
    (by fun_prop) (by fun_prop)
  simp only [young_split, mul_pow, ← ENNReal.rpow_mul_natCast] at hcs
  norm_num at hcs
  have hconj : Real.HolderConjugate (3 / 2) 3 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure Space) hconj
    (f := fun y => f y ^ (4 / 5 : ℝ))
    (g := fun y => g (x - y) ^ (1 / 2 : ℝ)) (by fun_prop) (by fun_prop)
  simp only [Pi.mul_apply, ← ENNReal.rpow_mul] at hh
  norm_num at hh
  rw [lintegral_sub_left_eq_self (fun y => g y ^ (3 / 2 : ℝ)) x] at hh
  exact hcs.trans (mul_le_mul_of_nonneg_left hh (by positivity))

theorem power_one_mul (a : ℝ≥0∞) {p : ℝ} (hp : 0 ≤ p) : a * a ^ p = a ^ (1 + p) := by
  rw [ENNReal.rpow_add_of_nonneg 1 p (by norm_num) hp, ENNReal.rpow_one]

/-- The precise second Young inequality needed for the near part of the
pressure commutator. -/
theorem majorant_young_six_fifths_three_halves {f g : Space → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x : Space, majorant f g x ^ 2) ≤
      (∫⁻ y : Space, f y ^ (6 / 5 : ℝ)) ^ (5 / 3 : ℝ) *
        (∫⁻ z : Space, g z ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ) := by
  let F := ∫⁻ y : Space, f y ^ (6 / 5 : ℝ)
  let G := ∫⁻ y : Space, g y ^ (3 / 2 : ℝ)
  calc
    _ ≤ ∫⁻ x : Space,
        majorant (fun y => f y ^ (6 / 5 : ℝ)) (fun y => g y ^ (3 / 2 : ℝ)) x *
          (F ^ (2 / 3 : ℝ) * G ^ (1 / 3 : ℝ)) :=
      lintegral_mono (majorant_sq_le_six_fifths_three_halves hf hg)
    _ = (F * G) * (F ^ (2 / 3 : ℝ) * G ^ (1 / 3 : ℝ)) := by
      rw [lintegral_mul_const _
        (majorant_measurable (hf.pow_const _) (hg.pow_const _)),
        integral_majorant (hf.pow_const _) (hg.pow_const _)]
    _ = (F * F ^ (2 / 3 : ℝ)) * (G * G ^ (1 / 3 : ℝ)) := by ac_rfl
    _ = _ := by
      rw [power_one_mul F (by norm_num), power_one_mul G (by norm_num)]
      norm_num [F, G]

variable {𝕜 : Type*} [RCLike 𝕜]

def scalarConvolution (f g : Space → 𝕜) (x : Space) : 𝕜 :=
  ∫ y : Space, f y * g (x - y)

theorem scalarConvolution_aestronglyMeasurable {f g : Space → 𝕜}
    (hf : Measurable f) (hg : Measurable g) : AEStronglyMeasurable (scalarConvolution f g) :=
  ((hf.comp measurable_snd).mul
    (hg.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable.integral_prod_right'

theorem enorm_scalarConvolution_le (f g : Space → 𝕜) (x : Space) :
    ‖scalarConvolution f g x‖ₑ ≤ majorant (fun y => ‖f y‖ₑ) (fun y => ‖g y‖ₑ) x := by
  simpa only [scalarConvolution, majorant, enorm_mul] using
    (enorm_integral_le_lintegral_enorm (fun y : Space => f y * g (x - y)))

theorem eLpNorm_scalarConvolution_two_one {f g : Space → 𝕜}
    (hf : Measurable f) (hg : Measurable g) :
    eLpNorm (scalarConvolution f g) 2 volume ≤ eLpNorm f 2 volume * eLpNorm g 1 volume := by
  have hb := (lintegral_mono fun x => pow_le_pow_left' (enorm_scalarConvolution_le f g x) 2).trans
    (majorant_young_two_one hf.enorm hg.enorm)
  have hp := ENNReal.rpow_le_rpow hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num),
    eLpNorm_one_eq_lintegral_enorm]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast_mul] at hp
  norm_num at hp
  exact hp

theorem eLpNorm_scalarConvolution_six_fifths_three_halves {f g : Space → 𝕜}
    (hf : Measurable f) (hg : Measurable g) :
    eLpNorm (scalarConvolution f g) 2 volume ≤
      eLpNorm f (6 / 5) volume * eLpNorm g (3 / 2) volume := by
  have hb := (lintegral_mono fun x => pow_le_pow_left' (enorm_scalarConvolution_le f g x) 2).trans
    (majorant_young_six_fifths_three_halves hf.enorm hg.enorm)
  have hp := ENNReal.rpow_le_rpow hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 6 / 5) (by norm_num) (by finiteness),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 3 / 2) (by norm_num) (by finiteness)]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.toReal_div, ENNReal.rpow_two]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hp
  norm_num at hp
  exact hp

theorem scalarConvolution_memLp_two_one {f g : Space → 𝕜}
    (hf : Measurable f) (hg : Measurable g) (hf₂ : MemLp f 2) (hg₁ : MemLp g 1) :
    MemLp (scalarConvolution f g) 2 :=
  ⟨scalarConvolution_aestronglyMeasurable hf hg,
    (eLpNorm_scalarConvolution_two_one hf hg).trans_lt (ENNReal.mul_lt_top hf₂.2 hg₁.2)⟩

theorem scalarConvolution_memLp_six_fifths_three_halves {f g : Space → 𝕜}
    (hf : Measurable f) (hg : Measurable g) (hf₆ : MemLp f (6 / 5)) (hg₃ : MemLp g (3 / 2)) :
    MemLp (scalarConvolution f g) 2 :=
  ⟨scalarConvolution_aestronglyMeasurable hf hg,
    (eLpNorm_scalarConvolution_six_fifths_three_halves hf hg).trans_lt
      (ENNReal.mul_lt_top hf₆.2 hg₃.2)⟩

theorem ae_integrable_of_majorant_sq_finite {f g : Space → 𝕜}
    (hf : Measurable f) (hg : Measurable g)
    (hfin : (∫⁻ x : Space, majorant (fun y => ‖f y‖ₑ) (fun y => ‖g y‖ₑ) x ^ 2) < ⊤) :
    ∀ᵐ x ∂volume, Integrable (fun y : Space => f y * g (x - y)) := by
  have ha := ae_lt_top ((majorant_measurable hf.enorm hg.enorm).pow_const 2) hfin.ne
  filter_upwards [ha] with x hx
  have hmajor : majorant (fun y => ‖f y‖ₑ) (fun y => ‖g y‖ₑ) x < ⊤ := by
    by_contra hn
    have he := top_le_iff.mp (le_of_not_gt hn)
    simp only [he, ENNReal.top_pow (by norm_num : (2 : ℕ) ≠ 0), lt_self_iff_false] at hx
  refine ⟨(hf.mul (hg.comp (measurable_const.sub measurable_id))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [majorant, enorm_mul] using hmajor

/-- The convolution defining the far commutator term exists almost
everywhere; this is stronger than just bounding its totalized integral. -/
theorem ae_integrable_two_one {f g : Space → 𝕜}
    (hf : Measurable f) (hg : Measurable g) (hf₂ : MemLp f 2) (hg₁ : MemLp g 1) :
    ∀ᵐ x ∂volume, Integrable (fun y : Space => f y * g (x - y)) := by
  have hfm : (∫⁻ y : Space, ‖f y‖ₑ ^ 2) < ⊤ := by
    simpa using (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := 2) (by norm_num) (by norm_num) hf₂.2)
  have hgm : (∫⁻ y : Space, ‖g y‖ₑ) < ⊤ := by
    simpa only [eLpNorm_one_eq_lintegral_enorm] using hg₁.2
  apply ae_integrable_of_majorant_sq_finite hf hg
  exact (majorant_young_two_one hf.enorm hg.enorm).trans_lt (by finiteness)

/-- The near commutator term also defines an absolutely convergent
convolution almost everywhere. -/
theorem ae_integrable_six_fifths_three_halves {f g : Space → 𝕜}
    (hf : Measurable f) (hg : Measurable g) (hf₆ : MemLp f (6 / 5)) (hg₃ : MemLp g (3 / 2)) :
    ∀ᵐ x ∂volume, Integrable (fun y : Space => f y * g (x - y)) := by
  have hfm : (∫⁻ y : Space, ‖f y‖ₑ ^ (6 / 5 : ℝ)) < ⊤ := by
    simpa using (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := 6 / 5) (by norm_num) (by finiteness) hf₆.2)
  have hgm : (∫⁻ y : Space, ‖g y‖ₑ ^ (3 / 2 : ℝ)) < ⊤ := by
    simpa using (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := 3 / 2) (by norm_num) (by finiteness) hg₃.2)
  apply ae_integrable_of_majorant_sq_finite hf hg
  exact (majorant_young_six_fifths_three_halves hf.enorm hg.enorm).trans_lt (by finiteness)

theorem lpNorm_scalarConvolution_two_one {f g : Space → 𝕜}
    (hf : Measurable f) (hg : Measurable g) (hf₂ : MemLp f 2) (hg₁ : MemLp g 1) :
    lpNorm (scalarConvolution f g) 2 volume ≤ lpNorm f 2 volume * lpNorm g 1 volume := by
  have hb := ENNReal.toReal_mono (ne_of_lt (ENNReal.mul_lt_top hf₂.2 hg₁.2))
    (eLpNorm_scalarConvolution_two_one hf hg)
  simpa only [ENNReal.toReal_mul, toReal_eLpNorm (scalarConvolution_aestronglyMeasurable hf hg),
    toReal_eLpNorm hf₂.1, toReal_eLpNorm hg₁.1] using hb

theorem lpNorm_scalarConvolution_six_fifths_three_halves {f g : Space → 𝕜}
    (hf : Measurable f) (hg : Measurable g) (hf₆ : MemLp f (6 / 5)) (hg₃ : MemLp g (3 / 2)) :
    lpNorm (scalarConvolution f g) 2 volume ≤
      lpNorm f (6 / 5) volume * lpNorm g (3 / 2) volume := by
  have hb := ENNReal.toReal_mono (ne_of_lt (ENNReal.mul_lt_top hf₆.2 hg₃.2))
    (eLpNorm_scalarConvolution_six_fifths_three_halves hf hg)
  simpa only [ENNReal.toReal_mul, toReal_eLpNorm (scalarConvolution_aestronglyMeasurable hf hg),
    toReal_eLpNorm hf₆.1, toReal_eLpNorm hg₃.1] using hb

end NavierStokes.R3ConvolutionYoung
