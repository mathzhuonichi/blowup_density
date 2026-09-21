import NSFormalization.Source.FourierTranslation

/-!
# The manuscripts' unitary angular-frequency convention

The papers use `(2*pi)^(-3/2) integral exp(-i x.xi) f(x) dx`. Mathlib uses
cycles per unit length. We define the exact unitary angular transform and
prove its weighted energies equivalent to the already verified Fourier norms.
-/
noncomputable section
namespace NSFormalization.Source
open NavierStokes.ProblemStatement MeasureTheory
open scoped FourierTransform RealInnerProductSpace

def frequencyUnit : ℝ := 2 * Real.pi

theorem frequencyUnit_pos : 0 < frequencyUnit := by unfold frequencyUnit; positivity

theorem frequencyUnit_ge_one : 1 ≤ frequencyUnit := by
  unfold frequencyUnit
  linarith [Real.pi_gt_three]

def angularFourier (f : Space → ℂ) (ξ : Space) : ℂ :=
  frequencyUnit ^ (-3 / 2 : ℝ) • 𝓕 f (frequencyUnit⁻¹ • ξ)

/-- This is exactly the integral normalization stated in the manuscripts. -/
theorem angularFourier_eq_integral (f : Space → ℂ) (ξ : Space) :
    angularFourier f ξ = frequencyUnit ^ (-3 / 2 : ℝ) •
      ∫ x : Space, Complex.exp (-((inner ℝ x ξ : ℝ) : ℂ) * Complex.I) • f x := by
  unfold angularFourier
  rw [Real.fourier_eq']
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [inner_smul_right]
  have he : -2 * Real.pi * (frequencyUnit⁻¹ * inner ℝ x ξ) = -inner ℝ x ξ := by
    unfold frequencyUnit
    field_simp [Real.pi_ne_zero]
  rw [he]
  simp

def angularSobolevSq (s : ℝ) (f : Space → ℂ) : ℝ :=
  ∫ ξ : Space, (1 + ‖ξ‖ ^ 2) ^ s * ‖angularFourier f ξ‖ ^ 2

def angularSobolevNorm (s : ℝ) (f : Space → ℂ) : ℝ := Real.sqrt (angularSobolevSq s f)

/-- The unitary amplitude exactly cancels the change of frequency volume. -/
theorem angularSobolevSq_eq_frequency_weight (s : ℝ) (f : Space → ℂ) :
    angularSobolevSq s f =
      ∫ ξ : Space, (1 + frequencyUnit ^ 2 * ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2 := by
  have hfirst : angularSobolevSq s f = (frequencyUnit ^ (-3 / 2 : ℝ)) ^ 2 *
      fourierSobolevSq s (concentratedForce frequencyUnit f) := by
    unfold angularSobolevSq angularFourier fourierSobolevSq
    simp_rw [fourier_concentratedForce f frequencyUnit frequencyUnit_pos,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun _ => by ring)
  rw [hfirst, fourierSobolevSq_concentrated s f frequencyUnit frequencyUnit_pos, ← mul_assoc]
  have hcoef : (frequencyUnit ^ (-3 / 2 : ℝ)) ^ 2 * frequencyUnit ^ 3 = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul frequencyUnit_pos.le]
    norm_num [frequencyUnit_pos.ne']
  rw [hcoef, one_mul]

theorem frequency_weight_equivalence {c s r : ℝ} (hc : 1 ≤ c) :
    (1 + c ^ 2 * r ^ 2) ^ s ≤ c ^ (2 * |s|) * (1 + r ^ 2) ^ s ∧
    (1 + r ^ 2) ^ s ≤ c ^ (2 * |s|) * (1 + c ^ 2 * r ^ 2) ^ s := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hbase : 1 + r ^ 2 ≤ 1 + c ^ 2 * r ^ 2 := by
    nlinarith [sq_nonneg r, sq_nonneg (c - 1)]
  have hC : 1 ≤ c ^ (2 * |s|) := Real.one_le_rpow hc (by positivity)
  by_cases hs : 0 ≤ s
  · refine ⟨?_, ?_⟩
    · simpa only [abs_of_nonneg hs] using positive_weight_scale (r := r) hs hc
    · exact (Real.rpow_le_rpow (by positivity) hbase hs).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg (by positivity) _) hC)
  · have hs0 : s ≤ 0 := le_of_not_ge hs
    refine ⟨?_, ?_⟩
    · exact (Real.rpow_le_rpow_of_nonpos (by positivity) hbase hs0).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg (by positivity) _) hC)
    · have hscaled : c ^ (2 * s) * (1 + r ^ 2) ^ s ≤ (1 + c ^ 2 * r ^ 2) ^ s := by
        calc
          c ^ (2 * s) * (1 + r ^ 2) ^ s = (c ^ 2 * (1 + r ^ 2)) ^ s := by
            rw [Real.mul_rpow (by positivity) (by positivity)]
            congr 1
            rw [← Real.rpow_natCast c 2, ← Real.rpow_mul hc0.le]
            norm_num
          _ ≤ (1 + c ^ 2 * r ^ 2) ^ s :=
            Real.rpow_le_rpow_of_nonpos (by positivity)
              (by nlinarith [sq_nonneg (c - 1)]) hs0
      have hm := mul_le_mul_of_nonneg_left hscaled (Real.rpow_nonneg hc0.le (-2 * s))
      have hcancel : c ^ (-2 * s) * c ^ (2 * s) = 1 := by
        rw [← Real.rpow_add hc0]
        ring_nf
        exact Real.rpow_zero _
      rw [← mul_assoc, hcancel, one_mul] at hm
      simpa only [abs_of_nonpos hs0, mul_neg, neg_mul] using hm

/-- Actual weighted integrals for the two Fourier conventions are equivalent,
with explicit positive constants depending only on the Sobolev order. -/
theorem angularSobolevSq_equivalence (s : ℝ) (f : Space → ℂ)
    (hF : Continuous (𝓕 f))
    (hint : Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2)) :
    angularSobolevSq s f ≤ frequencyUnit ^ (2 * |s|) * fourierSobolevSq s f ∧
    fourierSobolevSq s f ≤ frequencyUnit ^ (2 * |s|) * angularSobolevSq s f := by
  let G : Space → ℝ := fun ξ => (1 + frequencyUnit ^ 2 * ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2
  let C := frequencyUnit ^ (2 * |s|)
  have hupper (ξ : Space) : G ξ ≤ C * ((1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2) := by
    have h := mul_le_mul_of_nonneg_right
      (frequency_weight_equivalence (s := s) (r := ‖ξ‖) frequencyUnit_ge_one).1 (sq_nonneg ‖𝓕 f ξ‖)
    simpa only [G, C, mul_assoc] using h
  have hG : Integrable G := (hint.const_mul C).mono'
    (scaled_bessel_continuous s frequencyUnit hF).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [G]; positivity)]
      exact hupper ξ))
  rw [angularSobolevSq_eq_frequency_weight]
  constructor
  · have h := integral_mono hG (hint.const_mul C) hupper
    simpa only [integral_const_mul, G, C, fourierSobolevSq] using h
  · have h := integral_mono hint (hG.const_mul C) (fun ξ => by
      have hh := mul_le_mul_of_nonneg_right
        (frequency_weight_equivalence (s := s) (r := ‖ξ‖) frequencyUnit_ge_one).2 (sq_nonneg ‖𝓕 f ξ‖)
      simpa only [G, C, mul_assoc] using hh)
    simpa only [integral_const_mul, G, C, fourierSobolevSq] using h

theorem sqrt_frequency_constant (s E : ℝ) :
    Real.sqrt (frequencyUnit ^ (2 * |s|) * E) = frequencyUnit ^ |s| * Real.sqrt E := by
  rw [Real.sqrt_mul (Real.rpow_nonneg frequencyUnit_pos.le _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul frequencyUnit_pos.le]
  congr 2
  ring

theorem angularSobolevNorm_equivalence (s : ℝ) (f : Space → ℂ)
    (hF : Continuous (𝓕 f))
    (hint : Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2)) :
    angularSobolevNorm s f ≤ frequencyUnit ^ |s| * fourierSobolevNorm s f ∧
    fourierSobolevNorm s f ≤ frequencyUnit ^ |s| * angularSobolevNorm s f := by
  obtain ⟨h₁, h₂⟩ := angularSobolevSq_equivalence s f hF hint
  exact ⟨(Real.sqrt_le_sqrt h₁).trans_eq (sqrt_frequency_constant s _),
    (Real.sqrt_le_sqrt h₂).trans_eq (sqrt_frequency_constant s _)⟩

end NSFormalization.Source
