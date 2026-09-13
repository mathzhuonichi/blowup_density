import NavierStokes.R3PressureCutoff

/-!
# Weighted interpolation for the pressure and transport terms

These estimates use the global `L²` norm of a velocity and the `L⁶` norm
of its fourth-power cutoff. The exponents leave strictly less than two
powers of the localized gradient in the energy error.
-/

noncomputable section
namespace NavierStokes.R3WeightedLp

open Set Filter MeasureTheory ProblemStatement
open scoped ENNReal

private theorem four_mul_three_halves : (4 : ℝ≥0∞) * ENNReal.ofReal (3 / 2) = 6 := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul]

private theorem four_mul_half : (4 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 2 := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul]

private theorem four_thirds_mul_three_halves : (4 / 3 : ℝ≥0∞) * ENNReal.ofReal (3 / 2) = 2 := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul]

private theorem holder_four_four_two : ENNReal.HolderTriple 4 4 2 := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

private theorem holder_four_four_thirds_one : ENNReal.HolderTriple 4 (4 / 3) 1 := by
  have hne : (4 / 3 : ℝ≥0∞) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

theorem lpNorm_mul_le {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    {f g : Space → ℝ} (hf : MemLp f p) (hg : MemLp g q) :
    lpNorm (fun x => f x * g x) r volume ≤ lpNorm f p volume * lpNorm g q volume := by
  change lpNorm (f * g) r volume ≤ _
  have h := eLpNorm_smul_le_mul_eLpNorm (p := p) (q := q) (r := r) hg.1 hf.1
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top hf.2.ne hg.2.ne) h
  simpa only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    toReal_eLpNorm (hf.1.mul hg.1), toReal_eLpNorm hf.1, toReal_eLpNorm hg.1] using ht

theorem memLp_nonneg_rpow {f : Space → ℝ} (hm : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    {p : ℝ≥0∞} {q : ℝ} (hq : 0 < q) (hf : MemLp f (p * ENNReal.ofReal q)) :
    MemLp (fun x => f x ^ q) p := by
  have he := eLpNorm_norm_rpow (p := p) (μ := (volume : Measure Space)) f hq
  simp only [Real.norm_eq_abs, abs_of_nonneg (hpos _)] at he
  refine ⟨(hm.pow_const q).aestronglyMeasurable, ?_⟩
  rw [he]
  finiteness

theorem lpNorm_nonneg_rpow {f : Space → ℝ} (hm : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    {p : ℝ≥0∞} {q : ℝ} (hq : 0 < q) :
    lpNorm (fun x => f x ^ q) p volume = lpNorm f (p * ENNReal.ofReal q) volume ^ q := by
  have he := eLpNorm_norm_rpow (p := p) (μ := (volume : Measure Space)) f hq
  simp only [Real.norm_eq_abs, abs_of_nonneg (hpos _)] at he
  rw [← toReal_eLpNorm (hm.pow_const q).aestronglyMeasurable, he, ← ENNReal.toReal_rpow,
    toReal_eLpNorm hm.aestronglyMeasurable]

def fourthWeight (φ W : Space → ℝ) (x : Space) : ℝ := φ x ^ 4 * W x

def sixthQuadratic (φ W : Space → ℝ) (x : Space) : ℝ := φ x ^ 6 * W x ^ 2

theorem sixthQuadratic_factor {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 6 * b ^ 2 = (a ^ 4 * b) ^ (3 / 2 : ℝ) * b ^ (1 / 2 : ℝ) := by
  rw [Real.mul_rpow (pow_nonneg ha 4) hb, ← Real.rpow_natCast_mul ha, mul_assoc,
    ← Real.rpow_add_of_nonneg hb (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num

theorem sixthQuadratic_memLp {φ W : Space → ℝ} (hφ : Measurable φ) (hW : Measurable W)
    (hφ0 : ∀ x, 0 ≤ φ x) (hW0 : ∀ x, 0 ≤ W x)
    (hW₂ : MemLp W 2) (hA₆ : MemLp (fourthWeight φ W) 6) : MemLp (sixthQuadratic φ W) 2 := by
  have hAm : Measurable (fourthWeight φ W) := (hφ.pow_const 4).mul hW
  have hA0 : ∀ x, 0 ≤ fourthWeight φ W x := fun x => mul_nonneg (pow_nonneg (hφ0 x) 4) (hW0 x)
  have hA := memLp_nonneg_rpow (p := 4) (q := 3 / 2) hAm hA0 (by norm_num) (by rw [four_mul_three_halves]; exact hA₆)
  have hB := memLp_nonneg_rpow (p := 4) (q := 1 / 2) hW hW0 (by norm_num) (by rw [four_mul_half]; exact hW₂)
  have : ENNReal.HolderTriple 4 4 2 := holder_four_four_two
  convert! hB.mul' (r := 2) hA using 1
  funext x
  exact sixthQuadratic_factor (hφ0 x) (hW0 x)

theorem sixthQuadratic_lpNorm {φ W : Space → ℝ} (hφ : Measurable φ) (hW : Measurable W)
    (hφ0 : ∀ x, 0 ≤ φ x) (hW0 : ∀ x, 0 ≤ W x)
    (hW₂ : MemLp W 2) (hA₆ : MemLp (fourthWeight φ W) 6) :
    lpNorm (sixthQuadratic φ W) 2 volume ≤
      lpNorm (fourthWeight φ W) 6 volume ^ (3 / 2 : ℝ) * lpNorm W 2 volume ^ (1 / 2 : ℝ) := by
  have hAm : Measurable (fourthWeight φ W) := (hφ.pow_const 4).mul hW
  have hA0 : ∀ x, 0 ≤ fourthWeight φ W x := fun x => mul_nonneg (pow_nonneg (hφ0 x) 4) (hW0 x)
  have hA := memLp_nonneg_rpow (p := 4) (q := 3 / 2) hAm hA0 (by norm_num) (by rw [four_mul_three_halves]; exact hA₆)
  have hB := memLp_nonneg_rpow (p := 4) (q := 1 / 2) hW hW0 (by norm_num) (by rw [four_mul_half]; exact hW₂)
  have : ENNReal.HolderTriple 4 4 2 := holder_four_four_two
  have hb := lpNorm_mul_le (r := 2) hA hB
  rw [lpNorm_nonneg_rpow hAm hA0 (by norm_num), lpNorm_nonneg_rpow hW hW0 (by norm_num)] at hb
  simp only [four_mul_three_halves, four_mul_half] at hb
  have he : sixthQuadratic φ W = fun x => (fourthWeight φ W x) ^ (3 / 2 : ℝ) * W x ^ (1 / 2 : ℝ) := by
    funext x
    exact sixthQuadratic_factor (hφ0 x) (hW0 x)
  simpa only [he] using hb

theorem lpNorm_mono_ae_real {p : ℝ≥0∞} {f : Space → ℂ} {g : Space → ℝ}
    (hf : AEStronglyMeasurable f) (hg : MemLp g p) (h : ∀ᵐ x ∂volume, ‖f x‖ ≤ g x) :
    lpNorm f p volume ≤ lpNorm g p volume := by
  have hh := ENNReal.toReal_mono hg.2.ne (eLpNorm_mono_ae_real (p := p) h)
  simpa only [toReal_eLpNorm hf, toReal_eLpNorm hg.1] using hh

theorem fifthQuadratic_le {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (_hb : 0 ≤ b) :
    a ^ 5 * b ^ 2 ≤ (a ^ 4 * b) * b := by
  have hpow : a ^ 5 ≤ a ^ 4 := by
    calc
      a ^ 5 = a ^ 4 * a := by ring
      _ ≤ a ^ 4 * 1 := mul_le_mul_of_nonneg_left ha.2 (pow_nonneg ha.1 4)
      _ = _ := mul_one _
  nlinarith [sq_nonneg b, mul_le_mul_of_nonneg_right hpow (sq_nonneg b)]

/-- The cubic cutoff transport error has only `3/2` powers of the weighted `L⁶` norm. -/
theorem cubic_lpNorm {φ W : Space → ℝ} (hφ : Measurable φ) (hW : Measurable W)
    (hφrange : ∀ x, φ x ∈ Icc (0 : ℝ) 1) (hW0 : ∀ x, 0 ≤ W x)
    (hW₂ : MemLp W 2) (hA₆ : MemLp (fourthWeight φ W) 6) :
    lpNorm (fun x => φ x ^ 7 * W x ^ 3) 1 volume ≤
      lpNorm (fourthWeight φ W) 6 volume ^ (3 / 2 : ℝ) * lpNorm W 2 volume ^ (3 / 2 : ℝ) := by
  have hAm : Measurable (fourthWeight φ W) := (hφ.pow_const 4).mul hW
  have hA0 : ∀ x, 0 ≤ fourthWeight φ W x := fun x => mul_nonneg (pow_nonneg (hφrange x).1 4) (hW0 x)
  have hA := memLp_nonneg_rpow (p := 4) (q := 3 / 2) hAm hA0 (by norm_num) (by rw [four_mul_three_halves]; exact hA₆)
  have hB := memLp_nonneg_rpow (p := 4 / 3) (q := 3 / 2) hW hW0 (by norm_num) (by rw [four_thirds_mul_three_halves]; exact hW₂)
  have : ENNReal.HolderTriple 4 (4 / 3) 1 := holder_four_four_thirds_one
  have hAB : MemLp (fun x => (fourthWeight φ W x) ^ (3 / 2 : ℝ) * W x ^ (3 / 2 : ℝ)) 1 := hB.mul' hA
  apply (lpNorm_mono_real hAB (fun x => ?_)).trans
  · have hb := lpNorm_mul_le (r := 1) hA hB
    rw [lpNorm_nonneg_rpow hAm hA0 (by norm_num), lpNorm_nonneg_rpow hW hW0 (by norm_num)] at hb
    simp only [four_mul_three_halves, four_thirds_mul_three_halves] at hb
    exact hb
  · have hφx := (hφrange x).1
    have hWx := hW0 x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have he : (fourthWeight φ W x) ^ (3 / 2 : ℝ) * W x ^ (3 / 2 : ℝ) = φ x ^ 6 * W x ^ 3 := by
      unfold fourthWeight
      rw [Real.mul_rpow (pow_nonneg (hφrange x).1 4) (hW0 x),
        ← Real.rpow_natCast_mul (hφrange x).1, mul_assoc,
        ← Real.rpow_add_of_nonneg (hW0 x) (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      norm_num
    rw [he]
    have hpow : φ x ^ 7 ≤ φ x ^ 6 := by
      simpa only [pow_succ, mul_one] using
        mul_le_mul_of_nonneg_left (hφrange x).2 (pow_nonneg (hφrange x).1 6)
    exact mul_le_mul_of_nonneg_right hpow (pow_nonneg (hW0 x) 3)


theorem lpNorm_add_two_mul_le {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : Space → ℝ}
    (hf : MemLp f p) : lpNorm (fun x => f x + 2 * g x) p volume ≤
      lpNorm f p volume + 2 * lpNorm g p volume := by
  change lpNorm (f + (2 : ℝ) • g) p volume ≤ _
  have hh := lpNorm_add_le (g := (2 : ℝ) • g) hf hp
  simpa only [lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hh

private theorem holder_six_two_three_halves : ENNReal.HolderTriple 6 2 (3 / 2) := by
  have hne : (3 / 2 : ℝ≥0∞) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

/-- The full difference stress is integrable using just the two velocities' `L²` norms. -/
theorem stress_L1 {U W : Space → ℝ} {g : Space → ℂ}
    (hWm : Measurable W) (hgm : Measurable g) (hW0 : ∀ x, 0 ≤ W x)
    (hU₂ : MemLp U 2) (hW₂ : MemLp W 2)
    (hb : ∀ x, ‖g x‖ ≤ W x ^ 2 + 2 * (U x * W x)) :
    MemLp g 1 ∧ lpNorm g 1 volume ≤ lpNorm W 2 volume ^ 2 +
      2 * (lpNorm U 2 volume * lpNorm W 2 volume) := by
  have hQ : MemLp (fun x => W x ^ 2) 1 := by
    simpa only [Real.rpow_two] using memLp_nonneg_rpow (p := 1) (q := 2)
      hWm hW0 (by norm_num) (by norm_num; exact hW₂)
  have hH : MemLp (fun x => U x * W x) 1 := hW₂.mul' hU₂
  have hM : MemLp (fun x => W x ^ 2 + 2 * (U x * W x)) 1 := hQ.add (hH.const_mul 2)
  refine ⟨hM.mono' hgm.aestronglyMeasurable (Eventually.of_forall hb), ?_⟩
  apply (lpNorm_mono_real hM hb).trans
  have hQnorm : lpNorm (fun x => W x ^ 2) 1 volume = lpNorm W 2 volume ^ 2 := by
    simpa using lpNorm_nonneg_rpow (p := 1) (q := 2) hWm hW0 (by norm_num)
  have hh := lpNorm_add_two_mul_le (by norm_num : (1 : ℝ≥0∞) ≤ 1) (g := fun x => U x * W x) hQ
  rw [hQnorm] at hh
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (lpNorm_mul_le (r := 1) hU₂ hW₂) (by norm_num : (0 : ℝ) ≤ 2)))

/-- The fifth-power stress bound needed by the near commutator kernel. -/
theorem stress_weight_five {R L : ℝ} {φ U W : Space → ℝ} {g : Space → ℂ}
    (hφ : R3PressureCommutator.Cutoff R L φ) (_hWm : Measurable W) (hgm : Measurable g)
    (hU0 : ∀ x, 0 ≤ U x) (hW0 : ∀ x, 0 ≤ W x)
    (hU₆ : MemLp U 6) (hW₂ : MemLp W 2) (hA₆ : MemLp (fourthWeight φ W) 6)
    (hb : ∀ x, ‖g x‖ ≤ W x ^ 2 + 2 * (U x * W x)) :
    MemLp (R3PressureCommutator.weightedNorm φ g) (3 / 2) ∧
      lpNorm (R3PressureCommutator.weightedNorm φ g) (3 / 2) volume ≤
        lpNorm (fourthWeight φ W) 6 volume * lpNorm W 2 volume +
          2 * (lpNorm U 6 volume * lpNorm W 2 volume) := by
  have : ENNReal.HolderTriple 6 2 (3 / 2) := holder_six_two_three_halves
  have hQ : MemLp (fun x => fourthWeight φ W x * W x) (3 / 2) := hW₂.mul' hA₆
  have hH : MemLp (fun x => U x * W x) (3 / 2) := hW₂.mul' hU₆
  have hM : MemLp (fun x => fourthWeight φ W x * W x + 2 * (U x * W x)) (3 / 2) :=
    hQ.add (hH.const_mul 2)
  have hp (x : Space) : ‖R3PressureCommutator.weightedNorm φ g x‖ ≤
      fourthWeight φ W x * W x + 2 * (U x * W x) := by
    have hp5 : 0 ≤ φ x ^ 5 := pow_nonneg (hφ.range x).1 5
    have hle5 : φ x ^ 5 ≤ 1 := pow_le_one₀ (hφ.range x).1 (hφ.range x).2
    have hUW : 0 ≤ U x * W x := mul_nonneg (hU0 x) (hW0 x)
    rw [R3PressureCommutator.weightedNorm, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hp5 (norm_nonneg _))]
    have h₁ := mul_le_mul_of_nonneg_left (hb x) hp5
    have h₂ := fifthQuadratic_le (hφ.range x) (hW0 x)
    have h₃ := mul_le_mul_of_nonneg_right hle5 hUW
    unfold fourthWeight
    nlinarith
  have hm : Measurable (R3PressureCommutator.weightedNorm φ g) :=
    (hφ.measurable.pow_const 5).mul hgm.norm
  refine ⟨hM.mono' hm.aestronglyMeasurable (Eventually.of_forall hp), ?_⟩
  apply (lpNorm_mono_real hM hp).trans
  have hh := lpNorm_add_two_mul_le (by apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp; norm_num : (1 : ℝ≥0∞) ≤ 3 / 2) (g := fun x => U x * W x) hQ
  exact hh.trans (add_le_add (lpNorm_mul_le (r := 3 / 2) hA₆ hW₂)
    (mul_le_mul_of_nonneg_left (lpNorm_mul_le (r := 3 / 2) hU₆ hW₂) (by norm_num : (0 : ℝ) ≤ 2)))

/-- The sixth-power stress bound used in the `L²` part of the pressure. -/
theorem stress_weight_six {R L : ℝ} {φ U W : Space → ℝ} {g : Space → ℂ}
    (hφ : R3PressureCommutator.Cutoff R L φ) (hWm : Measurable W) (hgm : Measurable g)
    (hU0 : ∀ x, 0 ≤ U x) (hW0 : ∀ x, 0 ≤ W x)
    (hUinf : MemLp U ⊤) (hW₂ : MemLp W 2) (hA₆ : MemLp (fourthWeight φ W) 6)
    (hb : ∀ x, ‖g x‖ ≤ W x ^ 2 + 2 * (U x * W x)) :
    MemLp (fun x => R3PressureCutoff.powerCutoff φ x * g x) 2 ∧
      lpNorm (fun x => R3PressureCutoff.powerCutoff φ x * g x) 2 volume ≤
        lpNorm (fourthWeight φ W) 6 volume ^ (3 / 2 : ℝ) * lpNorm W 2 volume ^ (1 / 2 : ℝ) +
          2 * (lpNorm U ⊤ volume * lpNorm W 2 volume) := by
  have hQ := sixthQuadratic_memLp hφ.measurable hWm (fun x => (hφ.range x).1) hW0 hW₂ hA₆
  have hH : MemLp (fun x => U x * W x) 2 := hW₂.mul' hUinf
  have hM : MemLp (fun x => sixthQuadratic φ W x + 2 * (U x * W x)) 2 := hQ.add (hH.const_mul 2)
  have hp (x : Space) : ‖R3PressureCutoff.powerCutoff φ x * g x‖ ≤
      sixthQuadratic φ W x + 2 * (U x * W x) := by
    have hp6 : 0 ≤ φ x ^ 6 := pow_nonneg (hφ.range x).1 6
    have hle6 : φ x ^ 6 ≤ 1 := pow_le_one₀ (hφ.range x).1 (hφ.range x).2
    have hUW : 0 ≤ U x * W x := mul_nonneg (hU0 x) (hW0 x)
    rw [norm_mul, R3PressureCutoff.powerCutoff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp6]
    have h₁ := mul_le_mul_of_nonneg_left (hb x) hp6
    have h₂ := mul_le_mul_of_nonneg_right hle6 hUW
    unfold sixthQuadratic
    nlinarith
  have hm : Measurable (fun x => R3PressureCutoff.powerCutoff φ x * g x) :=
    (R3PressureCutoff.powerCutoff_measurable hφ).mul hgm
  refine ⟨hM.mono' hm.aestronglyMeasurable (Eventually.of_forall hp), ?_⟩
  apply (lpNorm_mono_real hM hp).trans
  have hh := lpNorm_add_two_mul_le (by norm_num : (1 : ℝ≥0∞) ≤ 2) (g := fun x => U x * W x) hQ
  exact hh.trans (add_le_add
    (sixthQuadratic_lpNorm hφ.measurable hWm (fun x => (hφ.range x).1) hW0 hW₂ hA₆)
    (mul_le_mul_of_nonneg_left (lpNorm_mul_le (r := 2) hUinf hW₂) (by norm_num : (0 : ℝ) ≤ 2)))

end NavierStokes.R3WeightedLp
