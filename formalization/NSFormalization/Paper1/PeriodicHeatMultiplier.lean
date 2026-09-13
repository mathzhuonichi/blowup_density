import NSFormalization.Paper1.PeriodicSobolevHilbert

/-!
# Native periodic heat multipliers

The carrier is complete square-summable Fourier data indexed by `ℤ³`. At any
Sobolev order its entries are the weighted coefficients. Multiplication by the
heat symbol commutes with that weight, so the contraction has no frequency
cutoff or dependence on the support cardinality. No ordinary `L²(ℝ³)`
representative is required.
-/
noncomputable section

namespace NSFormalization.Paper1.PeriodicHeatMultiplier
open scoped ENNReal

abbrev FourierHilbert := lp (fun _ : PeriodicFrequency => ℂ) 2

/-- The nonnegative eigenvalue of the negative Laplacian on the unit torus. -/
def laplaceEigenvalue (k : PeriodicFrequency) : ℝ := periodicFrequencyWeight k - 1

theorem laplaceEigenvalue_nonneg (k : PeriodicFrequency) :
    0 ≤ laplaceEigenvalue k := sub_nonneg.mpr (one_le_periodicFrequencyWeight k)

theorem laplaceEigenvalue_eq (k : PeriodicFrequency) :
    laplaceEigenvalue k = (2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 := by
  simp [laplaceEigenvalue, periodicFrequencyWeight_eq]

def heatSymbol (ν t : ℝ) (k : PeriodicFrequency) : ℝ :=
  Real.exp (-(ν * t) * laplaceEigenvalue k)

theorem heatSymbol_nonneg (ν t : ℝ) (k : PeriodicFrequency) :
    0 ≤ heatSymbol ν t k := (Real.exp_pos _).le

theorem heatSymbol_le_one {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (k : PeriodicFrequency) : heatSymbol ν t k ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hν ht))
    (laplaceEigenvalue_nonneg k)

@[simp] theorem heatSymbol_zero (ν : ℝ) (k : PeriodicFrequency) :
    heatSymbol ν 0 k = 1 := by simp [heatSymbol]

theorem heatSymbol_add (ν s t : ℝ) (k : PeriodicFrequency) :
    heatSymbol ν (s + t) k = heatSymbol ν s k * heatSymbol ν t k := by
  simp only [heatSymbol, ← Real.exp_add]
  congr 1
  ring

private theorem coeff_norm_le {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (f : FourierHilbert) (k : PeriodicFrequency) :
    ‖(heatSymbol ν t k : ℂ) * f k‖ ≤ ‖f k‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (heatSymbol_nonneg ν t k)]
  exact mul_le_of_le_one_left (norm_nonneg _) (heatSymbol_le_one hν ht k)

/-- The heat semigroup acts on arbitrary complete periodic Fourier data. -/
def heat {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (f : FourierHilbert) :
    FourierHilbert :=
  ⟨fun k => (heatSymbol ν t k : ℂ) * f k,
    (lp.memℓp f).norm.mono (coeff_norm_le hν ht f)⟩

@[simp] theorem heat_apply {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (f : FourierHilbert) (k : PeriodicFrequency) :
    heat hν ht f k = (heatSymbol ν t k : ℂ) * f k := rfl

theorem norm_heat_le {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (f : FourierHilbert) :
    ‖heat hν ht f‖ ≤ ‖f‖ :=
  lp.norm_mono (by norm_num) (coeff_norm_le hν ht f)

/-- Complex-linear, bounded realization of the periodic heat multiplier. -/
def heatCLM {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    FourierHilbert →L[ℂ] FourierHilbert :=
  LinearMap.mkContinuous
    { toFun := heat hν ht
      map_add' := fun f g => by ext k; simp [heat_apply, mul_add]
      map_smul' := fun c f => by ext k; simp [heat_apply, mul_left_comm] }
    1 (fun f => by simpa using norm_heat_le hν ht f)

@[simp] theorem heatCLM_apply {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (f : FourierHilbert) : heatCLM hν ht f = heat hν ht f := rfl

@[simp] theorem heat_zero {ν : ℝ} (hν : 0 ≤ ν) (f : FourierHilbert) :
    heat hν (le_refl 0) f = f := by
  ext k
  simp

theorem heat_add {ν s t : ℝ} (hν : 0 ≤ ν) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (f : FourierHilbert) :
    heat hν (add_nonneg hs ht) f = heat hν hs (heat hν ht f) := by
  ext k
  simp [heatSymbol_add, mul_assoc]

/-- A support-independent one-derivative heat estimate, including the zero mode. -/
theorem sqrt_weight_mul_heatSymbol_le {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (k : PeriodicFrequency) :
    Real.sqrt (periodicFrequencyWeight k) * heatSymbol ν t k ≤
      Real.sqrt (1 + 1 / (ν * t)) := by
  let a := ν * t
  let x := laplaceEigenvalue k
  let m := heatSymbol ν t k
  have ha : 0 < a := mul_pos hν ht
  have hx : 0 ≤ x := laplaceEigenvalue_nonneg k
  have hm : 0 ≤ m := heatSymbol_nonneg ν t k
  have hm1 : m ≤ 1 := heatSymbol_le_one hν.le ht.le k
  have hm2 : m ^ 2 = Real.exp (-(2 * a * x)) := by
    dsimp [m, heatSymbol, a, x]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hbound : (2 * a * x) * m ^ 2 ≤ 1 := by
    rw [hm2]
    exact (Real.mul_exp_neg_le_exp_neg_one _).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  have hxbound : x * m ^ 2 ≤ 1 / a := by
    apply (le_div_iff₀ ha).mpr
    have hnn : 0 ≤ a * x * m ^ 2 := by positivity
    nlinarith
  have hw : periodicFrequencyWeight k = 1 + x := by
    dsimp [x, laplaceEigenvalue]
    ring
  have hsq : (Real.sqrt (periodicFrequencyWeight k) * m) ^ 2 ≤ 1 + 1 / a := by
    rw [mul_pow, Real.sq_sqrt (by linarith [one_le_periodicFrequencyWeight k]), hw]
    nlinarith [sq_nonneg m]
  have hr : 0 ≤ 1 + 1 / a := by positivity
  have hrsq := Real.sq_sqrt hr
  have hrpos := Real.sqrt_nonneg (1 + 1 / a)
  change Real.sqrt (periodicFrequencyWeight k) * m ≤ Real.sqrt (1 + 1 / a)
  nlinarith [sq_nonneg (Real.sqrt (periodicFrequencyWeight k) * m -
    Real.sqrt (1 + 1 / a))]

/-- Weighted Fourier coefficients at one higher Sobolev order after heating. -/
def heatOneDerivative {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (f : FourierHilbert) : FourierHilbert :=
  ⟨fun k => ((Real.sqrt (periodicFrequencyWeight k) * heatSymbol ν t k : ℝ) : ℂ) * f k,
    ((lp.memℓp f).norm.const_mul (Real.sqrt (1 + 1 / (ν * t)))).mono (by
      intro k
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (heatSymbol_nonneg ν t k))]
      exact mul_le_mul_of_nonneg_right (sqrt_weight_mul_heatSymbol_le hν ht k)
        (norm_nonneg _))⟩

@[simp] theorem heatOneDerivative_apply {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (f : FourierHilbert) (k : PeriodicFrequency) :
    heatOneDerivative hν ht f k =
      ((Real.sqrt (periodicFrequencyWeight k) * heatSymbol ν t k : ℝ) : ℂ) * f k := rfl

/-- The complete-data `H^s → H^(s+1)` heat bound in weighted Fourier coordinates. -/
theorem norm_heatOneDerivative_le {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (f : FourierHilbert) :
    ‖heatOneDerivative hν ht f‖ ≤ Real.sqrt (1 + 1 / (ν * t)) * ‖f‖ := by
  have h := lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
    (x := heatOneDerivative hν ht f)
    (y := Real.sqrt (1 + 1 / (ν * t)) • f) (by
      intro k
      change ‖((Real.sqrt (periodicFrequencyWeight k) * heatSymbol ν t k : ℝ) : ℂ) * f k‖ ≤
        ‖Real.sqrt (1 + 1 / (ν * t)) • f k‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (heatSymbol_nonneg ν t k)),
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_right (sqrt_weight_mul_heatSymbol_le hν ht k)
        (norm_nonneg _))
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using h

end NSFormalization.Paper1.PeriodicHeatMultiplier

namespace NSFormalization.Paper1.PeriodicHeatMultiplier

/-- Coefficient-level composition of the one-derivative multiplier with heating.
This records the exact multiplier product without asserting a physical-space
Sobolev semigroup identity. -/
theorem heatOneDerivative_heat_apply {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (f : FourierHilbert) (k : PeriodicFrequency) :
    heatOneDerivative hν ht (heat hν.le ht.le f) k =
      ((Real.sqrt (periodicFrequencyWeight k) * heatSymbol ν t k : ℝ) : ℂ) *
        ((heatSymbol ν t k : ℂ) * f k) := by
  rw [heatOneDerivative_apply, heat_apply]

end NSFormalization.Paper1.PeriodicHeatMultiplier

namespace NSFormalization.Paper1.PeriodicHeatMultiplier


end NSFormalization.Paper1.PeriodicHeatMultiplier

namespace NSFormalization.Paper1.PeriodicHeatMultiplier

/-- Pointwise coefficient domination underlying the complete `lp` estimate. -/
theorem norm_heatOneDerivative_apply_le {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (f : FourierHilbert) (k : PeriodicFrequency) :
    ‖heatOneDerivative hν ht f k‖ ≤
      Real.sqrt (1 + 1 / (ν * t)) * ‖f k‖ := by
  rw [heatOneDerivative_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (heatSymbol_nonneg ν t k))]
  exact mul_le_mul_of_nonneg_right (sqrt_weight_mul_heatSymbol_le hν ht k)
    (norm_nonneg _)

end NSFormalization.Paper1.PeriodicHeatMultiplier

namespace NSFormalization.Paper1.PeriodicHeatMultiplier

/-- Pointwise coefficient form of the heat integrand used by Duhamel. -/
theorem heat_integrand_apply {ν τ t : ℝ} (hν : 0 ≤ ν)
    (hdelay : 0 ≤ max (t - τ) 0) (G : FourierHilbert) (k : PeriodicFrequency) :
    heat hν hdelay G k =
      ((heatSymbol ν (max (t - τ) 0) k : ℝ) : ℂ) * G k := by
  exact heat_apply hν hdelay G k

end NSFormalization.Paper1.PeriodicHeatMultiplier
