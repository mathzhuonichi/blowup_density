import NSFormalization.Paper1.PeriodicSobolevHilbert

/-!
# The inverse periodic Laplacian on the native integer frequency lattice

The convention is that of Paper 1: coordinate derivatives have symbol
`2π i kᵢ`, and the Laplacian has symbol `-4π²|k|²`. We construct its
zero-mean inverse on arbitrary coefficient data, prove the exact coefficient
equation and uniqueness, and establish a uniform two-order multiplier bound.
Physical reconstruction and time regularity are separate obligations.
-/

noncomputable section
namespace NSFormalization.Paper1.PeriodicPressureSymbol
open scoped BigOperators

def laplaceEigenvalue (k : PeriodicFrequency) : ℝ :=
  (2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2

theorem weight_eq (k : PeriodicFrequency) :
    periodicFrequencyWeight k = 1 + laplaceEigenvalue k :=
  periodicFrequencyWeight_eq k

@[simp] theorem laplaceEigenvalue_zero : laplaceEigenvalue 0 = 0 := by
  simp [laplaceEigenvalue]

theorem laplaceEigenvalue_nonneg (k : PeriodicFrequency) :
    0 ≤ laplaceEigenvalue k := by
  unfold laplaceEigenvalue
  positivity

theorem lattice_gap {k : PeriodicFrequency} (hk : k ≠ 0) :
    1 ≤ ∑ i : Fin 3, (k i : ℝ) ^ 2 := by
  have hex : ∃ i, k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  obtain ⟨i, hi⟩ := hex
  have hint : (1 : ℤ) ≤ (k i) ^ 2 := by
    have : 0 < (k i) ^ 2 := sq_pos_of_ne_zero hi
    omega
  have hreal : (1 : ℝ) ≤ (k i : ℝ) ^ 2 := by exact_mod_cast hint
  exact hreal.trans (Finset.single_le_sum (fun j _ => sq_nonneg (k j : ℝ))
    (Finset.mem_univ i))

theorem one_le_laplaceEigenvalue {k : PeriodicFrequency} (hk : k ≠ 0) :
    1 ≤ laplaceEigenvalue k := by
  have hpi := Real.two_le_pi
  have hgap := lattice_gap hk
  have hfactor : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith
  exact (one_mul (1 : ℝ)).symm.le.trans
    (mul_le_mul hfactor hgap zero_le_one (sq_nonneg _))

def inverseSymbol (k : PeriodicFrequency) : ℂ :=
  -((laplaceEigenvalue k : ℂ)⁻¹)

def pressureCoeff (g : PeriodicFrequency → ℂ) (k : PeriodicFrequency) : ℂ :=
  inverseSymbol k * g k

@[simp] theorem inverseSymbol_zero : inverseSymbol 0 = 0 := by
  simp [inverseSymbol]

@[simp] theorem pressureCoeff_zero (g : PeriodicFrequency → ℂ) :
    pressureCoeff g 0 = 0 := by simp [pressureCoeff]

theorem laplaceEigenvalue_ne_zero {k : PeriodicFrequency} (hk : k ≠ 0) :
    laplaceEigenvalue k ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one
      (one_le_laplaceEigenvalue hk))

theorem inverseSymbol_equation {k : PeriodicFrequency} (hk : k ≠ 0) :
    -(laplaceEigenvalue k : ℂ) * inverseSymbol k = 1 := by
  have h : (laplaceEigenvalue k : ℂ) ≠ 0 := by
    exact_mod_cast laplaceEigenvalue_ne_zero hk
  simp [inverseSymbol, h]

theorem pressureCoeff_equation (g : PeriodicFrequency → ℂ) (hg : g 0 = 0)
    (k : PeriodicFrequency) :
    -(laplaceEigenvalue k : ℂ) * pressureCoeff g k = g k := by
  by_cases hk : k = 0
  · subst k; simp [hg]
  · rw [pressureCoeff, ← mul_assoc, inverseSymbol_equation hk, one_mul]

theorem pressureCoeff_unique (g p : PeriodicFrequency → ℂ) (hp : p 0 = 0)
    (heq : ∀ k, -(laplaceEigenvalue k : ℂ) * p k = g k) :
    p = pressureCoeff g := by
  funext k
  by_cases hk : k = 0
  · subst k; simp [hp]
  · have h : -(laplaceEigenvalue k : ℂ) ≠ 0 := by
      exact neg_ne_zero.mpr (by exact_mod_cast laplaceEigenvalue_ne_zero hk)
    apply mul_left_cancel₀ h
    rw [heq, pressureCoeff, ← mul_assoc, inverseSymbol_equation hk, one_mul]

theorem weighted_inverseSymbol_bound (k : PeriodicFrequency) :
    ‖(periodicFrequencyWeight k : ℂ) * inverseSymbol k‖ ≤ 2 := by
  by_cases hk : k = 0
  · subst k; simp
  · have heigen := one_le_laplaceEigenvalue hk
    have heigenpos : 0 < laplaceEigenvalue k := lt_of_lt_of_le zero_lt_one heigen
    rw [norm_mul, inverseSymbol, norm_neg, norm_inv, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ((one_le_periodicFrequencyWeight k).trans' zero_le_one),
      abs_of_pos heigenpos, weight_eq, ← div_eq_mul_inv]
    apply (div_le_iff₀ heigenpos).2
    linarith

def derivativeSymbol (i : Fin 3) (k : PeriodicFrequency) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ) * (k i : ℂ)

/-- Fourier data of `div f - ∑ᵢⱼ ∂ᵢ∂ⱼ Aᵢⱼ`, with `Aᵢⱼ = uᵢuⱼ`
in the Navier--Stokes application. No convolution or physical identity is assumed. -/
def pressureSourceCoeff (f : Fin 3 → PeriodicFrequency → ℂ)
    (A : Fin 3 → Fin 3 → PeriodicFrequency → ℂ) (k : PeriodicFrequency) : ℂ :=
  (∑ i, derivativeSymbol i k * f i k) -
    ∑ i, ∑ j, derivativeSymbol i k * derivativeSymbol j k * A i j k

@[simp] theorem pressureSourceCoeff_zero (f : Fin 3 → PeriodicFrequency → ℂ)
    (A : Fin 3 → Fin 3 → PeriodicFrequency → ℂ) : pressureSourceCoeff f A 0 = 0 := by
  simp [pressureSourceCoeff, derivativeSymbol]

theorem forced_pressureCoeff_equation (f : Fin 3 → PeriodicFrequency → ℂ)
    (A : Fin 3 → Fin 3 → PeriodicFrequency → ℂ) (k : PeriodicFrequency) :
    -(laplaceEigenvalue k : ℂ) * pressureCoeff (pressureSourceCoeff f A) k =
      pressureSourceCoeff f A k :=
  pressureCoeff_equation _ (pressureSourceCoeff_zero f A) k

end NSFormalization.Paper1.PeriodicPressureSymbol
