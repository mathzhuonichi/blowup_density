import NSFormalization.Paper1.PeriodicPressureSymbol

/-!
# Coefficient-level periodic pressure operators

This file packages the inverse Laplace multiplier as linear maps on raw Fourier
coefficient functions.  No `lp` coercions or reconstruction statements occur
here; those belong to later analytic layers.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicPressureSymbol
open scoped BigOperators

/-- The coefficient-level periodic Laplace multiplier. -/
def laplaceOperator : (PeriodicFrequency → ℂ) →ₗ[ℂ] (PeriodicFrequency → ℂ) :=
  LinearMap.pi (fun k => (LinearMap.proj k).smulRight (-(laplaceEigenvalue k : ℂ)))

@[simp] theorem laplaceOperator_apply (g : PeriodicFrequency → ℂ)
    (k : PeriodicFrequency) : laplaceOperator g k = -(laplaceEigenvalue k : ℂ) * g k := by
  simp [laplaceOperator]
  ring

/-- The zero-mean inverse Laplace multiplier on raw coefficients. -/
def pressureOperator : (PeriodicFrequency → ℂ) →ₗ[ℂ] (PeriodicFrequency → ℂ) :=
  LinearMap.pi (fun k => (LinearMap.proj k).smulRight (inverseSymbol k))

@[simp] theorem pressureOperator_apply (g : PeriodicFrequency → ℂ)
    (k : PeriodicFrequency) : pressureOperator g k = pressureCoeff g k := by
  simp [pressureOperator, pressureCoeff]
  ring

@[simp] theorem pressureOperator_zero_mode (g : PeriodicFrequency → ℂ) :
    pressureOperator g 0 = 0 := by simp [pressureOperator]

/-- The inverse multiplier solves the coefficient Poisson equation for
zero-mode-compatible data. -/
theorem laplaceOperator_pressureOperator (g : PeriodicFrequency → ℂ)
    (hg : g 0 = 0) : laplaceOperator (pressureOperator g) = g := by
  funext k
  rw [laplaceOperator_apply, pressureOperator_apply]
  exact pressureCoeff_equation g hg k

/-- Uniqueness of the zero-mode-normalized inverse at coefficient level. -/
theorem pressureOperator_unique (g p : PeriodicFrequency → ℂ)
    (hp : p 0 = 0)
    (heq : laplaceOperator p = g) :
    p = pressureOperator g := by
  have hpu : p = pressureCoeff g := by
    apply pressureCoeff_unique g p hp
    intro k
    have hk := congrFun heq k
    simpa only [laplaceOperator_apply] using hk
  have hop : pressureOperator g = pressureCoeff g := by
    funext k
    exact pressureOperator_apply g k
  rw [hop]
  exact hpu


/-- The pressure multiplier cannot create Fourier support: every nonzero output
coefficient comes from a nonzero input coefficient. -/
theorem pressureOperator_support_subset (g : PeriodicFrequency → ℂ) :
    Function.support (pressureOperator g) ⊆ Function.support g := by
  intro k hk
  intro hg
  apply hk
  rw [pressureOperator_apply]
  simp [pressureCoeff, hg]

/-- A finite-support coefficient input produces a finite-support pressure
coefficient output. This is a purely algebraic statement and carries no
summability or `lp` assertion. -/
theorem pressureOperator_finite_support {g : PeriodicFrequency → ℂ}
    (hg : (Function.support g).Finite) :
    (Function.support (pressureOperator g)).Finite :=
  hg.subset (pressureOperator_support_subset g)

/-- Truncation to a finite frequency set commutes with the coefficient
pressure multiplier on that set. -/
def pressureOperatorOn (S : Finset PeriodicFrequency)
    (g : PeriodicFrequency → ℂ) : PeriodicFrequency → ℂ :=
  fun k => if k ∈ S then pressureOperator g k else 0

@[simp] theorem pressureOperatorOn_apply_mem {S : Finset PeriodicFrequency}
    {g : PeriodicFrequency → ℂ} {k : PeriodicFrequency} (hk : k ∈ S) :
    pressureOperatorOn S g k = pressureOperator g k := by
  simp [pressureOperatorOn, hk]

@[simp] theorem pressureOperatorOn_apply_not_mem {S : Finset PeriodicFrequency}
    {g : PeriodicFrequency → ℂ} {k : PeriodicFrequency} (hk : k ∉ S) :
    pressureOperatorOn S g k = 0 := by
  simp [pressureOperatorOn, hk]

@[simp] theorem pressureOperatorOn_zero_mode {S : Finset PeriodicFrequency}
    (g : PeriodicFrequency → ℂ) :
    pressureOperatorOn S g 0 = 0 := by
  by_cases h : 0 ∈ S <;> simp [pressureOperatorOn, h]

/-- Frequency truncation on raw coefficient data. -/
def truncateCoeffs (S : Finset PeriodicFrequency)
    (g : PeriodicFrequency → ℂ) : PeriodicFrequency → ℂ :=
  fun k => if k ∈ S then g k else 0

/-- Applying the inverse multiplier before or after a finite truncation gives
identical coefficients. -/
theorem pressureOperator_truncateCoeffs (S : Finset PeriodicFrequency)
    (g : PeriodicFrequency → ℂ) :
    pressureOperator (truncateCoeffs S g) = pressureOperatorOn S g := by
  funext k
  by_cases hk : k ∈ S <;>
    simp [pressureOperatorOn, pressureOperator_apply, pressureCoeff, truncateCoeffs, hk]

/-- Finite frequency pressure recovery solves the truncated Poisson equation
when the original source has zero constant coefficient. -/
theorem laplaceOperator_pressureOperatorOn (S : Finset PeriodicFrequency)
    (g : PeriodicFrequency → ℂ) (hg : g 0 = 0) :
    laplaceOperator (pressureOperatorOn S g) = truncateCoeffs S g := by
  rw [← pressureOperator_truncateCoeffs]
  apply laplaceOperator_pressureOperator
  simp [truncateCoeffs, hg]

/-- Pressure normalization is also a left inverse on zero-mode-normalized
coefficient data. Without this hypothesis it would discard the constant mode. -/
theorem pressureOperator_laplaceOperator (p : PeriodicFrequency → ℂ)
    (hp : p 0 = 0) : pressureOperator (laplaceOperator p) = p :=
  (pressureOperator_unique (laplaceOperator p) p hp rfl).symm

/-- The truncated pressure has no coefficients outside the chosen frequency set. -/
theorem pressureOperatorOn_support_subset (S : Finset PeriodicFrequency)
    (g : PeriodicFrequency → ℂ) :
    Function.support (pressureOperatorOn S g) ⊆ (S : Set PeriodicFrequency) := by
  intro k hk
  by_contra h
  exact hk (pressureOperatorOn_apply_not_mem h)

/-- Finite support of a truncated pressure requires no support hypothesis on
its source. -/
theorem pressureOperatorOn_finite_support (S : Finset PeriodicFrequency)
    (g : PeriodicFrequency → ℂ) :
    (Function.support (pressureOperatorOn S g)).Finite :=
  S.finite_toSet.subset (pressureOperatorOn_support_subset S g)

end NSFormalization.Paper1.PeriodicPressureSymbol
