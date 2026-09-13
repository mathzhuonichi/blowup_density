import NSFormalization.Paper1.PeriodicLerayDivergence

/-!
# The periodic Leray projection as a linear map on Fourier coefficients

The coefficient carrier is frequency-first. The projection is the identity
minus the composition of divergence, the normalized inverse Laplacian, and
gradient. Its range is exactly the divergence-free coefficient fields.
These are algebraic statements on raw coefficients; no Sobolev boundedness or
physical-space reconstruction is asserted.
-/

noncomputable section
namespace NSFormalization.Paper1.PeriodicLerayLinear

open NSFormalization.Paper1.PeriodicPressureSymbol
open NSFormalization.Paper1.PeriodicLerayCoeffCore
open NSFormalization.Paper1.PeriodicLerayDivergence
open scoped BigOperators

/-- Fourier divergence assembled from linear coordinate evaluations. -/
def divergenceLinear : VectorCoeff →ₗ[ℂ] (PeriodicFrequency → ℂ) :=
  LinearMap.pi (fun k => ∑ j : Fin 3,
    (((LinearMap.proj j : (Fin 3 → ℂ) →ₗ[ℂ] ℂ).comp
      (LinearMap.proj k : VectorCoeff →ₗ[ℂ] (Fin 3 → ℂ)))).smulRight
      (PeriodicLerayCoeffCore.derivativeSymbol j k))

@[simp] theorem divergenceLinear_apply (f : VectorCoeff) (k : PeriodicFrequency) :
    divergenceLinear f k = divergenceCoeff f k := by
  simp [divergenceLinear, divergenceCoeff, mul_comm]

theorem divergenceLinear_eq (f : VectorCoeff) :
    divergenceLinear f = divergenceCoeff f := by
  funext k
  exact divergenceLinear_apply f k

/-- Fourier gradient assembled from scalar coordinate evaluations. -/
def gradientLinear : (PeriodicFrequency → ℂ) →ₗ[ℂ] VectorCoeff :=
  LinearMap.pi (fun k => LinearMap.pi (fun j =>
    (LinearMap.proj k).smulRight (PeriodicLerayCoeffCore.derivativeSymbol j k)))

@[simp] theorem gradientLinear_apply (p : PeriodicFrequency → ℂ)
    (k : PeriodicFrequency) (j : Fin 3) :
    gradientLinear p k j = PeriodicLerayCoeffCore.derivativeSymbol j k * p k := by
  simp [gradientLinear, mul_comm]

/-- The Leray projection on raw periodic Fourier coefficient fields. -/
def lerayLinear : VectorCoeff →ₗ[ℂ] VectorCoeff :=
  LinearMap.id - gradientLinear.comp (pressureOperator.comp divergenceLinear)

@[simp] theorem lerayLinear_apply (f : VectorCoeff)
    (k : PeriodicFrequency) (j : Fin 3) :
    lerayLinear f k j = projectedCoeff f j k := by
  simp [lerayLinear, projectedCoeff, divergenceLinear_eq]

/-- Every projected coefficient field is divergence-free at every frequency. -/
@[simp] theorem divergenceCoeff_lerayLinear (f : VectorCoeff) (k : PeriodicFrequency) :
    divergenceCoeff (lerayLinear f) k = 0 := by
  simpa only [divergenceCoeff, lerayLinear_apply] using divergence_projectedCoeff f k

/-- A divergence-free coefficient field is fixed by the projection. -/
theorem lerayLinear_eq_self (f : VectorCoeff)
    (hdiv : ∀ k, divergenceCoeff f k = 0) : lerayLinear f = f := by
  funext k j
  rw [lerayLinear_apply]
  exact projectedCoeff_eq_of_divergence_zero f hdiv j k

/-- The coefficient projection is idempotent. -/
@[simp] theorem lerayLinear_idempotent (f : VectorCoeff) :
    lerayLinear (lerayLinear f) = lerayLinear f :=
  lerayLinear_eq_self _ (divergenceCoeff_lerayLinear f)

/-- Idempotence also holds as an equality of linear maps. -/
theorem lerayLinear_comp_self : lerayLinear.comp lerayLinear = lerayLinear := by
  ext f k j
  exact congrFun (congrFun (lerayLinear_idempotent f) k) j

/-- The fixed coefficient fields are exactly the divergence-free fields. -/
theorem lerayLinear_eq_self_iff (f : VectorCoeff) :
    lerayLinear f = f ↔ ∀ k, divergenceCoeff f k = 0 := by
  constructor
  · intro h k
    rw [← h]
    exact divergenceCoeff_lerayLinear f k
  · exact lerayLinear_eq_self f

/-- The projection preserves the spatially constant velocity mode. -/
@[simp] theorem lerayLinear_zero_mode (f : VectorCoeff) (j : Fin 3) :
    lerayLinear f 0 j = f 0 j := by
  rw [lerayLinear_apply, projectedCoeff_zero]

end NSFormalization.Paper1.PeriodicLerayLinear
