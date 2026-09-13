import Mathlib
import Formal.R3LerayFrequencySymbol

namespace MNS2

noncomputable section

/--
The nonnegative spatial decay rate for the heat/Stokes semigroup at frequency `ξ`,
using mathlib's Fourier-transform convention for the Laplacian:
`Δ̂ = -(2π)^2 |ξ|^2`.
-/
def r3StokesDecayRate (ν : ℝ) (ξ : R3) : ℝ :=
  (2 * Real.pi) ^ 2 * ν * ‖ξ‖ ^ 2

/-- Scalar heat/Stokes multiplier at one physical three-dimensional frequency. -/
def r3StokesScalar (ν t : ℝ) (ξ : R3) : ℝ :=
  Real.exp (-(r3StokesDecayRate ν ξ * t))

/--
The frequency-fiber Stokes/heat operator.  Since the heat multiplier is scalar, it
acts by the same scalar on each velocity component.

This is not yet a function-space semigroup on `R^3`; it is the exact pointwise
Fourier symbol that a later lift must realize.
-/
def r3StokesFrequencySymbol (ν t : ℝ) (ξ : R3) : R3 →L[ℝ] R3 :=
  (r3StokesScalar ν t ξ) • ContinuousLinearMap.id ℝ R3

/-- The decay rate is nonnegative for nonnegative viscosity. -/
theorem r3StokesDecayRate_nonneg
    {ν : ℝ} (hν : 0 ≤ ν) (ξ : R3) :
    0 ≤ r3StokesDecayRate ν ξ := by
  unfold r3StokesDecayRate
  positivity

/-- The scalar heat multiplier is strictly positive at every time and frequency. -/
theorem r3StokesScalar_pos
    (ν t : ℝ) (ξ : R3) :
    0 < r3StokesScalar ν t ξ := by
  exact Real.exp_pos _

/-- For nonnegative viscosity and forward time, the scalar heat multiplier is at most one. -/
theorem r3StokesScalar_le_one
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (ξ : R3) :
    r3StokesScalar ν t ξ ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr <| mul_nonneg (r3StokesDecayRate_nonneg hν ξ) ht

@[simp]
theorem r3StokesFrequencySymbol_apply
    (ν t : ℝ) (ξ v : R3) :
    r3StokesFrequencySymbol ν t ξ v = r3StokesScalar ν t ξ • v := by
  simp [r3StokesFrequencySymbol]

/-- The Stokes symbol is the identity at time zero. -/
@[simp]
theorem r3StokesFrequencySymbol_zero_time
    (ν : ℝ) (ξ : R3) :
    r3StokesFrequencySymbol ν 0 ξ = ContinuousLinearMap.id ℝ R3 := by
  ext v
  simp [r3StokesScalar]

/-- The zero frequency is unchanged by heat evolution. -/
@[simp]
theorem r3StokesFrequencySymbol_zero_frequency
    (ν t : ℝ) :
    r3StokesFrequencySymbol ν t (0 : R3) = ContinuousLinearMap.id ℝ R3 := by
  ext v
  simp [r3StokesScalar, r3StokesDecayRate]

/-- Scalar semigroup identity at a fixed frequency. -/
theorem r3StokesScalar_add_time
    (ν t s : ℝ) (ξ : R3) :
    r3StokesScalar ν (t + s) ξ =
      r3StokesScalar ν t ξ * r3StokesScalar ν s ξ := by
  unfold r3StokesScalar
  rw [← Real.exp_add]
  congr 1
  ring

/-- Exact pointwise semigroup law for the frequency-fiber Stokes operator. -/
theorem r3StokesFrequencySymbol_add_time
    (ν t s : ℝ) (ξ v : R3) :
    r3StokesFrequencySymbol ν (t + s) ξ v =
      r3StokesFrequencySymbol ν t ξ
        (r3StokesFrequencySymbol ν s ξ v) := by
  simp only [r3StokesFrequencySymbol_apply]
  rw [r3StokesScalar_add_time]
  simp [smul_smul]

/-- Scalar heat evolution preserves the transverse-frequency subspace. -/
theorem r3StokesFrequencySymbol_mem
    (ν t : ℝ) (ξ v : R3)
    (hv : v ∈ r3SolenoidalFiber ξ) :
    r3StokesFrequencySymbol ν t ξ v ∈ r3SolenoidalFiber ξ := by
  rw [r3StokesFrequencySymbol_apply]
  exact (r3SolenoidalFiber ξ).smul_mem (r3StokesScalar ν t ξ) hv

/--
At each frequency, the scalar Stokes symbol commutes exactly with the Leray symbol.
Thus heat evolution neither creates nor mixes the longitudinal component.
-/
theorem r3StokesFrequencySymbol_commutes_leray
    (ν t : ℝ) (ξ v : R3) :
    r3StokesFrequencySymbol ν t ξ (r3LeraySymbol ξ v) =
      r3LeraySymbol ξ (r3StokesFrequencySymbol ν t ξ v) := by
  simp only [r3StokesFrequencySymbol_apply]
  rw [map_smul]

/-- Forward Stokes evolution is norm non-increasing on each frequency fiber. -/
theorem norm_r3StokesFrequencySymbol_le
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (ξ v : R3) :
    ‖r3StokesFrequencySymbol ν t ξ v‖ ≤ ‖v‖ := by
  rw [r3StokesFrequencySymbol_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (r3StokesScalar_pos ν t ξ)]
  calc
    r3StokesScalar ν t ξ * ‖v‖ ≤ 1 * ‖v‖ :=
      mul_le_mul_of_nonneg_right (r3StokesScalar_le_one hν ht ξ) (norm_nonneg v)
    _ = ‖v‖ := one_mul _

/--
The combined fiber-level Stokes--Leray symbol.  Commutation shows that the order is
immaterial pointwise; this definition chooses Stokes followed by Leray.
-/
def r3StokesLerayFrequencySymbol (ν t : ℝ) (ξ : R3) : R3 →L[ℝ] R3 :=
  r3LeraySymbol ξ ∘L r3StokesFrequencySymbol ν t ξ

@[simp]
theorem r3StokesLerayFrequencySymbol_apply
    (ν t : ℝ) (ξ v : R3) :
    r3StokesLerayFrequencySymbol ν t ξ v =
      r3StokesScalar ν t ξ • r3LeraySymbol ξ v := by
  rw [r3StokesLerayFrequencySymbol, ContinuousLinearMap.comp_apply,
    r3StokesFrequencySymbol_apply, map_smul]

/-- Every output of the combined Stokes--Leray symbol is transverse. -/
theorem r3StokesLerayFrequencySymbol_mem
    (ν t : ℝ) (ξ v : R3) :
    r3StokesLerayFrequencySymbol ν t ξ v ∈ r3SolenoidalFiber ξ := by
  rw [r3StokesLerayFrequencySymbol_apply]
  exact (r3SolenoidalFiber ξ).smul_mem _ (r3LeraySymbol_mem ξ v)

end

end MNS2
