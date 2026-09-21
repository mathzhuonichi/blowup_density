import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.Holder
import Formal.R3StokesFrequencySymbol

namespace MNS2

open MeasureTheory FourierTransform Filter
open scoped ENNReal FourierTransform

noncomputable section

/-- Complexified three-component velocity fiber used by the `L²(R³)` Fourier theory. -/
abbrev R3C := EuclideanSpace ℂ (Fin 3)

/--
The first concrete bundled function-space carrier for the physical `R³` formal PDE layer.

It is the complexified velocity space `L²(R³; ℂ³)`. Complexification is used because mathlib's
Plancherel/Fourier `L²` equivalence is formulated over complex-valued target spaces. No claim is
made here that this is already the final local-wellposedness carrier for Navier--Stokes.
-/
abbrev R3L2Velocity := Lp (α := R3) R3C 2 (volume : Measure R3)

/-- Complex form of the real scalar Stokes multiplier from `R3StokesFrequencySymbol`. -/
def r3StokesScalarComplex (ν t : ℝ) (ξ : R3) : ℂ :=
  Complex.ofReal (r3StokesScalar ν t ξ)

/-- The complex scalar Stokes multiplier is continuous in the physical frequency. -/
theorem continuous_r3StokesScalarComplex (ν t : ℝ) :
    Continuous (r3StokesScalarComplex ν t) := by
  unfold r3StokesScalarComplex r3StokesScalar r3StokesDecayRate
  fun_prop

/-- For nonnegative viscosity and forward time, the complex Stokes multiplier has norm at most one. -/
theorem norm_r3StokesScalarComplex_le_one
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (ξ : R3) :
    ‖r3StokesScalarComplex ν t ξ‖ ≤ 1 := by
  rw [r3StokesScalarComplex, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (r3StokesScalar_pos ν t ξ)]
  exact r3StokesScalar_le_one hν ht ξ

/--
The scalar Stokes multiplier bundled as an `L∞` function on frequency space.

The proof data `hν`, `ht` certify the uniform forward-time bound by one; they do not alter the
underlying multiplier function.
-/
def r3StokesScalarLpTop
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    Lp ℂ ⊤ (volume : Measure R3) :=
  (memLp_top_of_bound
      (continuous_r3StokesScalarComplex ν t).aestronglyMeasurable
      1
      (ae_of_all _ fun ξ => norm_r3StokesScalarComplex_le_one hν ht ξ)).toLp
    (r3StokesScalarComplex ν t)

/-- The bundled `L∞` multiplier agrees almost everywhere with its pointwise formula. -/
theorem r3StokesScalarLpTop_ae
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    r3StokesScalarLpTop hν ht =ᵐ[volume]
      r3StokesScalarComplex ν t := by
  unfold r3StokesScalarLpTop
  exact MemLp.coeFn_toLp _

/--
Multiplication by a fixed complex `L∞` scalar field as a continuous linear map on
`L²(R³; ℂ³)`.

This is intentionally bundled directly from mathlib's heterogeneous `Lp` scalar multiplication,
rather than through `ContinuousLinearMap.holderL`. The latter exposes its result exponent as a
`semiOutParam`, which is fragile for the concrete `∞ · 2 → 2` specialization. Mathlib's direct
`Lp` scalar-multiplication API exists precisely to avoid those unnecessary typeclass constraints.
-/
def r3L2ScalarMultiplier
    (m : Lp ℂ ⊤ (volume : Measure R3)) :
    R3L2Velocity →L[ℂ] R3L2Velocity := by
  letI : ENNReal.HolderTriple (⊤ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) := ⟨by simp⟩
  let L : R3L2Velocity →ₗ[ℂ] R3L2Velocity :=
    { toFun := fun f => (m • f : R3L2Velocity)
      map_add' := by
        intro f g
        exact Lp.add_smul m f g
      map_smul' := by
        intro c f
        exact (Lp.smul_comm c m f).symm }
  exact L.mkContinuous ‖m‖ (fun f => Lp.norm_smul_le m f)

/-- The direct scalar-multiplier CLM has the expected underlying `Lp` action. -/
@[simp]
theorem r3L2ScalarMultiplier_apply
    (m : Lp ℂ ⊤ (volume : Measure R3)) (f : R3L2Velocity) :
    r3L2ScalarMultiplier m f = (m • f : R3L2Velocity) := by
  rfl

/--
The Stokes multiplier acting on the bundled Fourier-side space `L²(R³; ℂ³)`.

This is the first step beyond frequency-fiber algebra: the pointwise scalar symbol is now a genuine
bounded continuous linear operator on a complete function space.
-/
def r3StokesL2FrequencyMultiplier
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    R3L2Velocity →L[ℂ] R3L2Velocity :=
  r3L2ScalarMultiplier (r3StokesScalarLpTop hν ht)

/-- Exact almost-everywhere pointwise realization of the bundled Fourier-side Stokes multiplier. -/
theorem r3StokesL2FrequencyMultiplier_ae
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (f : R3L2Velocity) :
    r3StokesL2FrequencyMultiplier hν ht f =ᵐ[volume]
      fun ξ => r3StokesScalarComplex ν t ξ • f ξ := by
  letI : ENNReal.HolderTriple (⊤ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) := ⟨by simp⟩
  change
    ((r3StokesScalarLpTop hν ht • f : R3L2Velocity) : R3 → R3C) =ᵐ[volume]
      fun ξ => r3StokesScalarComplex ν t ξ • f ξ
  filter_upwards
    [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (r3StokesScalarLpTop hν ht) f,
      r3StokesScalarLpTop_ae hν ht]
    with ξ hmul hscalar
  rw [hmul, Pi.smul_apply', hscalar]

/--
The physical-space `L²(R³; ℂ³)` Stokes operator, defined by Fourier conjugation of the bounded
frequency multiplier.

Unlike `r3StokesFrequencySymbol`, this is a genuine function-space continuous linear map.
It still does not include the matrix-valued Leray multiplier or the nonlinear convection term.
-/
def r3StokesL2Operator
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    R3L2Velocity →L[ℂ] R3L2Velocity :=
  fourierInvCLM ℂ R3L2Velocity ∘L
    r3StokesL2FrequencyMultiplier hν ht ∘L
      fourierCLM ℂ R3L2Velocity

/-- The function-space Stokes operator has exactly the intended Fourier multiplier realization. -/
theorem fourier_r3StokesL2Operator
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (f : R3L2Velocity) :
    𝓕 (r3StokesL2Operator hν ht f) =
      r3StokesL2FrequencyMultiplier hν ht (𝓕 f) := by
  simp [r3StokesL2Operator]

/-- At time zero the bundled Fourier-side Stokes multiplier is the identity. -/
theorem r3StokesL2FrequencyMultiplier_zero_time
    {ν : ℝ} (hν : 0 ≤ ν) :
    r3StokesL2FrequencyMultiplier hν (le_refl 0) =
      ContinuousLinearMap.id ℂ R3L2Velocity := by
  ext f
  filter_upwards [r3StokesL2FrequencyMultiplier_ae hν (le_refl 0) f] with ξ hξ
  simpa [r3StokesScalarComplex, r3StokesScalar] using hξ

/-- At time zero the physical-space `L²` Stokes operator is the identity. -/
theorem r3StokesL2Operator_zero_time
    {ν : ℝ} (hν : 0 ≤ ν) :
    r3StokesL2Operator hν (le_refl 0) =
      ContinuousLinearMap.id ℂ R3L2Velocity := by
  ext f
  simp [r3StokesL2Operator, r3StokesL2FrequencyMultiplier_zero_time hν]

end

end MNS2