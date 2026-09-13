import Formal.R3ClassicalIncompressibility
import Formal.R3SchwartzConvection

/-!
# Frequency-side and classical divergence-free conditions agree on the Schwartz core

The admissible-datum interface states incompressibility on the **frequency side**: the raw
frequency divergence `ξ ↦ ξ · (𝓕 φ) ξ` vanishes identically. The physical formulation of the
Navier–Stokes problem states it **classically**: the pointwise divergence
`x ↦ ∑ᵢ ∂ᵢ φᵢ x` vanishes identically. This file proves that for a Schwartz velocity field the
two conditions are *equivalent*, in both directions.

The proof is a single pointwise identity plus injectivity of the Fourier transform on Schwartz
space. Writing `D φ` for the classical divergence packaged as a scalar Schwartz function
(`r3SchwartzDivergence`), mathlib's `SchwartzMap.fourier_lineDerivOp_eq` gives

`𝓕 (D φ) ξ = (2 * π * Complex.I) * r3RawDivergencePointwise ξ ((𝓕 φ) ξ)`

with the constant `+2πI` (mathlib's convention `𝓕 (∂_{m} f) = (2πI) • (⟪·, m⟫ • 𝓕 f)`). Since
`2πI ≠ 0`, the frequency-side vanishing is equivalent to `𝓕 (D φ) = 0`, hence — the Fourier
transform being a continuous linear equivalence on Schwartz space — to `D φ = 0`, i.e. to the
classical pointwise vanishing.

Scope note: nothing here is claimed beyond the Schwartz class. The statement is an equivalence of
two *hypotheses* on a Schwartz datum; it supplies no regularity, no `L²` identification, and no
extension of either condition to rougher data.
-/

namespace MNS2

open MeasureTheory FourierTransform LineDeriv Real SchwartzMap
open scoped FourierTransform SchwartzMap RealInnerProductSpace

noncomputable section

/-- The convection-file coordinate direction and the incompressibility-file standard basis
vector are the same element of `R3`. -/
theorem r3CoordinateDirection_eq_r3StdBasis (i : Fin 3) :
    r3CoordinateDirection i = r3StdBasis i := by
  ext j
  simp [r3CoordinateDirection, r3StdBasis]

/-- Pointwise value of the Schwartz coordinate derivative: it is the Fréchet derivative of the
underlying function evaluated on the `i`-th standard basis vector. -/
theorem r3SchwartzCoordinateDerivative_apply (i : Fin 3) (φ : R3SchwartzVelocity) (x : R3) :
    r3SchwartzCoordinateDerivative i φ x = fderiv ℝ (⇑φ) x (r3StdBasis i) := by
  rw [r3SchwartzCoordinateDerivative, LineDeriv.lineDerivOpCLM_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, r3CoordinateDirection_eq_r3StdBasis]

/-- The classical divergence of a Schwartz velocity field, packaged as a scalar Schwartz
function. -/
def r3SchwartzDivergence (φ : R3SchwartzVelocity) : R3SchwartzScalar :=
  ∑ i : Fin 3, r3SchwartzCoordinate i (r3SchwartzCoordinateDerivative i φ)

/-- The packaged Schwartz divergence computes the classical pointwise divergence. -/
theorem r3SchwartzDivergence_apply (φ : R3SchwartzVelocity) (x : R3) :
    r3SchwartzDivergence φ x = r3ClassicalDivergence (⇑φ) x := by
  rw [r3SchwartzDivergence, sum_apply, r3ClassicalDivergence]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [r3SchwartzCoordinate_apply, r3SchwartzCoordinateDerivative_apply]

/-- The Fourier transform acts componentwise: extracting the `i`-th component commutes with it. -/
theorem r3SchwartzCoordinate_fourier (i : Fin 3) (ψ : R3SchwartzVelocity) (ξ : R3) :
    (𝓕 (r3SchwartzCoordinate i ψ) : R3SchwartzScalar) ξ =
      ((𝓕 ψ : R3SchwartzVelocity) ξ) i := by
  have hint : Integrable (fun x : R3 => 𝐞 (-⟪x, ξ⟫) • ψ x) volume :=
    (Real.fourierIntegral_convergent_iff ξ).mpr ψ.integrable
  have hL := ContinuousLinearMap.integral_comp_comm (r3CoordinateFiberAux i) hint
  calc (𝓕 (r3SchwartzCoordinate i ψ) : R3SchwartzScalar) ξ
      = 𝓕 (fun x : R3 => (r3CoordinateFiberAux i) (ψ x)) ξ :=
        congrFun (SchwartzMap.fourier_coe (r3SchwartzCoordinate i ψ)) ξ
    _ = ∫ x : R3, (r3CoordinateFiberAux i) (𝐞 (-⟪x, ξ⟫) • ψ x) := by
        rw [Real.fourier_eq]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp)
    _ = (r3CoordinateFiberAux i) (∫ x : R3, 𝐞 (-⟪x, ξ⟫) • ψ x) := hL
    _ = ((𝓕 ψ : R3SchwartzVelocity) ξ) i := by
        rw [← Real.fourier_eq, ← congrFun (SchwartzMap.fourier_coe ψ) ξ]
        rfl

/-- Frequency-side form of one coordinate derivative of a Schwartz velocity field: mathlib's
convention gives the constant `+2πI`. -/
theorem r3SchwartzCoordinateDerivative_fourier (i : Fin 3) (φ : R3SchwartzVelocity) (ξ : R3) :
    ((𝓕 (r3SchwartzCoordinateDerivative i φ) : R3SchwartzVelocity) ξ) =
      (2 * (π : ℂ) * Complex.I) • (((ξ i : ℝ)) • ((𝓕 φ : R3SchwartzVelocity) ξ)) := by
  rw [r3SchwartzCoordinateDerivative, LineDeriv.lineDerivOpCLM_apply,
    r3CoordinateDirection_eq_r3StdBasis, SchwartzMap.fourier_lineDerivOp_eq, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_inner_r3StdBasis i),
    inner_r3StdBasis]

/-- **The pointwise transfer identity.** The Fourier transform of the classical divergence is a
fixed nonzero multiple of the raw frequency divergence of the Fourier transform. -/
theorem r3SchwartzDivergence_fourier_apply (φ : R3SchwartzVelocity) (ξ : R3) :
    (𝓕 (r3SchwartzDivergence φ) : R3SchwartzScalar) ξ =
      (2 * (π : ℂ) * Complex.I) *
        r3RawDivergencePointwise ξ ((𝓕 φ : R3SchwartzVelocity) ξ) := by
  have hterm : ∀ i : Fin 3,
      (𝓕 (r3SchwartzCoordinate i (r3SchwartzCoordinateDerivative i φ)) : R3SchwartzScalar) ξ =
        (2 * (π : ℂ) * Complex.I) * ((ξ i : ℝ) : ℂ) * ((𝓕 φ : R3SchwartzVelocity) ξ) i := by
    intro i
    rw [r3SchwartzCoordinate_fourier, r3SchwartzCoordinateDerivative_fourier]
    simp [Complex.real_smul, mul_assoc]
  rw [r3SchwartzDivergence, fourier_sum, sum_apply, r3RawDivergencePointwise,
    Fin.sum_univ_three, hterm 0, hterm 1, hterm 2]
  ring

/-- The multiplicative constant of the transfer identity is nonzero. -/
theorem r3SchwartzDivergence_fourier_const_ne_zero :
    (2 * (π : ℂ) * Complex.I) ≠ 0 := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero two_ne_zero hπ) Complex.I_ne_zero

/-- The classical divergence-free condition is exactly the vanishing of the packaged Schwartz
divergence. -/
theorem r3SchwartzDivergence_eq_zero_iff (φ : R3SchwartzVelocity) :
    r3SchwartzDivergence φ = 0 ↔ ∀ x : R3, r3ClassicalDivergence (⇑φ) x = 0 := by
  constructor
  · intro h x
    rw [← r3SchwartzDivergence_apply, h]
    rfl
  · intro h
    refine SchwartzMap.ext fun x => ?_
    rw [r3SchwartzDivergence_apply, h x]
    rfl

/-- **Equivalence of the frequency-side and classical divergence-free conditions on the Schwartz
core** (both directions).

For a Schwartz velocity field `φ`, the raw frequency divergence of `𝓕 φ` vanishes identically if
and only if the classical pointwise divergence of `φ` vanishes identically. -/
theorem r3Schwartz_rawDivergence_fourier_iff_classical (φ : R3SchwartzVelocity) :
    (∀ ξ : R3, r3RawDivergencePointwise ξ ((𝓕 φ : R3SchwartzVelocity) ξ) = 0) ↔
      ∀ x : R3, r3ClassicalDivergence (⇑φ) x = 0 := by
  rw [← r3SchwartzDivergence_eq_zero_iff]
  constructor
  · intro h
    have hF : (𝓕 (r3SchwartzDivergence φ) : R3SchwartzScalar) = 0 := by
      refine SchwartzMap.ext fun ξ => ?_
      rw [r3SchwartzDivergence_fourier_apply, h ξ, mul_zero]
      rfl
    have hinv : 𝓕⁻ (𝓕 (r3SchwartzDivergence φ) : R3SchwartzScalar) = r3SchwartzDivergence φ :=
      fourierInv_fourier_eq _
    rw [hF, fourierInv_zero] at hinv
    exact hinv.symm
  · intro h ξ
    have hz : (𝓕 (0 : R3SchwartzScalar) : R3SchwartzScalar) ξ = 0 := by simp
    have hF := r3SchwartzDivergence_fourier_apply φ ξ
    rw [h, hz] at hF
    exact (mul_eq_zero.mp hF.symm).resolve_left r3SchwartzDivergence_fourier_const_ne_zero

end

end MNS2
