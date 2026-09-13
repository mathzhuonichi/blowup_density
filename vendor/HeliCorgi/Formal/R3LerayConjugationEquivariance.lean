import Formal.R3StokesConjugationEquivariance
import Formal.R3LerayPointwiseProjectionIdentification
import Formal.R3H2LerayBridge

/-!
# Conjugation equivariance of the Leray projector

Second slice of the operator-realness gate. The Leray fiber symbol
`P(ξ) = I - (ξ ⊗ ξ)/|ξ|²` is a real matrix and is even in `ξ`, so the physical `L²` Leray
projector commutes with pointwise conjugation.

The file provides:

* fiber-level facts: the embedded frequency vector is real and odd, the complex Leray fiber
  symbol commutes with fiber conjugation and is even in the frequency;
* `reflect_conj_of_conjEquivariant_even_matrix` / `r3L2Conj_of_fourier_conjEquivariant_even`
  — the matrix-multiplier generalizations of the scalar equivariance theorems of
  `Formal/R3StokesConjugationEquivariance.lean`;
* `r3L2Conj_r3LerayL2Operator` and the `IsR3RealVelocity` preservation corollary.

The order-two/order-three Leray variants and the projected convection are the next slices.
-/

namespace MNS2

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate FourierTransform

noncomputable section

/-! ## Fiber-level facts -/

/-- The embedded frequency vector is componentwise real. -/
theorem r3CConj_r3FrequencyVectorComplex (ξ : R3) :
    r3CConj (r3FrequencyVectorComplex ξ) = r3FrequencyVectorComplex ξ := by
  ext i
  simp [r3FrequencyVectorComplex]

/-- The embedded frequency vector is odd in the frequency. -/
theorem r3FrequencyVectorComplex_neg (ξ : R3) :
    r3FrequencyVectorComplex (-ξ) = -r3FrequencyVectorComplex ξ := by
  ext i
  simp [r3FrequencyVectorComplex]

/-- Conjugating the second slot of the inner product against the real frequency vector. -/
theorem inner_r3FrequencyVectorComplex_r3CConj (ξ : R3) (v : R3C) :
    inner ℂ (r3FrequencyVectorComplex ξ) (r3CConj v) =
      conj (inner ℂ (r3FrequencyVectorComplex ξ) v) := by
  simp [PiLp.inner_apply, RCLike.inner_apply, r3FrequencyVectorComplex, map_sum, map_mul]

/-- The complex Leray fiber symbol commutes with fiber conjugation. -/
theorem r3CConj_r3LeraySymbolComplex (ξ : R3) (v : R3C) :
    r3CConj (r3LeraySymbolComplex ξ v) = r3LeraySymbolComplex ξ (r3CConj v) := by
  rw [r3LeraySymbolComplex_apply, r3LeraySymbolComplex_apply, map_sub, r3CConj_smul,
    map_div₀, Complex.conj_ofReal, r3CConj_r3FrequencyVectorComplex,
    inner_r3FrequencyVectorComplex_r3CConj]

/-- The complex Leray fiber symbol is even in the frequency. -/
theorem r3LeraySymbolComplex_neg (ξ : R3) :
    r3LeraySymbolComplex (-ξ) = r3LeraySymbolComplex ξ := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [r3LeraySymbolComplex_apply, r3LeraySymbolComplex_apply, r3FrequencyVectorComplex_neg]
  simp [inner_neg_left, neg_div, neg_smul, smul_neg]

/-! ## Generic conjugation-equivariant matrix multipliers -/

/-- Frequency side: an operator realized a.e. by a conjugation-equivariant, even
matrix-valued symbol commutes with reflected conjugation. -/
theorem reflect_conj_of_conjEquivariant_even_matrix
    {M : R3L2Velocity →L[ℂ] R3L2Velocity} {A : R3 → R3C →L[ℂ] R3C}
    (hM : ∀ f : R3L2Velocity, M f =ᵐ[volume] fun ξ => A ξ (f ξ))
    (hconj : ∀ (ξ : R3) (v : R3C), r3CConj (A ξ v) = A ξ (r3CConj v))
    (heven : ∀ ξ : R3, A (-ξ) = A ξ)
    (h : R3L2Velocity) :
    r3L2Reflect (r3L2Conj (M h)) = M (r3L2Reflect (r3L2Conj h)) := by
  refine Lp.ext ?_
  have h1 := coeFn_r3L2Reflect (r3L2Conj (M h))
  have h2 : ∀ᵐ x : R3 ∂(volume : Measure R3),
      (r3L2Conj (M h)) (-x) = r3CConj ((M h) (-x)) :=
    r3MeasurePreserving_neg.quasiMeasurePreserving.ae (coeFn_r3L2Conj (M h))
  have h3 : ∀ᵐ x : R3 ∂(volume : Measure R3),
      (M h) (-x) = A (-x) (h (-x)) :=
    r3MeasurePreserving_neg.quasiMeasurePreserving.ae (hM h)
  have h4 := hM (r3L2Reflect (r3L2Conj h))
  have h5 := coeFn_r3L2Reflect (r3L2Conj h)
  have h6 : ∀ᵐ x : R3 ∂(volume : Measure R3),
      (r3L2Conj h) (-x) = r3CConj (h (-x)) :=
    r3MeasurePreserving_neg.quasiMeasurePreserving.ae (coeFn_r3L2Conj h)
  filter_upwards [h1, h2, h3, h4, h5, h6] with x e1 e2 e3 e4 e5 e6
  rw [e1, e2, e3, hconj, heven, e4, e5, e6]

/-- Physical side: an operator whose Fourier realization is a conjugation-equivariant, even
matrix multiplier commutes with pointwise conjugation on the carrier. -/
theorem r3L2Conj_of_fourier_conjEquivariant_even
    {S M : R3L2Velocity →L[ℂ] R3L2Velocity} {A : R3 → R3C →L[ℂ] R3C}
    (hfourier : ∀ f : R3L2Velocity, 𝓕 (S f) = M (𝓕 f))
    (hM : ∀ f : R3L2Velocity, M f =ᵐ[volume] fun ξ => A ξ (f ξ))
    (hconj : ∀ (ξ : R3) (v : R3C), r3CConj (A ξ v) = A ξ (r3CConj v))
    (heven : ∀ ξ : R3, A (-ξ) = A ξ)
    (g : R3L2Velocity) :
    r3L2Conj (S g) = S (r3L2Conj g) := by
  refine (Lp.fourierTransformₗᵢ R3 R3C).injective ?_
  calc
    𝓕 (r3L2Conj (S g)) = r3L2Reflect (r3L2Conj (𝓕 (S g))) := fourier_r3L2Conj _
    _ = r3L2Reflect (r3L2Conj (M (𝓕 g))) := by rw [hfourier]
    _ = M (r3L2Reflect (r3L2Conj (𝓕 g))) :=
        reflect_conj_of_conjEquivariant_even_matrix hM hconj heven _
    _ = M (𝓕 (r3L2Conj g)) := by rw [← fourier_r3L2Conj]
    _ = 𝓕 (S (r3L2Conj g)) := (hfourier _).symm

/-! ## Conjugation equivariance of the Leray projector -/

/-- The physical `L²` Leray projector commutes with pointwise conjugation. -/
theorem r3L2Conj_r3LerayL2Operator (g : R3L2Velocity) :
    r3L2Conj (r3LerayL2Operator g) = r3LerayL2Operator (r3L2Conj g) :=
  r3L2Conj_of_fourier_conjEquivariant_even fourier_r3LerayL2Operator
    r3LerayL2FrequencyOperator_ae r3CConj_r3LeraySymbolComplex r3LeraySymbolComplex_neg g

/-- The Leray projector preserves physically real coordinates. -/
theorem IsR3RealVelocity.leray {g : R3L2Velocity} (hg : IsR3RealVelocity g) :
    IsR3RealVelocity (r3LerayL2Operator g) := by
  unfold IsR3RealVelocity at *
  rw [r3L2Conj_r3LerayL2Operator, hg]

/-- The order-two Leray projector commutes with pointwise conjugation. -/
theorem r3L2Conj_r3LerayH2Operator (g : R3HsVelocity 2) :
    r3L2Conj (r3LerayH2Operator g) = r3LerayH2Operator (r3L2Conj g) :=
  r3L2Conj_r3LerayL2Operator g

/-- The order-three Leray projector commutes with pointwise conjugation. -/
theorem r3L2Conj_r3LerayH3Operator (g : R3HsVelocity 3) :
    r3L2Conj (r3LerayH3Operator g) = r3LerayH3Operator (r3L2Conj g) :=
  r3L2Conj_r3LerayL2Operator g

/-- The order-two Leray projector preserves physically real coordinates. -/
theorem IsR3RealVelocity.lerayH2 {g : R3HsVelocity 2} (hg : IsR3RealVelocity g) :
    IsR3RealVelocity (r3LerayH2Operator g) :=
  hg.leray

/-- The order-three Leray projector preserves physically real coordinates. -/
theorem IsR3RealVelocity.lerayH3 {g : R3HsVelocity 3} (hg : IsR3RealVelocity g) :
    IsR3RealVelocity (r3LerayH3Operator g) :=
  hg.leray

end

end MNS2
