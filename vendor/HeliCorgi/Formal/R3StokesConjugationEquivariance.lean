import Formal.R3FourierConjugationBridge
import Formal.R3StokesH3Evolution

/-!
# Conjugation equivariance of the Stokes multipliers

First slice of the operator-realness gate: every concrete Stokes-type operator in this
repository is a Fourier multiplier with a **real, even** scalar symbol, and therefore
commutes with pointwise conjugation on the carrier.

The file provides:

* `reflect_conj_of_realEven_multiplier` — frequency side: an operator realized a.e. by a
  real, even scalar symbol commutes with reflected conjugation `r3L2Reflect ∘ r3L2Conj`;
* `r3L2Conj_of_fourier_realEven` — physical side: combining the Plancherel reality bridge
  `fourier_r3L2Conj` with the frequency-side commutation and injectivity of the transform,
  any operator with such a Fourier realization commutes with `r3L2Conj`;
* realness/evenness of the concrete symbols (`r3StokesScalarComplex`,
  `r3SobolevWeightComplex`, `r3StokesH2ToH3ScalarComplex`);
* the concrete equivariance theorems for `r3StokesL2Operator`, `r3StokesH3Evolution`, and
  `r3StokesH2ToH3Operator`.

Consequence (used by the later realness-of-solutions gate): all three operators preserve
`IsR3RealVelocity`. The Leray projector and the projected convection are NOT treated here;
they are the next slices of the gate.
-/

namespace MNS2

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate FourierTransform

noncomputable section

/-! ## Generic real-even multiplier equivariance -/

/-- Frequency side: an operator realized almost everywhere by a real, even scalar symbol
commutes with reflected conjugation. -/
theorem reflect_conj_of_realEven_multiplier
    {M : R3L2Velocity →L[ℂ] R3L2Velocity} {m₀ : R3 → ℂ}
    (hM : ∀ f : R3L2Velocity, M f =ᵐ[volume] fun ξ => m₀ ξ • f ξ)
    (hreal : ∀ ξ : R3, conj (m₀ ξ) = m₀ ξ)
    (heven : ∀ ξ : R3, m₀ (-ξ) = m₀ ξ)
    (h : R3L2Velocity) :
    r3L2Reflect (r3L2Conj (M h)) = M (r3L2Reflect (r3L2Conj h)) := by
  refine Lp.ext ?_
  have h1 := coeFn_r3L2Reflect (r3L2Conj (M h))
  have h2 : ∀ᵐ x : R3 ∂(volume : Measure R3),
      (r3L2Conj (M h)) (-x) = r3CConj ((M h) (-x)) :=
    r3MeasurePreserving_neg.quasiMeasurePreserving.ae (coeFn_r3L2Conj (M h))
  have h3 : ∀ᵐ x : R3 ∂(volume : Measure R3),
      (M h) (-x) = m₀ (-x) • h (-x) :=
    r3MeasurePreserving_neg.quasiMeasurePreserving.ae (hM h)
  have h4 := hM (r3L2Reflect (r3L2Conj h))
  have h5 := coeFn_r3L2Reflect (r3L2Conj h)
  have h6 : ∀ᵐ x : R3 ∂(volume : Measure R3),
      (r3L2Conj h) (-x) = r3CConj (h (-x)) :=
    r3MeasurePreserving_neg.quasiMeasurePreserving.ae (coeFn_r3L2Conj h)
  filter_upwards [h1, h2, h3, h4, h5, h6] with x e1 e2 e3 e4 e5 e6
  rw [e1, e2, e3, r3CConj_smul, hreal, heven, e4, e5, e6]

/-- Physical side: an operator with a real, even Fourier-multiplier realization commutes
with pointwise conjugation on the carrier. -/
theorem r3L2Conj_of_fourier_realEven
    {S M : R3L2Velocity →L[ℂ] R3L2Velocity} {m₀ : R3 → ℂ}
    (hfourier : ∀ f : R3L2Velocity, 𝓕 (S f) = M (𝓕 f))
    (hM : ∀ f : R3L2Velocity, M f =ᵐ[volume] fun ξ => m₀ ξ • f ξ)
    (hreal : ∀ ξ : R3, conj (m₀ ξ) = m₀ ξ)
    (heven : ∀ ξ : R3, m₀ (-ξ) = m₀ ξ)
    (g : R3L2Velocity) :
    r3L2Conj (S g) = S (r3L2Conj g) := by
  refine (Lp.fourierTransformₗᵢ R3 R3C).injective ?_
  calc
    𝓕 (r3L2Conj (S g)) = r3L2Reflect (r3L2Conj (𝓕 (S g))) := fourier_r3L2Conj _
    _ = r3L2Reflect (r3L2Conj (M (𝓕 g))) := by rw [hfourier]
    _ = M (r3L2Reflect (r3L2Conj (𝓕 g))) :=
        reflect_conj_of_realEven_multiplier hM hreal heven _
    _ = M (𝓕 (r3L2Conj g)) := by rw [← fourier_r3L2Conj]
    _ = 𝓕 (S (r3L2Conj g)) := (hfourier _).symm

/-! ## Realness and evenness of the concrete symbols -/

theorem r3StokesScalarComplex_conj (ν t : ℝ) (ξ : R3) :
    conj (r3StokesScalarComplex ν t ξ) = r3StokesScalarComplex ν t ξ :=
  Complex.conj_ofReal _

theorem r3StokesScalarComplex_neg (ν t : ℝ) (ξ : R3) :
    r3StokesScalarComplex ν t (-ξ) = r3StokesScalarComplex ν t ξ := by
  simp [r3StokesScalarComplex, r3StokesScalar, r3StokesDecayRate]

theorem r3SobolevWeightComplex_conj (s : ℝ) (ξ : R3) :
    conj (r3SobolevWeightComplex s ξ) = r3SobolevWeightComplex s ξ :=
  Complex.conj_ofReal _

theorem r3SobolevWeightComplex_neg (s : ℝ) (ξ : R3) :
    r3SobolevWeightComplex s (-ξ) = r3SobolevWeightComplex s ξ := by
  simp [r3SobolevWeightComplex]

theorem r3StokesH2ToH3ScalarComplex_conj (nu tau : ℝ) (ξ : R3) :
    conj (r3StokesH2ToH3ScalarComplex nu tau ξ) =
      r3StokesH2ToH3ScalarComplex nu tau ξ := by
  unfold r3StokesH2ToH3ScalarComplex
  rw [map_mul, r3SobolevWeightComplex_conj, r3StokesScalarComplex_conj]

theorem r3StokesH2ToH3ScalarComplex_neg (nu tau : ℝ) (ξ : R3) :
    r3StokesH2ToH3ScalarComplex nu tau (-ξ) =
      r3StokesH2ToH3ScalarComplex nu tau ξ := by
  unfold r3StokesH2ToH3ScalarComplex
  rw [r3SobolevWeightComplex_neg, r3StokesScalarComplex_neg]

/-! ## Conjugation equivariance of the concrete Stokes operators -/

/-- The physical `L²` Stokes evolution commutes with pointwise conjugation. -/
theorem r3L2Conj_r3StokesL2Operator {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (g : R3L2Velocity) :
    r3L2Conj (r3StokesL2Operator hν ht g) = r3StokesL2Operator hν ht (r3L2Conj g) :=
  r3L2Conj_of_fourier_realEven (fourier_r3StokesL2Operator hν ht)
    (r3StokesL2FrequencyMultiplier_ae hν ht)
    (r3StokesScalarComplex_conj ν t) (r3StokesScalarComplex_neg ν t) g

/-- The same-space order-three Stokes evolution commutes with pointwise conjugation. -/
theorem r3L2Conj_r3StokesH3Evolution {nu : ℝ} (hnu : 0 ≤ nu) (t : ℝ≥0)
    (g : R3HsVelocity 3) :
    r3L2Conj (r3StokesH3Evolution hnu t g) = r3StokesH3Evolution hnu t (r3L2Conj g) :=
  r3L2Conj_r3StokesL2Operator hnu t.property g

/-- The positive-time `H² → H³` smoothing operator commutes with pointwise conjugation. -/
theorem r3L2Conj_r3StokesH2ToH3Operator {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau)
    (g : R3HsVelocity 2) :
    r3L2Conj (r3StokesH2ToH3Operator hnu htau g) =
      r3StokesH2ToH3Operator hnu htau (r3L2Conj g) :=
  r3L2Conj_of_fourier_realEven (fourier_r3StokesH2ToH3Operator hnu htau)
    (r3StokesH2ToH3FrequencyOperator_ae hnu htau)
    (r3StokesH2ToH3ScalarComplex_conj nu tau) (r3StokesH2ToH3ScalarComplex_neg nu tau) g

/-- Stokes evolutions preserve physically real coordinates. -/
theorem IsR3RealVelocity.stokesL2 {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    {g : R3L2Velocity} (hg : IsR3RealVelocity g) :
    IsR3RealVelocity (r3StokesL2Operator hν ht g) := by
  unfold IsR3RealVelocity at *
  rw [r3L2Conj_r3StokesL2Operator, hg]

/-- The same-space order-three Stokes evolution preserves physically real coordinates. -/
theorem IsR3RealVelocity.stokesH3 {nu : ℝ} (hnu : 0 ≤ nu) (t : ℝ≥0)
    {g : R3HsVelocity 3} (hg : IsR3RealVelocity g) :
    IsR3RealVelocity (r3StokesH3Evolution hnu t g) := by
  unfold IsR3RealVelocity at *
  rw [r3L2Conj_r3StokesH3Evolution, hg]

/-- The `H² → H³` smoothing operator preserves physically real coordinates. -/
theorem IsR3RealVelocity.stokesH2ToH3 {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau)
    {g : R3HsVelocity 2} (hg : IsR3RealVelocity g) :
    IsR3RealVelocity (r3StokesH2ToH3Operator hnu htau g) := by
  unfold IsR3RealVelocity at *
  rw [r3L2Conj_r3StokesH2ToH3Operator, hg]

end

end MNS2
