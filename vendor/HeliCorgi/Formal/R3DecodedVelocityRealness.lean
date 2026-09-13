import Formal.R3StokesConjugationEquivariance
import Formal.EndpointSafeTwoSpaceUniqueness
import Formal.R3NavierStokesEquation

/-!
# Realness transport through the order-three decoder

Cheapest remaining Gate-A semantic gap (Stage-9 readiness pass, Task A): the certified
Navier–Stokes capstone `r3EndpointSafeProjectedMild_navierStokes` speaks about the decoded
physical velocity `U s = r3H3ToL2Operator (u s)`, while the realness theory
(`IsR3RealVelocity`, unconditional realness of mild solutions with real data) lives on the
coordinate carrier.  This file transports realness through the decoder:

* `r3H3InverseBesselWeightComplex_conj` / `r3H3InverseBesselWeightComplex_neg` — the
  decoder symbol `J⁻³ = (1 + ‖ξ‖²)^(-3/2)` is real and even (instances of the existing
  `r3SobolevWeightComplex` lemmas at order `-3`);
* `r3L2Conj_r3H3ToL2Operator` — the bounded order-three decoder commutes with pointwise
  conjugation (one application of the existing generic `r3L2Conj_of_fourier_realEven`);
* `isR3RealVelocity_r3H3ToL2Operator` — the decoder preserves `IsR3RealVelocity`;
* `r3EndpointSafeProjectedMild_isR3RealVelocity_decoded` — along any endpoint-safe
  projected mild solution with physically real initial coordinate, the decoded physical
  velocity is real at every certified time (consuming the unconditional coordinate-level
  realness `IsR3EndpointSafeProjectedMildSolutionOn.isR3RealVelocity`).

No new reality framework is built; no classical `C^∞` upgrade and no pointwise
representative theorem is claimed.  The decoded field is real as an element of the
physical `L²` carrier (fixed point of `r3L2Conj`, equivalently a.e. vanishing imaginary
part via `isR3RealVelocity_iff_im_ae`).
-/

namespace MNS2

open MeasureTheory Set
open scoped ComplexConjugate FourierTransform

noncomputable section

/-! ## The decoder symbol is real and even -/

theorem r3H3InverseBesselWeightComplex_conj (ξ : R3) :
    conj (r3H3InverseBesselWeightComplex ξ) = r3H3InverseBesselWeightComplex ξ :=
  r3SobolevWeightComplex_conj (-3) ξ

theorem r3H3InverseBesselWeightComplex_neg (ξ : R3) :
    r3H3InverseBesselWeightComplex (-ξ) = r3H3InverseBesselWeightComplex ξ :=
  r3SobolevWeightComplex_neg (-3) ξ

/-! ## Conjugation equivariance and realness preservation of the decoder -/

/-- The bounded order-three decoder `J⁻³` commutes with pointwise conjugation. -/
theorem r3L2Conj_r3H3ToL2Operator (g : R3HsVelocity 3) :
    r3L2Conj (r3H3ToL2Operator g) = r3H3ToL2Operator (r3L2Conj g) :=
  r3L2Conj_of_fourier_realEven fourier_r3H3ToL2Operator
    r3H3InverseBesselL2FrequencyOperator_ae
    r3H3InverseBesselWeightComplex_conj r3H3InverseBesselWeightComplex_neg g

/-- Realness transport: the decoded physical velocity of a physically real coordinate is
real. -/
theorem isR3RealVelocity_r3H3ToL2Operator {g : R3HsVelocity 3}
    (hg : IsR3RealVelocity g) : IsR3RealVelocity (r3H3ToL2Operator g) := by
  unfold IsR3RealVelocity at *
  rw [r3L2Conj_r3H3ToL2Operator, hg]

/-! ## Realness of the certified decoded velocity -/

/-- Along any endpoint-safe projected mild solution with physically real initial
coordinate, the decoded physical velocity `U t = r3H3ToL2Operator (u t)` — the field
appearing in the Navier–Stokes capstone `r3EndpointSafeProjectedMild_navierStokes` — is
physically real at every certified time.  No ball hypothesis: this consumes the
unconditional coordinate-level realness theorem. -/
theorem r3EndpointSafeProjectedMild_isR3RealVelocity_decoded {nu T : ℝ} {hnu : 0 < nu}
    {u0 : R3HsVelocity 3} {u : ℝ → R3HsVelocity 3}
    (h : IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u)
    (hu0 : IsR3RealVelocity u0) :
    ∀ t ∈ Icc (0 : ℝ) T, IsR3RealVelocity (r3H3ToL2Operator (u t)) := fun t ht =>
  isR3RealVelocity_r3H3ToL2Operator (h.isR3RealVelocity hu0 t ht)

end

end MNS2
