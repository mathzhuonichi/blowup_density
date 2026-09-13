import Mathlib
import Formal.QuadraticMildTangentAdapter
import Formal.QuadraticMildTangentRealization

namespace MNS2

open Set
open scoped Interval ContDiff

noncomputable section

section QuadraticMildCoherentFamilyAdapter

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
A time-coherent `C¹` quadratic mild flow-map family whose derivative-side analytic
obligations are stated explicitly rather than compressed into the semantic assumption
`tangentRealizes`.

The underlying `flow` is the existing time-slice adapter.  The additional fields say:

* the selected states across `s ∈ [0,t]` form one actual base mild trajectory;
* the directional Fréchet derivative trajectory is continuous in time and starts from
  the input direction;
* at every prefix time, a local fixed-point/dominated-differentiation certificate is
  available for the same selected state family.

These are strong analytic obligations, but they are lower-level than directly assuming
that every `fderiv` endpoint already satisfies `QuadraticMildTangentEvolvesAt`.
-/
structure QuadraticMildC1CoherentFamilyAdapter
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V) where
  flow : NavierStokesTimeBridgeAdapter V V
    (fun t x y => (MildEvolutionKernel.ofQuadratic H Q).EvolvesAt t x y)
  baseTrajectory :
    ∀ t ∈ flow.certifiedTimes, ∀ x ∈ flow.admissible t,
      (MildEvolutionKernel.ofQuadratic H Q).IsMildSolutionOn t x
        (fun s : ℝ => flow.stateMap s x)
  tangentContinuous :
    ∀ t ∈ flow.certifiedTimes, ∀ x ∈ flow.admissible t, ∀ h : V,
      ContinuousOn
        (fun s : ℝ => (fderiv ℝ (flow.stateMap s) x) h)
        (Icc (0 : ℝ) t)
  tangentInitial :
    ∀ t ∈ flow.certifiedTimes, ∀ x ∈ flow.admissible t, ∀ h : V,
      (fderiv ℝ (flow.stateMap 0) x) h = h
  derivativeCertificates :
    ∀ t ∈ flow.certifiedTimes, ∀ x ∈ flow.admissible t,
      ∀ s ∈ Icc (0 : ℝ) t,
        QuadraticMildFixedPointDerivativeCertificateAt H Q s
          (fun y : V => fun τ : ℝ => flow.stateMap τ y)
          x
          (fun τ : ℝ => fderiv ℝ (flow.stateMap τ) x)

/--
The coherent-family obligations imply the derivative-side semantic field required by
`QuadraticMildC1TangentAdapter`.

This is the first constructor in the repository that obtains `tangentRealizes` from a
base mild trajectory plus explicit differentiability/fixed-point certificates rather
than taking `tangentRealizes` itself as an input assumption.
-/
def QuadraticMildC1CoherentFamilyAdapter.toTangentAdapter
    (A : QuadraticMildC1CoherentFamilyAdapter (V := V) H Q) :
    QuadraticMildC1TangentAdapter (V := V) H Q where
  flow := A.flow
  tangentRealizes := by
    intro t ht x hx h
    exact quadraticMildTangentEvolvesAt_of_local_fixedPoint_family
      H Q t
      (fun y : V => fun s : ℝ => A.flow.stateMap s y)
      x
      (fun s : ℝ => fderiv ℝ (A.flow.stateMap s) x)
      h
      (A.baseTrajectory t ht x hx)
      (A.tangentContinuous t ht x hx h)
      (A.tangentInitial t ht x hx h)
      (A.derivativeCertificates t ht x hx)

/--
Consequently, the actual Fréchet derivative endpoint of a coherent family is realized
by the quadratic linearized mild semantics at every certified datum and direction.
-/
theorem QuadraticMildC1CoherentFamilyAdapter.fderiv_realizes_linearized_mild
    (A : QuadraticMildC1CoherentFamilyAdapter (V := V) H Q)
    {t : ℝ} (ht : t ∈ A.flow.certifiedTimes)
    {x : V} (hx : x ∈ A.flow.admissible t)
    (h : V) :
    QuadraticMildTangentEvolvesAt H Q t x h
      ((fderiv ℝ (A.flow.stateMap t) x) h) := by
  exact A.toTangentAdapter.fderiv_realizes_linearized_mild ht hx h

/--
The exact radial flow-map bridge and its pointwise linearized-mild semantics are therefore
available without a separately supplied `tangentRealizes` field.
-/
theorem QuadraticMildC1CoherentFamilyAdapter.radial_bridge_with_derived_tangent_semantics
    (A : QuadraticMildC1CoherentFamilyAdapter (V := V) H Q)
    (t : ℝ) (ht : t ∈ A.flow.certifiedTimes) (d : V)
    (hpath : MapsTo (fun s : ℝ => s • d) (uIcc (0 : ℝ) 1) (A.flow.admissible t)) :
    ((∫ s in (0 : ℝ)..1, (fderiv ℝ (A.flow.stateMap t) (s • d)) d) =
        A.flow.stateMap t d - A.flow.stateMap t 0) ∧
      (∀ s ∈ uIcc (0 : ℝ) 1,
        QuadraticMildTangentEvolvesAt H Q t (s • d) d
          ((fderiv ℝ (A.flow.stateMap t) (s • d)) d)) := by
  exact A.toTangentAdapter.radial_bridge_with_linearized_mild_semantics t ht d hpath

end QuadraticMildCoherentFamilyAdapter

end

end MNS2
