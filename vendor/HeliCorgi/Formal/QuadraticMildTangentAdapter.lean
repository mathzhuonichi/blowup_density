import Mathlib
import Formal.NavierStokesTimeBridge
import Formal.QuadraticLinearizedMild

namespace MNS2

open Set
open scoped Interval ContDiff

noncomputable section

section QuadraticMildTangentAdapter

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
A certified `C¹` time-indexed flow map for an abstract quadratic mild kernel together
with an explicit semantic obligation for its Fréchet derivative.

The base flow-map relation is the existential mild endpoint relation of
`MildEvolutionKernel.ofQuadratic H Q`. The additional `tangentRealizes` field states
that the actual `fderiv` action chosen by the `C¹` state map is realized by a base+tangent
pair satisfying the quadratic linearized mild equation.

This is a packaging/interface structure. It does NOT prove differentiability of a PDE
solution map or derive the tangent equation from the nonlinear mild equation.
-/
structure QuadraticMildC1TangentAdapter
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V) where
  flow : NavierStokesTimeBridgeAdapter V V
    (fun t x y => (MildEvolutionKernel.ofQuadratic H Q).EvolvesAt t x y)
  tangentRealizes :
    ∀ t ∈ flow.certifiedTimes, ∀ x ∈ flow.admissible t, ∀ h : V,
      QuadraticMildTangentEvolvesAt H Q t x h
        ((fderiv ℝ (flow.stateMap t) x) h)

/-- The selected base endpoint has an actual mild-solution witness. -/
theorem QuadraticMildC1TangentAdapter.base_realizes_mild
    (A : QuadraticMildC1TangentAdapter (V := V) H Q)
    {t : ℝ} (ht : t ∈ A.flow.certifiedTimes)
    {x : V} (hx : x ∈ A.flow.admissible t) :
    (MildEvolutionKernel.ofQuadratic H Q).EvolvesAt t x (A.flow.stateMap t x) := by
  exact A.flow.realizesNS t ht x hx

/--
At every certified datum and direction, the actual Fréchet derivative endpoint of the
state map is realized by the quadratic linearized mild tangent semantics.
-/
theorem QuadraticMildC1TangentAdapter.fderiv_realizes_linearized_mild
    (A : QuadraticMildC1TangentAdapter (V := V) H Q)
    {t : ℝ} (ht : t ∈ A.flow.certifiedTimes)
    {x : V} (hx : x ∈ A.flow.admissible t)
    (h : V) :
    QuadraticMildTangentEvolvesAt H Q t x h
      ((fderiv ℝ (A.flow.stateMap t) x) h) := by
  exact A.tangentRealizes t ht x hx h

/--
Every tangent integrand on a certified radial initial-data path has the intended
linearized mild endpoint meaning. The tangent direction remains the fixed,
unnormalized datum `d`.
-/
theorem QuadraticMildC1TangentAdapter.radial_path_fderiv_realizes_linearized_mild
    (A : QuadraticMildC1TangentAdapter (V := V) H Q)
    (t : ℝ) (ht : t ∈ A.flow.certifiedTimes) (d : V)
    (hpath : MapsTo (fun s : ℝ => s • d) (uIcc (0 : ℝ) 1) (A.flow.admissible t))
    {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) 1) :
    QuadraticMildTangentEvolvesAt H Q t (s • d) d
      ((fderiv ℝ (A.flow.stateMap t) (s • d)) d) := by
  exact A.tangentRealizes t ht (s • d) (hpath hs) d

/--
The exact radial flow-map bridge together with pointwise linearized-mild semantics for
its entire integrand family.

The first component is the already-proved local `C¹` path-integral identity. The second
component is semantic realization of each Fréchet tangent endpoint; it is not inferred
from the first component.
-/
theorem QuadraticMildC1TangentAdapter.radial_bridge_with_linearized_mild_semantics
    (A : QuadraticMildC1TangentAdapter (V := V) H Q)
    (t : ℝ) (ht : t ∈ A.flow.certifiedTimes) (d : V)
    (hpath : MapsTo (fun s : ℝ => s • d) (uIcc (0 : ℝ) 1) (A.flow.admissible t)) :
    ((∫ s in (0 : ℝ)..1, (fderiv ℝ (A.flow.stateMap t) (s • d)) d) =
        A.flow.stateMap t d - A.flow.stateMap t 0) ∧
      (∀ s ∈ uIcc (0 : ℝ) 1,
        QuadraticMildTangentEvolvesAt H Q t (s • d) d
          ((fderiv ℝ (A.flow.stateMap t) (s • d)) d)) := by
  constructor
  · exact A.flow.radial_bridge_at_time t ht d hpath
  · intro s hs
    exact A.radial_path_fderiv_realizes_linearized_mild t ht d hpath hs

/--
Zero-fixed endpoint form of the radial bridge, still retaining explicit pointwise
linearized-mild semantics of the integrand.
-/
theorem QuadraticMildC1TangentAdapter.radial_endpoint_bridge_with_linearized_mild_semantics
    (A : QuadraticMildC1TangentAdapter (V := V) H Q)
    (t : ℝ) (ht : t ∈ A.flow.certifiedTimes) (d : V)
    (hpath : MapsTo (fun s : ℝ => s • d) (uIcc (0 : ℝ) 1) (A.flow.admissible t))
    (hzero : A.flow.stateMap t 0 = 0) :
    ((∫ s in (0 : ℝ)..1, (fderiv ℝ (A.flow.stateMap t) (s • d)) d) =
        A.flow.stateMap t d) ∧
      (∀ s ∈ uIcc (0 : ℝ) 1,
        QuadraticMildTangentEvolvesAt H Q t (s • d) d
          ((fderiv ℝ (A.flow.stateMap t) (s • d)) d)) := by
  constructor
  · exact A.flow.radial_bridge_at_time_of_zero_fixed t ht d hpath hzero
  · intro s hs
    exact A.radial_path_fderiv_realizes_linearized_mild t ht d hpath hs

end QuadraticMildTangentAdapter

end

end MNS2
