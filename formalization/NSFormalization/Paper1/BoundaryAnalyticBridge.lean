import NSFormalization.Paper1.BoundaryCorollaryCorrected
import NSFormalization.Paper1.BoundaryReferenceRestriction

/-!
# Boundary bookkeeping and witness binding

This file does not construct a bounded-domain solution.  It records two
bridges which are often hidden by the existential `BoundedFlow` predicate:
support separated from the boundary gives no-slip for a reference field, and
an existential bounded flow can be unpacked into explicit velocity/pressure
witnesses.  The latter is the only sound way to bind a separately named
pressure family to the pressure occurring in `BoundedFlow`.
-/
noncomputable section
namespace NSFormalization.Paper1.BoundaryCorollary

open Set
open NavierStokes NavierStokes.ProblemStatement
open scoped ContDiff Topology

/-- A package exposing the fields hidden by `BoundedFlow`. -/
structure BoundedFlowData (Ω : Set Space) (ν : ℝ)
    (a : Space → Space) (g : VelocityField) (T : ℝ) where
  velocity : VelocityField
  pressure : PressureField
  positive_time : 0 < T
  velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) T ×ˢ closure Ω)
  pressure_smooth : ContDiffOn ℝ ∞ pressure (Ico (0 : ℝ) T ×ˢ closure Ω)
  divergence_free : ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ Ω,
    spatialDivergence velocity t x = 0
  equation : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Ω,
    Source.residual ν velocity pressure t x = g (t, x)
  initial : ∀ x ∈ Ω, velocity (0, x) = a x
  no_slip : ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ frontier Ω, velocity (t, x) = 0

/-- Repackage explicit witnesses as the existential `BoundedFlow` predicate. -/
theorem boundedFlow_of_data
    {Ω : Set Space} {ν : ℝ} {a : Space → Space}
    {g : VelocityField} {T : ℝ}
    (w : BoundedFlowData Ω ν a g T) : BoundedFlow Ω ν a g T := by
  exact ⟨w.velocity, w.pressure, w.positive_time, w.velocity_smooth,
    w.pressure_smooth, w.divergence_free, w.equation, w.initial, w.no_slip⟩

/-- A positive-parameter family with explicit PDE witnesses.  The equality
`pressure_binding` is deliberate: it states that the named family `P` is the
pressure used by the corresponding `BoundedFlow` witness, rather than the
tautology `P ε = P ε` in the old contract. -/
structure ExplicitInsertionFlowBinding
    {Ω : Set Space} {ν T : ℝ} {a : Space → Space}
    {g : VelocityField} (P : ℝ → PressureField)
    (G : ℝ → VelocityField) : Type where
  data : ∀ ε, 0 < ε → BoundedFlowData Ω ν a (G ε) T
  pressure_binding : ∀ ε (hε : 0 < ε), (data ε hε).pressure = P ε

/-- The support statement needed for no-slip is independent of the PDE
equation.  The reference no-slip condition and support separation suffice. -/
theorem reference_supported_noSlip_on_horizon
    {Ω : Set Space} {ν T δ : ℝ} {a : Space → Space}
    {v : VelocityField} {π : PressureField} {g : VelocityField}
    (href : BoundedReference Ω ν T δ a v π g)
    {B : Set Space} (hBinterior : B ⊆ interior Ω)
    {U : ℝ → VelocityField} {ε : ℝ}
    (hslice : ∀ t : ℝ, tsupport (fun x : Space =>
      U ε (t, x) - v (t, x)) ⊆ B) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ frontier Ω, U ε (t, x) = 0 := by
  intro t ht
  apply noSlip_of_reference_and_supported_difference href
    (U := U) (ε := ε)
    (B := B) (t := t)
  · intro x hx
    exact disjoint_frontier_of_subset_interior hBinterior x hx
  · exact hslice
  · exact ht

end NSFormalization.Paper1.BoundaryCorollary
