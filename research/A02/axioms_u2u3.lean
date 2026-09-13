import NSFormalization.Section4.A02.Uniqueness

/-! Transitive-axiom audit and spec conformance for A02 units U2 and U3.
Run with `cd verification && lake env lean ../research/A02/axioms_u2u3.lean`.
Every `#print axioms` line must print exactly `propext, Classical.choice, Quot.sound`. -/

open Set
open NSFormalization.Section4.A02
open NavierStokes.ProblemStatement

-- U2 / U3 axiom audit
#print axioms velocity_unique_core
#print axioms velocity_unique
#print axioms pressure_gauge_core
#print axioms pressure_gauge

/-! ## Conformance: each claimed field has the spec's type, verbatim

Copied from `research/A02/Spec.lean:267-281` (`UniquenessAPI`), with the local
restatements of the D01 objects (`Section4/A02/SolutionClass.lean`) substituted
for the `Contracts.V1.Data` ones. -/

/-- `Spec.lean:267-272` `UniquenessAPI.velocity_unique`. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionR ν a f T₁)
        (u₂ : ClassicalSolutionR ν a f T₂),
        ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
          u₁.velocity (t, x) = u₂.velocity (t, x) :=
  velocity_unique

/-- `Spec.lean:277-281` `UniquenessAPI.pressure_gauge`. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionR ν a f T₁)
        (u₂ : ClassicalSolutionR ν a f T₂),
        PressureGaugeEquivOn (Ico (0 : ℝ) (min T₁ T₂)) u₁.pressure u₂.pressure :=
  pressure_gauge
