import NSFormalization.Section4.A02.Patch

/-! Transitive-axiom audit and spec conformance for A02 units U5 and U9.
Run with `cd verification && lake env lean ../research/A02/axioms_u5u9.lean`.
Every `#print axioms` line must print exactly `propext, Classical.choice, Quot.sound`. -/

open Set MeasureTheory Filter
open NSFormalization.Section4.A02
open NavierStokes.ProblemStatement
open scoped ENNReal

-- U5 / U9 axiom audit
#print axioms PressureGaugeEquivOn.refl
#print axioms PressureGaugeEquivOn.symm
#print axioms PressureGaugeEquivOn.mono
#print axioms patch
#print axioms speedENorm_le_ofReal
#print axioms lifespan_le_of_unbounded

/-! ## Conformance: each claimed field has the spec's type, verbatim

Copied from `research/A02/Spec.lean` (`MaximalSolutionAPI.patch`, `:357-367`;
`MaximalSolutionAPI.lifespan_le_of_unbounded`, `:576-582`), with the local
restatements of the D01 objects (`Section4/A02/SolutionClass.lean`) and of
`limsupLeft`/`speedENorm` (`Section4/A02/Patch.lean`, restated from
`Spec.lean:135-136,148-149`) substituted for the `Contracts.V1.Data`/Draft ones. -/

/-- `Spec.lean:357-367` `MaximalSolutionAPI.patch`. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionR ν a f T₁)
        (u₂ : ClassicalSolutionR ν a f T₂),
        ∃ w : ClassicalSolutionR ν a f (max T₁ T₂),
          (∀ t ∈ Ico (0 : ℝ) T₁, ∀ x : Space,
              w.velocity (t, x) = u₁.velocity (t, x)) ∧
          (∀ t ∈ Ico (0 : ℝ) T₂, ∀ x : Space,
              w.velocity (t, x) = u₂.velocity (t, x)) ∧
          PressureGaugeEquivOn (Ico (0 : ℝ) T₁) u₁.pressure w.pressure ∧
          PressureGaugeEquivOn (Ico (0 : ℝ) T₂) u₂.pressure w.pressure :=
  patch

/-- `Spec.lean:576-582` `MaximalSolutionAPI.lifespan_le_of_unbounded`, with the
local `limsupLeft`/`speedENorm` substituted. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (T : ℝ), 0 < ν → a ∈ initialClassR → MemForceR f → 0 < T →
    ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
      (∀ S : ℝ, 0 < S → S < T →
          ∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p) →
      limsupLeft T (fun t => speedENorm (fun x : Space => u (t, x))) = ⊤ →
        maximalLifespanR ν a f ≤ ENNReal.ofReal T :=
  lifespan_le_of_unbounded
