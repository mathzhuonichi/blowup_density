import NSFormalization.Section4.A02.Maximal

/-! Transitive-axiom audit and spec conformance for A02 unit U7.
Run with `cd verification && lake env lean ../research/A02/axioms_u7.lean`.
Every `#print axioms` line must print exactly
`propext, Classical.choice, Quot.sound`. -/

open Set MeasureTheory
open NSFormalization.Section4.A02
open NavierStokes.ProblemStatement
open scoped ENNReal

-- U7 axiom audit
#print axioms uField_eq
#print axioms pField_eq
#print axioms exists_maximal_of_localSolution
#print axioms maximal_unique

/-! ## Conformance: each claimed field has the spec's type, verbatim

Copied from `research/A02/Spec.lean` (`MaximalSolutionAPI.exists_maximal`,
`:421-423`; `MaximalSolutionAPI.maximal_unique`, `:429-434`), with the local
restatements of the D01 objects (`Section4/A02/SolutionClass.lean`) and of
`IsMaximalSolution`/`presingularTimes` (`Section4/A02/Maximal.lean`, restated from
`Spec.lean:210-214,168-169`) substituted for the `Contracts.V1.Data`/Draft ones. -/

/-- `Spec.lean:421-423` `MaximalSolutionAPI.exists_maximal`, given
`Spec.lean:317-321` ⟪A01:LocalTheoryAPI.solution⟫ as an explicit hypothesis, in
the same shape `MaximalPartial.lean`'s `horizon_le_lifespan` uses for the A01
clause.  `exists_maximal` is the only U7 field that consumes A01: the positivity
conjunct of `IsMaximalSolution` holds precisely because A01 supplies a local
solution on a positive horizon. -/
example (horizon : ℝ → SpatialField → SpaceTimeField → ℝ)
    (localSolution : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ClassicalSolutionR ν a f (horizon ν a f)) :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ∃ (u : SpaceTimeField) (p : SpaceTimeScalar), IsMaximalSolution ν a f u p :=
  exists_maximal_of_localSolution horizon localSolution

/-- `Spec.lean:429-434` `MaximalSolutionAPI.maximal_unique`, verbatim.

This field's *type* carries no A01 clause, and its proof needs none: the two
`IsMaximalSolution` hypotheses already deliver classical solutions on `[0,S)` for
every `S < T^ν_{max,R}`, so uniqueness (U2) and the basepoint pressure gauge (U3)
close it directly.  It is therefore discharged by `maximal_unique` with no
`localSolution` argument — a stronger conformance than the A01-hypothesis shape
`exists_maximal` needs. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ (u₁ u₂ : SpaceTimeField) (p₁ p₂ : SpaceTimeScalar),
        IsMaximalSolution ν a f u₁ p₁ → IsMaximalSolution ν a f u₂ p₂ →
          (∀ t ∈ presingularTimes ν a f, ∀ x : Space, u₁ (t, x) = u₂ (t, x)) ∧
          PressureGaugeEquivOn (presingularTimes ν a f) p₁ p₂ :=
  maximal_unique
