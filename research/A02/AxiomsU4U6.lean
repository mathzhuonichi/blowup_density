import NSFormalization.Section4.A02.Order

/-!
Axiom audit for A02 units U4 and U6.  Draft check file, not part of any library:
run it with `cd verification && lake env lean ../research/A02/AxiomsU4U6.lean`.
Every line below must print exactly `propext, Classical.choice, Quot.sound`.
-/

open NSFormalization.Section4.A02

-- U4
#print axioms ClassicalSolutionR.restrict
#print axioms ClassicalSolutionR.nonempty_restrict
#print axioms exists_restrict
#print axioms slice_eq_of_eqOn
#print axioms scalarSlice_eq_of_eqOn
#print axioms spatialDerivative_eq_of_eqOn
#print axioms pressureGradient_eq_of_eqOn
#print axioms temporalDerivative_eq_of_eqOn
#print axioms navierStokesResidual_eq_of_eqOn
#print axioms ClassicalSolutionR.congr
#print axioms exists_eq_fields_of_eqOn
#print axioms exists_eq_fields_of_agree
#print axioms pressureGradient_sub_basepoint
#print axioms contDiffOn_basepoint
#print axioms ClassicalSolutionR.normalizePressure
#print axioms exists_pressure_normalization
#print axioms normalizePressure_gauge_invariant

-- U6
#print axioms horizon_le_lifespan
#print axioms horizon_le_lifespan_of_localSolution
#print axioms lifespan_le_iff
#print axioms lifespan_le_iff_no_extension
#print axioms lifespan_ge_of_forall_shorter
#print axioms exists_horizon_gt_of_lt_lifespan
#print axioms regularThrough_iff
#print axioms referenceLifespan

/-! ## Conformance: each claimed field has the spec's type, verbatim

The statements are copied from `research/A02/Spec.lean` with the local
restatements of the D01 objects substituted for the `Contracts.V1.Data` ones. -/

open NavierStokes.ProblemStatement

/-- `Spec.lean:345-348` `MaximalSolutionAPI.restrict`. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T), ∀ S : ℝ, 0 < S → S ≤ T →
      ∃ w : ClassicalSolutionR ν a f S,
        w.velocity = u.velocity ∧ w.pressure = u.pressure :=
  exists_restrict

/-- `Spec.lean:399-403` `MaximalSolutionAPI.pressure_normalization`. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (T : ℝ) (w : ClassicalSolutionR ν a f T) (x₀ : Space),
      ∃ w' : ClassicalSolutionR ν a f T,
        w'.velocity = w.velocity ∧
        ∀ z : SpaceTime, w'.pressure z = w.pressure z - w.pressure (z.1, x₀) :=
  exists_pressure_normalization

/-- `Spec.lean:372-375` `MaximalSolutionAPI.horizon_le_lifespan`, given
`Spec.lean:318-321` ⟪A01:LocalTheoryAPI.solution⟫. -/
example (horizon : ℝ → SpatialField → SpaceTimeField → ℝ)
    (localSolution : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ClassicalSolutionR ν a f (horizon ν a f)) :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ENNReal.ofReal (horizon ν a f) ≤ maximalLifespanR ν a f :=
  horizon_le_lifespan_of_localSolution localSolution

/-- `Spec.lean:443-446` `MaximalSolutionAPI.lifespan_le_iff`. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ), 0 ≤ T →
    (maximalLifespanR ν a f ≤ ENNReal.ofReal T ↔
      ∀ S : ℝ, Nonempty (ClassicalSolutionR ν a f S) → S ≤ T) :=
  lifespan_le_iff

/-- `Spec.lean:451-455` `MaximalSolutionAPI.lifespan_le_iff_no_extension`. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ), 0 ≤ T →
    (maximalLifespanR ν a f ≤ ENNReal.ofReal T ↔
      ∀ S : ℝ, T < S → IsEmpty (ClassicalSolutionR ν a f S)) :=
  lifespan_le_iff_no_extension

/-- `Spec.lean:463-466` `MaximalSolutionAPI.lifespan_ge_of_forall_shorter`. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ), 0 < T →
    (∀ b : ℝ, 0 < b → b < T → Nonempty (ClassicalSolutionR ν a f b)) →
      ENNReal.ofReal T ≤ maximalLifespanR ν a f :=
  lifespan_ge_of_forall_shorter

/-- `Spec.lean:476-478` `MaximalSolutionAPI.regularThrough_iff`. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ), 0 < T →
    (RegularThrough ν a f T ↔ ENNReal.ofReal T < maximalLifespanR ν a f) :=
  regularThrough_iff

/-- `Spec.lean:500-504` `MaximalSolutionAPI.referenceLifespan`. -/
example : ∀ (ν : ℝ) (a : SpatialField) (g : SpaceTimeField) (T : ℝ), 0 < T →
    RegularThrough ν a g T →
    ∃ δ : ℝ, 0 < δ ∧ Nonempty (ClassicalSolutionR ν a g (T + δ)) ∧
      (∃ S : ℝ, T + δ < S ∧ Nonempty (ClassicalSolutionR ν a g S)) ∧
      ENNReal.ofReal (T + δ) < maximalLifespanR ν a g :=
  referenceLifespan

/-- `Spec.lean:210-214` `IsMaximalSolution`'s literal-field clause, restated on
the local class: the shape unit U7 needs from the congruence lemma. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
    (w : ClassicalSolutionR ν a f S) (u : SpaceTimeField) (p : SpaceTimeScalar),
    (∀ t ∈ Set.Ico (0 : ℝ) S, ∀ x : Space, u (t, x) = w.velocity (t, x)) →
    (∀ t ∈ Set.Ico (0 : ℝ) S, ∀ x : Space, p (t, x) = w.pressure (t, x)) →
      ∃ w' : ClassicalSolutionR ν a f S, w'.velocity = u ∧ w'.pressure = p :=
  fun _ _ _ _ w u p hu hp => exists_eq_fields_of_agree w u p hu hp
