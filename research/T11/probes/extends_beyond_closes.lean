import NSFormalization.Section3.T11.ExtendsBeyond

/-! Exact target-shape and non-vacuity probe for T11/U14 + U16
(`extendsBeyond`, `lifespanInfiniteOfLocallyFinite`).

The first two `example`s are the last two fields of `PeriodicContinuationAPI`
copied verbatim from `research/T11/probes/api_on_canonical.lean:136-158`,
discharged by the module theorems under exactly two conditions: the single
named input `PeriodicQuantitativeLocalInput'` (consumed through lane 332's
`restartBeyond`) and the `higherOrderBound` field of the same structure, itself
copied verbatim as the binder `hHigh`.  The third `example` chains lane 322's
`higherOrderBound_of_energyInequality` into that binder, which checks that
`hHigh` is token-identical to U12's conclusion. -/

noncomputable section

namespace NSFormalization.Section3.T11.ExtendsBeyondProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal

/-- **Target 1.** The `PeriodicContinuationAPI.extendsBeyond` field copied
verbatim from `api_on_canonical.lean:136-143`, with the `higherOrderBound`
field copied verbatim as the binder `hHigh`. -/
example (H : PeriodicQuantitativeLocalInput')
    (hHigh : ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∀ (S : ℝ), 0 < S →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
                ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                  ∀ t ∈ Ico (0 : ℝ) S,
                    periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M) :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ExtendsBeyondT ν a f S u p := by
  exact extendsBeyond_of_input H hHigh

/-- **Target 2.** The `PeriodicContinuationAPI.lifespanInfiniteOfLocallyFinite`
field copied verbatim from `api_on_canonical.lean:144-158`.  The `≤` in the
criterion hypothesis is the manuscript's and is kept. -/
example (H : PeriodicQuantitativeLocalInput')
    (hHigh : ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∀ (S : ℝ), 0 < S →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
                ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                  ∀ t ∈ Ico (0 : ℝ) S,
                    periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M) :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u p →
            (∀ S : ℝ, 0 < S →
              ENNReal.ofReal S ≤ maximalLifespanT ν a f →
                squaredHTwoIntegralT S u ≠ ⊤) →
              maximalLifespanT ν a f = ⊤ := by
  exact lifespanInfiniteOfLocallyFinite_of_input H hHigh

/-- **The `hHigh` binder is exactly U12's conclusion.**  Lane 322's
`higherOrderBound_of_energyInequality` plugs straight into it, so under the
manuscript energy inequality `eq:Rhigh` both targets rest on the single named
input `PeriodicQuantitativeLocalInput'` alone. -/
example (H : PeriodicQuantitativeLocalInput') (Chigh : ℕ → ℝ)
    (hRhigh : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T) (m : ℕ), 3 ≤ m →
          ∀ t ∈ Ioo (0 : ℝ) T, ∃ d g : ℝ, 0 ≤ g ∧
            HasDerivAt (fun r ↦ torusSobolevNormAt (m : ℝ) w.velocity r ^ 2) d t ∧
            (1 / 2) * d + ν * g ^ 2 ≤
              Chigh m * torusSobolevNormAt 2 w.velocity t *
                  torusSobolevNormAt (m : ℝ) w.velocity t * g +
                torusSobolevNormAt (m : ℝ) f t * torusSobolevNormAt (m : ℝ) w.velocity t) :
    (∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∀ (S : ℝ), 0 < S →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
                ExtendsBeyondT ν a f S u p) ∧
    (∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            IsMaximalPeriodicSolution ν a f u p →
              (∀ S : ℝ, 0 < S →
                ENNReal.ofReal S ≤ maximalLifespanT ν a f →
                  squaredHTwoIntegralT S u ≠ ⊤) →
                maximalLifespanT ν a f = ⊤) :=
  ⟨extendsBeyond_of_input H (higherOrderBound_of_energyInequality Chigh hRhigh),
    lifespanInfiniteOfLocallyFinite_of_input H
      (higherOrderBound_of_energyInequality Chigh hRhigh)⟩

/-- **Export for T18–T21.** A concrete extension past `S` pushes the maximal
lifespan strictly past `ofReal S`. -/
example {ν S : ℝ} {a : SpatialField} {f : SpaceTimeField}
    {u : SpaceTimeField} {p : SpaceTimeScalar}
    (h : ExtendsBeyondT ν a f S u p) :
    ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal (S + δ) ≤ maximalLifespanT ν a f :=
  lifespan_ge_of_extends h

/-- **Export.** The `PeriodicLocalTheoryAPI.exists_maximal` field, verbatim,
with lane 323's residual `PeriodicMaximalExistenceInput` discharged from the
single named input. -/
example (H : PeriodicQuantitativeLocalInput') :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∃ (u : SpaceTimeField) (p : SpaceTimeScalar),
            IsMaximalPeriodicSolution ν a f u p :=
  exists_maximal_of_input H

/-- **Why the `≤` of Target 2 is load-bearing** (`RECONCILIATION.md` §2).  For a
maximal solution the *strict* form of the criterion hypothesis carries no
information at all: at every `S` with `ofReal S < maximalLifespanT ν a f` the
squared `H²` lintegral is already finite, unconditionally.  So a `<` variant of
`lifespanInfiniteOfLocallyFinite` would assert that every maximal lifespan is
`⊤` with a vacuous hypothesis.  The whole content sits at `S = L.toReal`, which
is where the module applies it. -/
example {ν : ℝ} {a : SpatialField} {f : SpaceTimeField}
    {u : SpaceTimeField} {p : SpaceTimeScalar}
    (hmax : IsMaximalPeriodicSolution ν a f u p)
    (S : ℝ) (hS : 0 < S) (hSL : ENNReal.ofReal S < maximalLifespanT ν a f) :
    squaredHTwoIntegralT S u ≠ ⊤ := by
  rw [maximalLifespanT, lt_iSup_iff] at hSL
  obtain ⟨b, hb⟩ := hSL
  rw [lt_iSup_iff] at hb
  obtain ⟨hne, hSb⟩ := hb
  have hSb' : S < b := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hS.le).mp hSb
  have hb'pos : 0 < (S + b) / 2 := by linarith
  have hSb'' : S < (S + b) / 2 := by linarith
  have hb'life : ENNReal.ofReal ((S + b) / 2) < maximalLifespanT ν a f :=
    lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
      (le_iSup_of_le b (le_iSup_of_le hne le_rfl))
  obtain ⟨w, hwv, -⟩ := hmax.2 ((S + b) / 2) hb'pos hb'life
  rw [← hwv]
  exact squaredHTwoIntegralT_ne_top_of_lt w hSb''

/-- **Non-vacuity of every hypothesis of both targets**, unconditionally on the
named input, at a genuinely nonzero velocity: a constant divergence-free datum
with the compactly time-supported zero force. -/
example :
    ∃ (a : SpatialField) (f : SpaceTimeField) (u : SpaceTimeField)
      (p : SpaceTimeScalar),
      a ∈ initialClassT ∧ f ∈ forceClassT ∧ u (0, 0) ≠ 0 ∧
        SolvesBelowT 1 a f 1 u p ∧ squaredHTwoIntegralT 1 u ≠ ⊤ ∧
        IsMaximalPeriodicSolution 1 a f u p ∧
        (∀ S : ℝ, 0 < S → ENNReal.ofReal S ≤ maximalLifespanT 1 a f →
          squaredHTwoIntegralT S u ≠ ⊤) := by
  let c : Space := coordinateVector 0
  have hc : c ≠ 0 := by
    intro h
    have h0 := congrArg (fun v : Space ↦ v (0 : Fin 3)) h
    simp [c, coordinateVector] at h0
  have ha : (fun _ ↦ c) ∈ initialClassT := by
    refine ⟨contDiff_const, fun _ _ ↦ rfl, ?_⟩
    intro x
    simp [spatialDivergence, spatialDerivative]
  have hf : (0 : SpaceTimeField) ∈ forceClassT := by
    refine ⟨contDiff_const, fun _ _ _ _ ↦ rfl, ∅, isCompact_empty, empty_subset _, ?_⟩
    simp
  refine ⟨fun _ ↦ c, 0, fun _ ↦ c, 0, ha, hf, hc,
    fun b hb0 _ ↦ ⟨constantVelocitySolutionT c hb0, rfl, rfl⟩,
    squaredHTwoIntegralT_constant_ne_top c 1,
    ⟨lt_of_lt_of_le (ENNReal.ofReal_pos.mpr one_pos)
      (lifespan_ge_of_horizon (constantVelocitySolutionT c one_pos)),
      fun S hS _ ↦ ⟨constantVelocitySolutionT c hS, rfl, rfl⟩⟩,
    fun S _ _ ↦ squaredHTwoIntegralT_constant_ne_top c S⟩

/-- **Non-vacuity of the conclusions.**  At that witness both targets fire: the
extension is a genuine classical solution past `S = 1` agreeing with the
nonzero velocity on `[0, 1)`, and the maximal lifespan is `⊤`. -/
example (H : PeriodicQuantitativeLocalInput')
    (hHigh : ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∀ (S : ℝ), 0 < S →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
                ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                  ∀ t ∈ Ico (0 : ℝ) S,
                    periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M) :
    ∃ (a : SpatialField) (f : SpaceTimeField) (u : SpaceTimeField)
      (p : SpaceTimeScalar),
      u (0, 0) ≠ 0 ∧
        (∃ δ : ℝ, 0 < δ ∧ ∃ v : ClassicalSolutionT 1 a f (1 + δ),
          (∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, v.velocity (t, x) = u (t, x)) ∧
            ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, v.pressure (t, x) = p (t, x)) ∧
        maximalLifespanT 1 a f = ⊤ := by
  let c : Space := coordinateVector 0
  have hc : c ≠ 0 := by
    intro h
    have h0 := congrArg (fun v : Space ↦ v (0 : Fin 3)) h
    simp [c, coordinateVector] at h0
  have ha : (fun _ ↦ c) ∈ initialClassT := by
    refine ⟨contDiff_const, fun _ _ ↦ rfl, ?_⟩
    intro x
    simp [spatialDivergence, spatialDerivative]
  have hf : (0 : SpaceTimeField) ∈ forceClassT := by
    refine ⟨contDiff_const, fun _ _ _ _ ↦ rfl, ∅, isCompact_empty, empty_subset _, ?_⟩
    simp
  have hsolve : SolvesBelowT 1 (fun _ ↦ c) 0 1 (fun _ ↦ c) 0 :=
    fun b hb0 _ ↦ ⟨constantVelocitySolutionT c hb0, rfl, rfl⟩
  have hmax : IsMaximalPeriodicSolution 1 (fun _ ↦ c) 0 (fun _ ↦ c) 0 :=
    ⟨lt_of_lt_of_le (ENNReal.ofReal_pos.mpr one_pos)
      (lifespan_ge_of_horizon (constantVelocitySolutionT c one_pos)),
      fun S hS _ ↦ ⟨constantVelocitySolutionT c hS, rfl, rfl⟩⟩
  obtain ⟨δ, hδ, v, hvu, hvp⟩ := extendsBeyond_of_input H hHigh 1 one_pos
    (fun _ ↦ c) ha 0 hf 1 one_pos (fun _ ↦ c) 0 hsolve
    (squaredHTwoIntegralT_constant_ne_top c 1)
  exact ⟨fun _ ↦ c, 0, fun _ ↦ c, 0, hc, ⟨δ, hδ, v, hvu, hvp⟩,
    lifespanInfiniteOfLocallyFinite_of_input H hHigh 1 one_pos (fun _ ↦ c) ha 0 hf
      (fun _ ↦ c) 0 hmax (fun S _ _ ↦ squaredHTwoIntegralT_constant_ne_top c S)⟩

end NSFormalization.Section3.T11.ExtendsBeyondProbe
