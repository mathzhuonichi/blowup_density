import NSFormalization.Section3.T11.ExistenceInputH3

/-! Exact target-shape and non-vacuity probe for T11/U9e
(`research/T11/LEAD_AMENDMENTS.md` amendment 2).

Target 1 is `PeriodicQuantitativeLocalInput'` (`Section3/T11/LocalExistence.lean:24`)
written out in full with `periodicSobolevENorm 3` in place of
`periodicSobolevENorm 1` and *nothing else changed*; it is discharged with no
hypothesis at all.  Targets 2–6 are the fields of `PeriodicContinuationAPI` and
`PeriodicLocalTheoryAPI` copied verbatim from
`research/T11/probes/api_on_canonical.lean`, at the `H³` ball where the field
carries a ball; the only binder that survives anywhere is `hHigh`, the
`higherOrderBound` field of the same structure (U12, lanes 335/336). -/

noncomputable section

namespace NSFormalization.Section3.T11.ExistenceInputH3Probe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal

/-- **Target 1.**  Amendment 2's existence input, written out in full: this is
`PeriodicQuantitativeLocalInput'` with `periodicSobolevENorm 3 a ≤ K` in place
of `periodicSobolevENorm 1 a ≤ K`.  No hypothesis. -/
example :
    ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∀ M : ℕ → ℝ≥0∞, (∀ m, M m ≠ ⊤) →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 3 a ≤ K →
          ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
            (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) →
              ∃ w : ClassicalSolutionT ν a g δ, PeriodicLocalRegularity ν a g δ w :=
  periodicQuantitativeLocalInputH3

/-- The horizon of Target 1 is the explicit `picardHorizon ν K M`, which is a
function of `ν`, `K` and `M` only — it is applied to the datum and the force
*after* it has been produced. -/
example (ν : ℝ) (hν : 0 < ν) (K : ℝ≥0∞) (hK : K ≠ ⊤) (M : ℕ → ℝ≥0∞)
    (hM : ∀ m, M m ≠ ⊤) :
    0 < picardHorizon ν K M ∧ picardHorizon ν K M ≤ 1 ∧
      ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 3 a ≤ K →
        ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
          (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) →
            ∃ w : ClassicalSolutionT ν a g (picardHorizon ν K M),
              PeriodicLocalRegularity ν a g (picardHorizon ν K M) w := by
  exact ⟨picardHorizon_pos ν K M, picardHorizon_le_one ν K M,
    exists_classical_on_picardHorizon ν hν K hK M hM⟩

/-- **Target 2.**  The `PeriodicContinuationAPI.restart` field copied verbatim
from `api_on_canonical.lean:102-111`, at the `H³` ball.  No hypothesis. -/
example :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 3 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  NSFormalization.Section3.T11.PeriodicLocalRegularity
                    ν a' (timeShiftT t₀ f) δ w :=
  restartH3

/-- **Target 3.**  The `PeriodicContinuationAPI.restartBeyond` field copied
verbatim from `api_on_canonical.lean:121-135`, at the `H³` ball.  No
hypothesis. -/
example :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField), a ∈ initialClassT →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p →
                (∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm 3 (fun x ↦ u (t, x)) ≤ K) →
                    ∃ v : ClassicalSolutionT ν a f (S + δ),
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.velocity (t, x) = u (t, x)) ∧
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.pressure (t, x) = p (t, x)) :=
  restartBeyondH3

/-- **Target 4.**  The `PeriodicContinuationAPI.extendsBeyond` field copied
verbatim from `api_on_canonical.lean:136-143`.  The statement itself carries no
ball, and the only binder left is `hHigh` (U12's `higherOrderBound`, copied
verbatim); the `PeriodicQuantitativeLocalInput'` hypothesis of lane 337 is
gone. -/
example
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
              ExtendsBeyondT ν a f S u p :=
  extendsBeyondH3 hHigh

/-- **Target 5.**  The `PeriodicContinuationAPI.lifespanInfiniteOfLocallyFinite`
field copied verbatim from `api_on_canonical.lean:144-158`.  Same single binder
`hHigh`. -/
example
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
              maximalLifespanT ν a f = ⊤ :=
  lifespanInfiniteOfLocallyFiniteH3 hHigh

/-- **Target 6.**  The `PeriodicLocalTheoryAPI.exists_maximal` field copied
verbatim.  Unconditional — this field carries no ball at all, so it is now
closed outright. -/
example :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∃ (u : SpaceTimeField) (p : SpaceTimeScalar),
            IsMaximalPeriodicSolution ν a f u p :=
  exists_maximal_unconditional

/-- **Non-vacuity.**  The proved input is inhabited by a nonzero datum, a
nonzero smooth periodic force and a nonzero classical solution. -/
example : ∃ (a : SpatialField) (g : SpaceTimeField)
    (w : ClassicalSolutionT 1 a g 1), w.velocity (0, 0) ≠ 0 ∧ g (0, 0) ≠ 0 := by
  obtain ⟨-, -, a, g, -, -, -, -, -, -, -, w, -, hw0, hg0⟩ := nonzero_forced_witness_H3
  exact ⟨a, g, w, hw0, hg0⟩

/-- **Non-vacuity of the `L¹` force bound.**  The `H³` ball hypothesis of the
input is satisfiable together with the order-wise force bounds on the same
witness, with the `H³` ball actually binding (`le_rfl`). -/
example : ∃ (K : ℝ≥0∞) (a : SpatialField), K ≠ ⊤ ∧ a ∈ initialClassT ∧
    periodicSobolevENorm 3 a ≤ K := by
  obtain ⟨K, -, a, -, hK, -, ha, hKa, -⟩ := nonzero_forced_witness_H3
  exact ⟨K, a, hK, ha, hKa⟩

-- Axiom conformance of the three headline results, checked inside the probe.

/-- info: 'NSFormalization.Section3.T11.periodicQuantitativeLocalInputH3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms periodicQuantitativeLocalInputH3

/-- info: 'NSFormalization.Section3.T11.restartH3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms restartH3

/-- info: 'NSFormalization.Section3.T11.exists_maximal_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_maximal_unconditional

end NSFormalization.Section3.T11.ExistenceInputH3Probe
