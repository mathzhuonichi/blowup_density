import Contracts.V2.Continuation
import Bindings.ContinuationV2
import TestSupport.Axioms

/-!
Public-type, statement-conformance, and transitive-axiom checks for A04
continuation V2.  This is an independent V2 interface, not an extension of an
unproved V1 continuation structure.
-/

noncomputable section

namespace BlowupDensity.Tests

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open Contracts.V1.Data
open Contracts.V2.Continuation
open scoped ENNReal

/-- The implementation supplies all five owner-approved/proved fields. -/
theorem checkedContinuationV2 :
    ContinuationV2API NSFormalization.Section4.A01.localHorizon' :=
  Bindings.continuationV2

run_cmd TestSupport.checkAxioms ``checkedContinuationV2

/-- Conformance with the owner-approved restart wording: force and `S` precede
the existential duration; the bound is `H⁷`; the duration is uniform over
every restart time in `[0,S]`. -/
example :
    ∀ ν : ℝ, 0 < ν → ∀ f : SpaceTimeField, MemForceR f →
      ∀ S : ℝ, 0 ≤ S → ∀ K : ℝ≥0∞, K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S, ∀ a' : SpatialField, a' ∈ initialClassR →
            sobolevENorm 7 a' ≤ K →
              δ ≤ NSFormalization.Section4.A01.localHorizon' ν a' (timeShift t₀ f) :=
  checkedContinuationV2.restart

/-- Conformance with `research/A04/Spec.lean`'s unchanged
`higherOrderBound` field. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
      ∀ S : ℝ, 0 < S → ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        SolvesBelow ν a f S u p → squaredHTwoIntegral S u ≠ ⊤ →
          ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
            ∀ t ∈ Ico (0 : ℝ) S,
              sobolevENorm (m : ℝ) (fun x : Space => u (t, x)) ≤ M :=
  checkedContinuationV2.higherOrderBound

/-- Conformance with lane 217's fixed-force `H⁷` endpoint theorem. -/
example :
    ∀ (ν : ℝ), 0 < ν → ∀ (f : SpaceTimeField), MemForceR f →
      ∀ (S : ℝ), 0 < S → ∀ K : ℝ≥0∞, K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField) (u : SpaceTimeField) (p : SpaceTimeScalar),
            a ∈ initialClassR → SolvesBelow ν a f S u p →
              (∀ t ∈ Ico (0 : ℝ) S,
                sobolevENorm 7 (fun x : Space => u (t, x)) ≤ K) →
              ENNReal.ofReal (S + δ) ≤ maximalLifespanR ν a f :=
  checkedContinuationV2.restartBeyond

/-- Conformance with lane 217's unconditional integral continuation theorem. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ S : ℝ, 0 < S → ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        SolvesBelow ν a f S u p → squaredHTwoIntegral S u ≠ ⊤ →
          ENNReal.ofReal S < maximalLifespanR ν a f :=
  checkedContinuationV2.extendsBeyond

/-- Conformance with lane 217's maximal-lifespan packaging. -/
example :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalSolution ν a f u p →
            (∀ S : ℝ, 0 < S → ENNReal.ofReal S ≤ maximalLifespanR ν a f →
              squaredHTwoIntegral S u ≠ ⊤) →
            maximalLifespanR ν a f = ⊤ :=
  checkedContinuationV2.lifespanInfiniteOfLocallyFinite

/-- Non-vacuity at explicitly nonzero inputs: once a nonzero force and datum
satisfy the displayed class/bound hypotheses, the checked restart produces an
actual positive real duration, not merely an inhabited proposition.  The
research conformance file supplies concrete compact-bump witnesses for these
hypotheses. -/
example (f : SpaceTimeField) (hf : MemForceR f) (_hf0 : f ≠ 0)
    (a' : SpatialField) (ha' : a' ∈ initialClassR) (_ha0 : a' ≠ 0)
    (K : ℝ≥0∞) (hK : K ≠ ⊤) (haK : sobolevENorm 7 a' ≤ K) :
    ∃ δ : ℝ, 0 < δ ∧
      δ ≤ NSFormalization.Section4.A01.localHorizon' 1 a' (timeShift 0 f) := by
  obtain ⟨δ, hδ, hr⟩ := checkedContinuationV2.restart
    1 (by norm_num) f hf 0 le_rfl K hK
  exact ⟨δ, hδ, hr 0 (by simp) a' ha' haK⟩

end BlowupDensity.Tests
