import Contracts.V2.Continuation
import Bindings.MaximalPartialV2
import NSFormalization.Section4.A04.ShiftedExtension

/-!
# Binding for A04 continuation V2

The witness is assembled from lanes 215 and 217:

* `restartFixedForce_of_memForceR` supplies the fixed-force `H⁷` restart;
* `higherOrderBound_of_gronwall` supplies the unchanged higher-order bound;
* the three primed theorems in `ShiftedExtension.lean` supply endpoint restart,
  strict continuation, and infinite lifespan with shifted gluing discharged.

The contract is parameterized by its horizon function because
`NSFormalization.Section4.A01.LocalTheoryBundle` is not in
`experiments/check_contracts.py`'s `CONTRACT_CANONICAL_MODULES`.  The witness
instantiates the parameter with the actual `A01.localHorizon'`; the restart
predicate and its `timeShift` then agree with the implementation by `rfl`.

Definitions made only from data vocabulary bridge by `rfl`.  `SolvesBelow`,
`IsMaximalSolution`, and `maximalLifespanR` quantify over the two distinct
`ClassicalSolutionR` structures, so they use the established field-by-field
conversions and `maximalPartial_maximalLifespanR_eq` instead.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

namespace C

abbrev timeShift := Contracts.V2.Continuation.timeShift
abbrev squaredHTwoIntegral := Contracts.V2.Continuation.squaredHTwoIntegral
abbrev SolvesBelow := Contracts.V2.Continuation.SolvesBelow
abbrev MemL1Hm := Contracts.V2.Continuation.MemL1Hm
abbrev IsMaximalSolution := Contracts.V2.Continuation.IsMaximalSolution
abbrev RestartFixedForce := Contracts.V2.Continuation.RestartFixedForce
abbrev ContinuationV2API := Contracts.V2.Continuation.ContinuationV2API

end C

/-! ## Definitional correspondence -/

/-- The contract and implementation initial classes have the same body. -/
theorem continuationV2_initialClassR_eq :
    (initialClassR : Set SpatialField) =
      NSFormalization.Section4.A02.initialClassR := rfl

/-- The contract and implementation force classes have the same body. -/
theorem continuationV2_memForceR_eq (f : SpaceTimeField) :
    MemForceR f = NSFormalization.Section4.A02.MemForceR f := rfl

/-- The registered datum norm is the implementation norm. -/
theorem continuationV2_sobolevENorm_eq :
    sobolevENorm = NSFormalization.Section4.D01.sobolevENorm := rfl

/-- The registered force `L¹_tH^s_x` norm is the implementation norm. -/
theorem continuationV2_forceSobolevENormL1_eq :
    forceSobolevENormL1 = NSFormalization.Section4.D01.forceSobolevENormL1 := rfl

/-- Positive-time translation is restated token-for-token. -/
theorem continuationV2_timeShift_eq :
    C.timeShift = NSFormalization.Section4.A04.timeShift := rfl

/-- The squared `H²` integral is restated token-for-token. -/
theorem continuationV2_squaredHTwoIntegral_eq :
    C.squaredHTwoIntegral =
      NSFormalization.Section4.A04.squaredHTwoIntegral := rfl

/-- The separate `L¹_tH^m_x` predicate is restated token-for-token. -/
theorem continuationV2_memL1Hm_eq :
    C.MemL1Hm = NSFormalization.Section4.A04.MemL1Hm := rfl

/-- Instantiating the contract's horizon parameter with the proved A01 horizon
makes the approved restart predicate exactly lane 215's `RestartFixedForce`. -/
theorem continuationV2_restartFixedForce_eq :
    C.RestartFixedForce NSFormalization.Section4.A01.localHorizon' =
      (∀ ν : ℝ, 0 < ν → ∀ f : SpaceTimeField,
        NSFormalization.Section4.A02.MemForceR f →
        ∀ S : ℝ, 0 ≤ S →
          NSFormalization.Section4.A04.RestartFixedForce ν f S) := rfl

/-! ## Transport through `ClassicalSolutionR` -/

/-- `SolvesBelow` transports in both directions by converting each shorter
classical solution field by field. -/
theorem continuationV2_solvesBelow_iff
    (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
    (u : SpaceTimeField) (p : SpaceTimeScalar) :
    C.SolvesBelow ν a f S u p ↔
      NSFormalization.Section4.A04.SolvesBelow ν a f S u p := by
  constructor
  · intro h b hb hbS
    obtain ⟨w, hv, hp⟩ := h b hb hbS
    exact ⟨uniqueness_toA02 w, hv, hp⟩
  · intro h b hb hbS
    obtain ⟨w, hv, hp⟩ := h b hb hbS
    exact ⟨maximalPartial_ofA02 w, hv, hp⟩

/-- The contract's maximal-solution predicate is the implementation's after
the solution conversion and maximal-lifespan bridge. -/
theorem continuationV2_isMaximalSolution_iff
    (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (u : SpaceTimeField) (p : SpaceTimeScalar) :
    NSFormalization.Section4.A02.IsMaximalSolution ν a f u p ↔
      C.IsMaximalSolution ν a f u p := by
  change NSFormalization.Section4.A02.IsMaximalSolution ν a f u p ↔
    Contracts.V2.MaximalPartial.IsMaximalSolution ν a f u p
  exact maximalPartial_isMaximalSolution_iff ν a f u p

/-! ## Checked witness -/

/-- The owner-approved A04 continuation V2 interface.  It has only
propositional fields, so the witness is a theorem. -/
theorem continuationV2 :
    C.ContinuationV2API NSFormalization.Section4.A01.localHorizon' where
  restart := by
    intro ν hν f hf S hS
    exact NSFormalization.Section4.A04.restartFixedForce_of_memForceR
      ν hν f hf S hS
  higherOrderBound := by
    intro ν a f hν ha hf hf1 S hS u p hu hfin m
    exact NSFormalization.Section4.A04.higherOrderBound_of_gronwall
      ν a f hν ha hf hf1 S hS u p
      ((continuationV2_solvesBelow_iff ν a f S u p).mp hu) hfin m
  restartBeyond := by
    intro ν hν f hf S hS K hK
    obtain ⟨δ, hδ, hrestart⟩ :=
      NSFormalization.Section4.A04.restartBeyond_of_memForceR'
        ν hν f hf S hS K hK
    refine ⟨δ, hδ, ?_⟩
    intro a u p ha hu hbound
    rw [← maximalPartial_maximalLifespanR_eq]
    exact hrestart a u p ha
      ((continuationV2_solvesBelow_iff ν a f S u p).mp hu) hbound
  extendsBeyond := by
    intro ν a f hν ha hf S hS u p hu hfin
    rw [← maximalPartial_maximalLifespanR_eq]
    exact NSFormalization.Section4.A04.extendsBeyond_of_memForceR'
      ν a f hν ha hf S hS u p
      ((continuationV2_solvesBelow_iff ν a f S u p).mp hu) hfin
  lifespanInfiniteOfLocallyFinite := by
    intro ν a f hν ha hf u p hu hfin
    have hu' : NSFormalization.Section4.A02.IsMaximalSolution ν a f u p :=
      (continuationV2_isMaximalSolution_iff ν a f u p).mpr hu
    have hfin' : ∀ S : ℝ, 0 < S →
        ENNReal.ofReal S ≤ NSFormalization.Section4.A02.maximalLifespanR ν a f →
          NSFormalization.Section4.A04.squaredHTwoIntegral S u ≠ ⊤ := by
      intro S hS hle
      exact hfin S hS
        (hle.trans_eq (maximalPartial_maximalLifespanR_eq ν a f))
    rw [← maximalPartial_maximalLifespanR_eq]
    exact NSFormalization.Section4.A04.lifespanInfiniteOfLocallyFinite_of_memForceR'
      ν a f hν ha hf u p hu' hfin'

end BlowupDensity.Bindings
