import NSFormalization.Section3.T10.ForcePaths

/-!
# T21 canonical non-density API

This module restates the reconciled nine-field `NonDensityAPI` from
`research/T21/Spec.lean` over the canonical Section 3 vocabulary.  The
contract-facing probe transports these declarations to the registered
vocabulary; in particular, the maximal-lifespan equality is handled there by
the existing structure-exception bridge.
-/

noncomputable section

namespace NSFormalization.Section3.T21

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open scoped ENNReal

/-- The forces that break down by `T` from the zero initial velocity. -/
def breakdownSetTZero (ν T : ℝ) : Set SpaceTimeField :=
  breakdownSetT ν (fun _ : Space ↦ 0) T

/-- The relative `L¹_t H^s_x` ball of radius `c * ν` in the force class. -/
def criticalBallT (c ν s : ℝ) : Set SpaceTimeField :=
  {g | g ∈ forceClassT ∧
    forceSobolevENormT 1 s g < ENNReal.ofReal (c * ν)}

/-- Canonical form of `cor:nondensity`, indexed by the critical smallness
constant. -/
structure NonDensityAPI (c : ℝ) : Prop where
  hc : 0 < c
  criticalGlobalRegularity : ∀ ν : ℝ, 0 < ν →
    ∀ g : SpaceTimeField, g ∈ forceClassT →
      forceSobolevENormT 1 (1 / 2) g < ENNReal.ofReal (c * ν) →
        maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤
  zeroMemBall : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ,
    (0 : SpaceTimeField) ∈ criticalBallT c ν s
  ballRelativelyOpen : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ,
    ∀ g ∈ criticalBallT c ν s,
      ∃ r : ℝ≥0∞, 0 < r ∧
        ∀ f ∈ forceClassT, forceSobolevENormT 1 s (f - g) < r →
          f ∈ criticalBallT c ν s
  sliceSobolevMonotone : ∀ s : ℝ, 1 / 2 ≤ s → ∀ z : SpatialField,
    periodicSobolevENorm (1 / 2) z ≤ periodicSobolevENorm s z
  forceSobolevMonotone : ∀ s : ℝ, 1 / 2 ≤ s → ∀ f : SpaceTimeField,
    forceSobolevENormT 1 (1 / 2) f ≤ forceSobolevENormT 1 s f
  criticalBallDisjoint : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    Disjoint (criticalBallT c ν (1 / 2)) (breakdownSetTZero ν T)
  ballDisjoint : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    ∀ s : ℝ, 1 / 2 ≤ s →
      Disjoint (criticalBallT c ν s) (breakdownSetTZero ν T)
  nonDensity : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 1 / 2 ≤ s →
    ∀ T : ℝ, 0 < T →
      ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)

/-- The paper-order headline proposition extracted from `NonDensityAPI`. -/
def nonDensityStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 1 / 2 ≤ s → ∀ T : ℝ, 0 < T →
    ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)

end NSFormalization.Section3.T21
