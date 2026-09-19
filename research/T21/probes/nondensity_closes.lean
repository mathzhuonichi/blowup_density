import Contracts.V1.Data
import Contracts.V1.TorusData
import Contracts.V1.TorusLocalTheory
import Bindings.TorusLocalTheory
import NSFormalization.Section3.T21.Assembly

/-!
# T21 registered-shape conformance probe

The definitions and nine-field record below are copied from
`research/T21/Spec.lean`.  Each field is then closed by an `exact` against the
canonical T21 theorem.  The only preparatory rewrites are the existing
structure-exception bridges for maximal lifespan and breakdown sets.
-/

noncomputable section

open Set
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ENNReal

namespace BlowupDensity.T21

def breakdownSetTZero (ν T : ℝ) : Set SpaceTimeField :=
  breakdownSetT ν (fun _ : Space ↦ 0) T

def criticalBallT (c ν s : ℝ) : Set SpaceTimeField :=
  {g | g ∈ forceClassT ∧
    forceSobolevENormT 1 s g < ENNReal.ofReal (c * ν)}

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

def nonDensityOfCritical : Prop :=
  ∀ K : NSFormalization.Section3.T20.CriticalRegularityTAPI,
    NonDensityAPI K.c

namespace Probe
set_option linter.defProp false

/-- Registered N0, using the canonical theorem after the lifespan rewrite. -/
theorem criticalGlobalRegularity
    (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν →
      ∀ g : SpaceTimeField, g ∈ forceClassT →
        forceSobolevENormT 1 (1 / 2) g < ENNReal.ofReal (K.c * ν) →
          maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤ := by
  intro ν hν g hg hsmall
  rw [BlowupDensity.Bindings.TorusLocalTheory.maximalLifespanT_eq]
  exact NSFormalization.Section3.T21.criticalGlobalRegularity
    K ν hν g hg hsmall

/-- The registered and canonical zero-datum breakdown sets are propositionally
equal through the existing solution-structure conversion. -/
theorem breakdownSetTZero_eq (ν T : ℝ) :
    breakdownSetTZero ν T =
      NSFormalization.Section3.T21.breakdownSetTZero ν T := by
  exact BlowupDensity.Bindings.TorusLocalTheory.breakdownSetT_eq
    ν (fun _ : Space ↦ 0) T

theorem criticalBallDisjoint
    (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      Disjoint (criticalBallT K.c ν (1 / 2)) (breakdownSetTZero ν T) := by
  intro ν hν T hT
  rw [breakdownSetTZero_eq]
  exact NSFormalization.Section3.T21.criticalBallDisjoint K ν hν T hT

theorem ballDisjoint
    (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ, 1 / 2 ≤ s →
      Disjoint (criticalBallT K.c ν s) (breakdownSetTZero ν T) := by
  intro ν hν T hT s hs
  rw [breakdownSetTZero_eq]
  exact NSFormalization.Section3.T21.ballDisjoint K ν hν T hT s hs

theorem nonDensity
    (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 1 / 2 ≤ s → ∀ T : ℝ, 0 < T →
      ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) := by
  intro ν hν s hs T hT
  rw [breakdownSetTZero_eq]
  exact NSFormalization.Section3.T21.nonDensity K ν hν s hs T hT

/-! Every reconciled field is checked by `exact`. -/

example (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    0 < K.c := by
  exact K.hc

example (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν →
      ∀ g : SpaceTimeField, g ∈ forceClassT →
        forceSobolevENormT 1 (1 / 2) g < ENNReal.ofReal (K.c * ν) →
          maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤ := by
  exact criticalGlobalRegularity K

example (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ s : ℝ,
      (0 : SpaceTimeField) ∈ criticalBallT K.c ν s := by
  exact NSFormalization.Section3.T21.zeroMemBall K.c K.hc

example (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ s : ℝ,
      ∀ g ∈ criticalBallT K.c ν s,
        ∃ r : ℝ≥0∞, 0 < r ∧
          ∀ f ∈ forceClassT, forceSobolevENormT 1 s (f - g) < r →
            f ∈ criticalBallT K.c ν s := by
  exact NSFormalization.Section3.T21.ballRelativelyOpen K.c

example : ∀ s : ℝ, 1 / 2 ≤ s → ∀ z : SpatialField,
    periodicSobolevENorm (1 / 2) z ≤ periodicSobolevENorm s z := by
  exact NSFormalization.Section3.T21.sliceSobolevMonotone

example : ∀ s : ℝ, 1 / 2 ≤ s → ∀ f : SpaceTimeField,
    forceSobolevENormT 1 (1 / 2) f ≤ forceSobolevENormT 1 s f := by
  exact NSFormalization.Section3.T21.forceSobolevMonotone

example (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      Disjoint (criticalBallT K.c ν (1 / 2)) (breakdownSetTZero ν T) := by
  exact criticalBallDisjoint K

example (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ, 1 / 2 ≤ s →
      Disjoint (criticalBallT K.c ν s) (breakdownSetTZero ν T) := by
  exact ballDisjoint K

example (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 1 / 2 ≤ s → ∀ T : ℝ, 0 < T →
      ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) := by
  exact nonDensity K

/-- Registered assembly of all nine exact-field probes. -/
def nonDensityAPI
    (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    NonDensityAPI K.c where
  hc := K.hc
  criticalGlobalRegularity := criticalGlobalRegularity K
  zeroMemBall := NSFormalization.Section3.T21.zeroMemBall K.c K.hc
  ballRelativelyOpen := NSFormalization.Section3.T21.ballRelativelyOpen K.c
  sliceSobolevMonotone := NSFormalization.Section3.T21.sliceSobolevMonotone
  forceSobolevMonotone := NSFormalization.Section3.T21.forceSobolevMonotone
  criticalBallDisjoint := criticalBallDisjoint K
  ballDisjoint := ballDisjoint K
  nonDensity := nonDensity K

example : nonDensityOfCritical := by
  intro K
  exact nonDensityAPI K

/-! N12 registered-shape transport. -/

example : (fun _ : Space ↦ 0) ∈ initialClassT := by
  exact NSFormalization.Section3.T21.zeroInitialClass

end Probe
end BlowupDensity.T21
