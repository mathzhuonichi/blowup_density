import Contracts.V1.TorusLocalTheory
import Contracts.V1.CriticalRegularityT

/-!
# Contract: torus non-density at and above the critical order

This is `cor:nondensity` from `03-torus.tex:506-520`.  It records the explicit
relative ball used in the proof, the complete nine-field reconciled API, the
paper-order statement, and its dependency on `prop:critical`.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.TorusNonDensity
set_option linter.defProp false

open Set
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ENNReal

/-- `02-preliminaries.tex:38-41`: the zero-datum breakdown set. -/
def breakdownSetTZero (ν T : ℝ) : Set SpaceTimeField :=
  breakdownSetT ν (fun _ : Space ↦ 0) T

/-- `03-torus.tex:511-514,519`: the relative ball of radius `c * ν`. -/
def criticalBallT (c ν s : ℝ) : Set SpaceTimeField :=
  {g | g ∈ forceClassT ∧ forceSobolevENormT 1 s g < ENNReal.ofReal (c * ν)}

/-- **`cor:nondensity`, `03-torus.tex:506-520`.** -/
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
  ballDisjoint : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ, 1 / 2 ≤ s →
    Disjoint (criticalBallT c ν s) (breakdownSetTZero ν T)
  nonDensity : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 1 / 2 ≤ s → ∀ T : ℝ, 0 < T →
    ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)

/-- **`cor:nondensity` in the paper's quantifier order,
`03-torus.tex:507-508`.** -/
def nonDensityStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 1 / 2 ≤ s → ∀ T : ℝ, 0 < T →
    ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)

/-- `03-torus.tex:511-516`: non-density follows from `prop:critical`. -/
def nonDensityOfCritical : Prop :=
  ∀ K : BlowupDensity.Contracts.V1.CriticalRegularityT.CriticalRegularityTAPI,
    NonDensityAPI K.c

end BlowupDensity.Contracts.V1.TorusNonDensity
