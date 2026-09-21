import Contracts.V1.TorusNonDensity
import Bindings.TorusLocalTheory
import Bindings.CriticalRegularityT
import NSFormalization.Section3.T21.Assembly
import NSFormalization.Section3.T20.Assembly

/-!
# Binding for torus non-density

The registered lifespan and breakdown set are transported through
`Bindings.TorusLocalTheory`; all norm and class vocabulary is definitionally
shared with the canonical implementation.
-/

noncomputable section

namespace BlowupDensity.Bindings.TorusNonDensity

open Set
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V1.TorusNonDensity
open scoped ENNReal

/-- Definitional drift guard for the explicit critical ball. -/
theorem criticalBallT_eq (c ν s : ℝ) :
    criticalBallT c ν s = NSFormalization.Section3.T21.criticalBallT c ν s :=
  rfl

/-- The zero-datum breakdown set crosses the separately restated solution
structure through the registered lifespan bridge. -/
theorem breakdownSetTZero_eq (ν T : ℝ) :
    breakdownSetTZero ν T =
      NSFormalization.Section3.T21.breakdownSetTZero ν T := by
  unfold breakdownSetTZero NSFormalization.Section3.T21.breakdownSetTZero
  exact TorusLocalTheory.breakdownSetT_eq ν (fun _ : Space ↦ 0) T

/-- Registered N8, using the registered T20 global-regularity field directly. -/
theorem criticalBallDisjoint
    (K : BlowupDensity.Contracts.V1.CriticalRegularityT.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      Disjoint (criticalBallT K.c ν (1 / 2)) (breakdownSetTZero ν T) := by
  intro ν hν T _hT
  rw [Set.disjoint_left]
  intro g hball hbreak
  have htop : maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤ :=
    K.globalRegularity ν hν g hball.1 hball.2
  have hle : maximalLifespanT ν (fun _ : Space ↦ 0) g ≤
      ENNReal.ofReal T := hbreak.2
  rw [htop] at hle
  exact ENNReal.ofReal_ne_top (top_le_iff.mp hle)

/-- Registered N9. -/
theorem ballDisjoint
    (K : BlowupDensity.Contracts.V1.CriticalRegularityT.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ, 1 / 2 ≤ s →
      Disjoint (criticalBallT K.c ν s) (breakdownSetTZero ν T) := by
  intro ν hν T hT s hs
  rw [Set.disjoint_left]
  intro g hball hbreak
  have hcritical : g ∈ criticalBallT K.c ν (1 / 2) :=
    ⟨hball.1, lt_of_le_of_lt
      (NSFormalization.Section3.T21.forceSobolevMonotone s hs g) hball.2⟩
  exact Set.disjoint_left.mp (criticalBallDisjoint K ν hν T hT)
    hcritical hbreak

/-- Registered N10. -/
theorem nonDensity
    (K : BlowupDensity.Contracts.V1.CriticalRegularityT.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 1 / 2 ≤ s → ∀ T : ℝ, 0 < T →
      ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) := by
  intro ν hν s hs T hT hdense
  have hradius : 0 < ENNReal.ofReal (K.c * ν) :=
    ENNReal.ofReal_pos.mpr (mul_pos K.hc hν)
  obtain ⟨f, hbreak, hdist⟩ := hdense (0 : SpaceTimeField)
    NSFormalization.Section3.T21.zero_mem_forceClassT
    (ENNReal.ofReal (K.c * ν)) hradius
  have hball : f ∈ criticalBallT K.c ν s := by
    refine ⟨hbreak.1, ?_⟩
    simpa only [sub_zero] using hdist
  exact Set.disjoint_left.mp (ballDisjoint K ν hν T hT s hs) hball hbreak

/-- The complete registered nine-field package for any registered T20 input. -/
theorem nonDensityAPI
    (K : BlowupDensity.Contracts.V1.CriticalRegularityT.CriticalRegularityTAPI) :
    NonDensityAPI K.c where
  hc := K.hc
  criticalGlobalRegularity := K.globalRegularity
  zeroMemBall := by
    intro ν hν s
    rw [criticalBallT_eq]
    exact NSFormalization.Section3.T21.zeroMemBall K.c K.hc ν hν s
  ballRelativelyOpen := by
    intro ν hν s g hg
    rw [criticalBallT_eq] at hg ⊢
    exact NSFormalization.Section3.T21.ballRelativelyOpen K.c ν hν s g hg
  sliceSobolevMonotone := NSFormalization.Section3.T21.sliceSobolevMonotone
  forceSobolevMonotone := NSFormalization.Section3.T21.forceSobolevMonotone
  criticalBallDisjoint := criticalBallDisjoint K
  ballDisjoint := ballDisjoint K
  nonDensity := nonDensity K

/-- The registered critical-to-non-density arrow is inhabited. -/
theorem nonDensityOfCritical_holds : nonDensityOfCritical :=
  nonDensityAPI

/-- The closed package uses exactly the canonical T20 smallness constant. -/
theorem closedNonDensityAPI : NonDensityAPI NSFormalization.Section3.T20.criticalSmallnessH1 := by
  change NonDensityAPI BlowupDensity.Bindings.criticalRegularityT.c
  exact nonDensityAPI BlowupDensity.Bindings.criticalRegularityT

/-- Closed record non-vacuity at the explicit canonical constant. -/
theorem nonemptyNonDensityAPI :
    Nonempty (NonDensityAPI NSFormalization.Section3.T20.criticalSmallnessH1) :=
  ⟨closedNonDensityAPI⟩

/-- Witness-independent registered record non-vacuity. -/
theorem exists_nonemptyNonDensityAPI : ∃ c : ℝ, Nonempty (NonDensityAPI c) :=
  ⟨NSFormalization.Section3.T20.criticalSmallnessH1, nonemptyNonDensityAPI⟩

/-- The registered paper statement is closed unconditionally. -/
theorem nonDensityStatement_holds : nonDensityStatement :=
  closedNonDensityAPI.nonDensity

end BlowupDensity.Bindings.TorusNonDensity
