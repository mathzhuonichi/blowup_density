import Contracts.V1.TorusLocalTheory
import Contracts.V2.Continuation
import Contracts.V2.LocalTheory
import Bindings.TorusData
import NSFormalization.Section3.T11.Assembly

/-!
# Binding for the periodic local-theory contract

Part 1 checks every restated `def` of `Contracts/V1/TorusLocalTheory.lean`
against the canonical modules `NSFormalization.Section3.T10.PeriodicData` and
`NSFormalization.Section3.T11.LocalTheory` by `rfl`.

Part 2 is the **structure exception** (`CLAUDE.md`).  `ClassicalSolutionT` is
restated as a `structure`, hence a different inductive type from the canonical
one; no `rfl` bridge exists.  Every field type is definitionally equal, so the
fieldwise conversions `toContract` / `ofContract` typecheck by `rfl` on each
field, and both round trips are `rfl`.  The declarations that mention
`ClassicalSolutionT` — `maximalLifespanT`, `RegularThroughT`, `breakdownSet*`,
`SolvesBelowT`, `IsMaximalPeriodicSolution`, `ExtendsBeyondT` and
`PeriodicLocalRegularity` — are bridged through those conversions instead.

Part 3 transports the four API terms of `Section3/T11/Assembly.lean` across the
conversions.  The registered continuation API is the `H³` narrowing
`PeriodicContinuationH3API`; the manuscript's two `H¹` sentences stay unproved
named predicates (contract module docstring, `research/T11/H1_GAP.md`).
-/

noncomputable section

namespace BlowupDensity.Bindings.TorusLocalTheory

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ContDiff ENNReal BigOperators

-- Named (never anonymous) short-circuits for the `lp`-based Sobolev carrier;
-- the global instance searches on `↥(PeriodicSobolev s)` time out at the
-- default heartbeat budget (`Section3/T11/ExistenceInputH3.lean`).
local instance torusLocalTheoryNormedGroup (s : ℝ) :
    NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance torusLocalTheoryNormedSpace (s : ℝ) :
    NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-! ## 1. Definitional drift guards for the restated `def`s -/

theorem isPeriodicSobolevPath_eq (s : ℝ) (f : SpaceTimeField)
    (G : ℝ → PeriodicSobolev s) :
    IsPeriodicSobolevPath s f G =
      NSFormalization.Section3.T10.IsPeriodicSobolevPath s f G := rfl

theorem forceSobolevENormT_eq (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) :
    forceSobolevENormT q s f =
      NSFormalization.Section3.T10.forceSobolevENormT q s f := rfl

theorem initialClassT_eq :
    initialClassT = NSFormalization.Section3.T10.initialClassT := rfl

theorem memForceT_eq (f : SpaceTimeField) :
    MemForceT f = NSFormalization.Section3.T10.MemForceT f := rfl

theorem forceClassT_eq :
    forceClassT = NSFormalization.Section3.T10.forceClassT := rfl

theorem pressureMeanT_eq (p : SpaceTimeScalar) (t : ℝ) :
    pressureMeanT p t = NSFormalization.Section3.T10.pressureMeanT p t := rfl

theorem pressureGaugeT_eq (I : Set ℝ) (p : SpaceTimeScalar) :
    PressureGaugeT I p = NSFormalization.Section3.T10.PressureGaugeT I p := rfl

theorem normalizePressureT_eq (p : SpaceTimeScalar) :
    normalizePressureT p =
      NSFormalization.Section3.T10.normalizePressureT p := rfl

theorem relativelyDenseT_eq (q : ℝ≥0∞) (s : ℝ) (Y S : Set SpaceTimeField) :
    RelativelyDenseT q s Y S =
      NSFormalization.Section3.T10.RelativelyDenseT q s Y S := rfl

theorem energyEssSupT_eq (T : ℝ) (z : SpaceTimeField) :
    energyEssSupT T z = NSFormalization.Section3.T10.energyEssSupT T z := rfl

theorem energyGradientT_eq (T : ℝ) (z : SpaceTimeField) :
    energyGradientT T z =
      NSFormalization.Section3.T10.energyGradientT T z := rfl

theorem energyENormT_eq (T : ℝ) (z : SpaceTimeField) :
    energyENormT T z = NSFormalization.Section3.T10.energyENormT T z := rfl

theorem coefficientEnergyEssSupT_eq (T : ℝ) (z : SpaceTimeField) :
    coefficientEnergyEssSupT T z =
      NSFormalization.Section3.T10.coefficientEnergyEssSupT T z := rfl

theorem coefficientEnergyGradientT_eq (T : ℝ) (z : SpaceTimeField) :
    coefficientEnergyGradientT T z =
      NSFormalization.Section3.T10.coefficientEnergyGradientT T z := rfl

theorem coefficientEnergyENormT_eq (T : ℝ) (z : SpaceTimeField) :
    coefficientEnergyENormT T z =
      NSFormalization.Section3.T10.coefficientEnergyENormT T z := rfl

theorem isPeriodicSobolevPathOn_eq (s : ℝ) (I : Set ℝ) (u : SpaceTimeField)
    (G : ℝ → PeriodicSobolev s) :
    IsPeriodicSobolevPathOn s I u G =
      NSFormalization.Section3.T11.IsPeriodicSobolevPathOn s I u G := rfl

theorem convectionDivergenceT_eq (u : SpaceTimeField) (t : ℝ) (x : Space) :
    convectionDivergenceT u t x =
      NSFormalization.Section3.T11.convectionDivergenceT u t x := rfl

/-- The periodic convection definition has exactly the registered Section 4
body (`Contracts/V2/LocalTheory.lean:58-60`). -/
theorem convectionDivergenceT_eq_v2 (u : SpaceTimeField) (t : ℝ) (x : Space) :
    convectionDivergenceT u t x =
      BlowupDensity.Contracts.V2.LocalTheory.convectionDivergence u t x := rfl

theorem scalarSpatialLaplacianT_eq (p : SpaceTimeScalar) (t : ℝ) (x : Space) :
    scalarSpatialLaplacianT p t x =
      NSFormalization.Section3.T11.scalarSpatialLaplacianT p t x := rfl

theorem squaredHTwoIntegralT_eq (S : ℝ) (u : SpaceTimeField) :
    squaredHTwoIntegralT S u =
      NSFormalization.Section3.T11.squaredHTwoIntegralT S u := rfl

theorem timeShiftT_eq (t₀ : ℝ) (f : SpaceTimeField) :
    timeShiftT t₀ f = NSFormalization.Section3.T11.timeShiftT t₀ f := rfl

/-- The periodic time shift has exactly the registered Section 4 body
(`Contracts/V2/Continuation.lean:50-51`). -/
theorem timeShiftT_eq_v2 (t₀ : ℝ) (f : SpaceTimeField) :
    timeShiftT t₀ f = BlowupDensity.Contracts.V2.Continuation.timeShift t₀ f :=
  rfl

theorem velocityMeanT_eq (u : SpaceTimeField) (t : ℝ) :
    velocityMeanT u t = NSFormalization.Section3.T11.velocityMeanT u t := rfl

theorem forceMeanT_eq (f : SpaceTimeField) (t : ℝ) :
    forceMeanT f t = NSFormalization.Section3.T11.forceMeanT f t := rfl

theorem galileanMeanT_eq (a : SpatialField) (f : SpaceTimeField) (t : ℝ) :
    galileanMeanT a f t =
      NSFormalization.Section3.T11.galileanMeanT a f t := rfl

theorem galileanShiftT_eq (a : SpatialField) (f : SpaceTimeField) (t : ℝ) :
    galileanShiftT a f t =
      NSFormalization.Section3.T11.galileanShiftT a f t := rfl

theorem galileanVelocityT_eq (a : SpatialField) (f u : SpaceTimeField) :
    galileanVelocityT a f u =
      NSFormalization.Section3.T11.galileanVelocityT a f u := rfl

theorem galileanForceT_eq (a : SpatialField) (f : SpaceTimeField) :
    galileanForceT a f = NSFormalization.Section3.T11.galileanForceT a f := rfl

theorem galileanPressureT_eq (a : SpatialField) (f : SpaceTimeField)
    (p : SpaceTimeScalar) :
    galileanPressureT a f p =
      NSFormalization.Section3.T11.galileanPressureT a f p := rfl

theorem unitViscosityInitialT_eq (ν : ℝ) (a : SpatialField) :
    unitViscosityInitialT ν a =
      NSFormalization.Section3.T11.unitViscosityInitialT ν a := rfl

theorem unitViscosityVelocityT_eq (ν : ℝ) (u : SpaceTimeField) :
    unitViscosityVelocityT ν u =
      NSFormalization.Section3.T11.unitViscosityVelocityT ν u := rfl

theorem unitViscosityPressureT_eq (ν : ℝ) (p : SpaceTimeScalar) :
    unitViscosityPressureT ν p =
      NSFormalization.Section3.T11.unitViscosityPressureT ν p := rfl

theorem unitViscosityForceT_eq (ν : ℝ) (f : SpaceTimeField) :
    unitViscosityForceT ν f =
      NSFormalization.Section3.T11.unitViscosityForceT ν f := rfl

theorem restoreViscosityVelocityT_eq (ν : ℝ) (u : SpaceTimeField) :
    restoreViscosityVelocityT ν u =
      NSFormalization.Section3.T11.restoreViscosityVelocityT ν u := rfl

theorem restoreViscosityPressureT_eq (ν : ℝ) (p : SpaceTimeScalar) :
    restoreViscosityPressureT ν p =
      NSFormalization.Section3.T11.restoreViscosityPressureT ν p := rfl

theorem restoreViscosityForceT_eq (ν : ℝ) (f : SpaceTimeField) :
    restoreViscosityForceT ν f =
      NSFormalization.Section3.T11.restoreViscosityForceT ν f := rfl

/-! ## 2. The structure exception: `ClassicalSolutionT`

The contract copy and the canonical structure have definitionally equal fields,
so the conversions below are pure field transport and the round trips are
`rfl`. -/

/-- Canonical solution ⟶ contract solution, field by field. -/
def toContract {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : NSFormalization.Section3.T10.ClassicalSolutionT ν a f T) :
    ClassicalSolutionT ν a f T where
  velocity := w.velocity
  pressure := w.pressure
  horizon_pos := w.horizon_pos
  velocity_smooth := w.velocity_smooth
  pressure_smooth := w.pressure_smooth
  initial := w.initial
  divergence := w.divergence
  momentum := w.momentum
  sobolev := w.sobolev
  pressure_gradient := w.pressure_gradient
  velocity_periodic := w.velocity_periodic
  pressure_periodic := w.pressure_periodic
  pressure_gauge := w.pressure_gauge

/-- Contract solution ⟶ canonical solution, field by field. -/
def ofContract {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionT ν a f T) :
    NSFormalization.Section3.T10.ClassicalSolutionT ν a f T where
  velocity := w.velocity
  pressure := w.pressure
  horizon_pos := w.horizon_pos
  velocity_smooth := w.velocity_smooth
  pressure_smooth := w.pressure_smooth
  initial := w.initial
  divergence := w.divergence
  momentum := w.momentum
  sobolev := w.sobolev
  pressure_gradient := w.pressure_gradient
  velocity_periodic := w.velocity_periodic
  pressure_periodic := w.pressure_periodic
  pressure_gauge := w.pressure_gauge

@[simp] theorem toContract_velocity {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} {T : ℝ}
    (w : NSFormalization.Section3.T10.ClassicalSolutionT ν a f T) :
    (toContract w).velocity = w.velocity := rfl

@[simp] theorem toContract_pressure {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} {T : ℝ}
    (w : NSFormalization.Section3.T10.ClassicalSolutionT ν a f T) :
    (toContract w).pressure = w.pressure := rfl

@[simp] theorem ofContract_velocity {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} {T : ℝ} (w : ClassicalSolutionT ν a f T) :
    (ofContract w).velocity = w.velocity := rfl

@[simp] theorem ofContract_pressure {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} {T : ℝ} (w : ClassicalSolutionT ν a f T) :
    (ofContract w).pressure = w.pressure := rfl

/-- Round trip, canonical ⟶ contract ⟶ canonical. -/
theorem ofContract_toContract {ν : ℝ} {a : SpatialField} {f : SpaceTimeField}
    {T : ℝ} (w : NSFormalization.Section3.T10.ClassicalSolutionT ν a f T) :
    ofContract (toContract w) = w := rfl

/-- Round trip, contract ⟶ canonical ⟶ contract. -/
theorem toContract_ofContract {ν : ℝ} {a : SpatialField} {f : SpaceTimeField}
    {T : ℝ} (w : ClassicalSolutionT ν a f T) :
    toContract (ofContract w) = w := rfl

theorem nonempty_classicalSolutionT_iff (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) (S : ℝ) :
    Nonempty (ClassicalSolutionT ν a f S) ↔
      Nonempty (NSFormalization.Section3.T10.ClassicalSolutionT ν a f S) :=
  ⟨fun ⟨w⟩ ↦ ⟨ofContract w⟩, fun ⟨w⟩ ↦ ⟨toContract w⟩⟩

/-! ### Declarations bridged through the conversions -/

theorem maximalLifespanT_eq (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) :
    maximalLifespanT ν a f =
      NSFormalization.Section3.T10.maximalLifespanT ν a f :=
  iSup_congr fun S ↦
    iSup_congr_Prop (nonempty_classicalSolutionT_iff ν a f S) fun _ ↦ rfl

theorem regularThroughT_eq (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (T : ℝ) :
    RegularThroughT ν a f T =
      NSFormalization.Section3.T10.RegularThroughT ν a f T := by
  refine propext ⟨?_, ?_⟩ <;> rintro ⟨δ, hδ, h⟩
  · exact ⟨δ, hδ, (nonempty_classicalSolutionT_iff ν a f (T + δ)).mp h⟩
  · exact ⟨δ, hδ, (nonempty_classicalSolutionT_iff ν a f (T + δ)).mpr h⟩

theorem breakdownSetInT_eq (Y : Set SpaceTimeField) (ν : ℝ) (a : SpatialField)
    (T : ℝ) :
    breakdownSetInT Y ν a T =
      NSFormalization.Section3.T10.breakdownSetInT Y ν a T := by
  ext f
  constructor
  · rintro ⟨hY, hle⟩
    exact ⟨hY, by rwa [maximalLifespanT_eq] at hle⟩
  · rintro ⟨hY, hle⟩
    exact ⟨hY, by rwa [← maximalLifespanT_eq] at hle⟩

theorem breakdownSetT_eq (ν : ℝ) (a : SpatialField) (T : ℝ) :
    breakdownSetT ν a T = NSFormalization.Section3.T10.breakdownSetT ν a T :=
  breakdownSetInT_eq _ ν a T

theorem solvesBelowT_eq (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (S : ℝ) (u : SpaceTimeField) (p : SpaceTimeScalar) :
    SolvesBelowT ν a f S u p =
      NSFormalization.Section3.T11.SolvesBelowT ν a f S u p := by
  refine propext ⟨fun h b hb hbS ↦ ?_, fun h b hb hbS ↦ ?_⟩
  · obtain ⟨w, hu, hp⟩ := h b hb hbS
    exact ⟨ofContract w, hu, hp⟩
  · obtain ⟨w, hu, hp⟩ := h b hb hbS
    exact ⟨toContract w, hu, hp⟩

theorem isMaximalPeriodicSolution_eq (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) (u : SpaceTimeField) (p : SpaceTimeScalar) :
    IsMaximalPeriodicSolution ν a f u p =
      NSFormalization.Section3.T11.IsMaximalPeriodicSolution ν a f u p := by
  refine propext ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ ⟨?_, ?_⟩⟩
  · exact maximalLifespanT_eq ν a f ▸ h.1
  · intro S hS hlife
    obtain ⟨w, hu, hp⟩ := h.2 S hS (by rw [maximalLifespanT_eq]; exact hlife)
    exact ⟨ofContract w, hu, hp⟩
  · exact (maximalLifespanT_eq ν a f).symm ▸ h.1
  · intro S hS hlife
    obtain ⟨w, hu, hp⟩ := h.2 S hS (by rw [← maximalLifespanT_eq]; exact hlife)
    exact ⟨toContract w, hu, hp⟩

theorem extendsBeyondT_eq (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (S : ℝ) (u : SpaceTimeField) (p : SpaceTimeScalar) :
    ExtendsBeyondT ν a f S u p =
      NSFormalization.Section3.T11.ExtendsBeyondT ν a f S u p := by
  refine propext ⟨?_, ?_⟩ <;> rintro ⟨δ, hδ, v, hu, hp⟩
  · exact ⟨δ, hδ, ofContract v, hu, hp⟩
  · exact ⟨δ, hδ, toContract v, hu, hp⟩

/-- The regularity record transports along the conversion in both directions;
it depends on the solution only through `velocity` and `pressure`, which the
conversion preserves by `rfl`. -/
theorem periodicLocalRegularity_eq {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} {T : ℝ} (w : ClassicalSolutionT ν a f T) :
    PeriodicLocalRegularity ν a f T w =
      NSFormalization.Section3.T11.PeriodicLocalRegularity ν a f T
        (ofContract w) :=
  propext
    ⟨fun h ↦ ⟨h.sobolev_smooth, h.pressure_poisson, h.projected⟩,
      fun h ↦ ⟨h.sobolev_smooth, h.pressure_poisson, h.projected⟩⟩

/-- The same transport, stated at a canonical solution. -/
theorem periodicLocalRegularity_toContract {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} {T : ℝ}
    (w : NSFormalization.Section3.T10.ClassicalSolutionT ν a f T) :
    PeriodicLocalRegularity ν a f T (toContract w) =
      NSFormalization.Section3.T11.PeriodicLocalRegularity ν a f T w :=
  periodicLocalRegularity_eq (toContract w)

/-! ## 3. Transport of the four API terms -/

/-- The eight-field periodic local theory, transported from
`Section3/T11/Assembly.lean`. -/
noncomputable def torusLocalTheoryAPI : PeriodicLocalTheoryAPI where
  horizon := NSFormalization.Section3.T11.periodicLocalHorizon
  solution := fun ν hν a ha f hf ↦
    toContract (NSFormalization.Section3.T11.periodicLocalSolution ν hν a ha f hf)
  regularity := fun ν hν a ha f hf ↦
    (periodicLocalRegularity_toContract _).mpr
      (NSFormalization.Section3.T11.periodicLocalTheoryAPI.regularity
        ν hν a ha f hf)
  velocity_unique := fun ν hν a ha f hf T₁ T₂ u₁ u₂ t ht x ↦
    NSFormalization.Section3.T11.velocity_unique ν hν a ha f hf T₁ T₂
      (ofContract u₁) (ofContract u₂) t ht x
  pressure_unique := fun ν hν a ha f hf T₁ T₂ u₁ u₂ t ht x ↦
    NSFormalization.Section3.T11.pressure_unique ν hν a ha f hf T₁ T₂
      (ofContract u₁) (ofContract u₂) t ht x
  horizon_le_lifespan := by
    intro ν hν a ha f hf
    rw [maximalLifespanT_eq]
    exact NSFormalization.Section3.T11.periodicLocalTheoryAPI.horizon_le_lifespan
      ν hν a ha f hf
  exists_maximal := by
    intro ν hν a ha f hf
    obtain ⟨u, p, hup⟩ :=
      NSFormalization.Section3.T11.exists_maximal_unconditional ν hν a ha f hf
    exact ⟨u, p, (isMaximalPeriodicSolution_eq ν a f u p).mpr hup⟩
  maximal_unique := by
    intro ν hν a ha f hf u₁ u₂ p₁ p₂ h₁ h₂ t ht htlife x
    exact NSFormalization.Section3.T11.maximal_unique ν hν a ha f hf u₁ u₂ p₁ p₂
      ((isMaximalPeriodicSolution_eq ν a f u₁ p₁).mp h₁)
      ((isMaximalPeriodicSolution_eq ν a f u₂ p₂).mp h₂)
      t ht (by rwa [maximalLifespanT_eq] at htlife) x

/-- The registered `H³` narrowing of the continuation package, transported. -/
theorem torusContinuationH3API : PeriodicContinuationH3API where
  restart := by
    intro ν hν f hf S hS K hK
    obtain ⟨δ, hδ, h⟩ :=
      NSFormalization.Section3.T11.restartH3 ν hν f hf S hS K hK
    refine ⟨δ, hδ, fun t₀ ht₀ a' ha' hK' ↦ ?_⟩
    obtain ⟨w, hw⟩ := h t₀ ht₀ a' ha' hK'
    exact ⟨toContract w, (periodicLocalRegularity_toContract w).mpr hw⟩
  higherOrderBound := by
    intro ν hν a ha f hf S hS u p hsolve hfin m
    exact NSFormalization.Section3.T11.torusHigherOrderBound ν hν a ha f hf S hS
      u p ((solvesBelowT_eq ν a f S u p).mp hsolve) hfin m
  restartBeyond := by
    intro ν hν f hf S hS K hK
    obtain ⟨δ, hδ, h⟩ :=
      NSFormalization.Section3.T11.restartBeyondH3 ν hν f hf S hS K hK
    refine ⟨δ, hδ, fun a ha u p hsolve hbound ↦ ?_⟩
    obtain ⟨v, hu, hp⟩ :=
      h a ha u p ((solvesBelowT_eq ν a f S u p).mp hsolve) hbound
    exact ⟨toContract v, hu, hp⟩
  extendsBeyond := by
    intro ν hν a ha f hf S hS u p hsolve hfin
    exact (extendsBeyondT_eq ν a f S u p).mpr
      (NSFormalization.Section3.T11.periodicContinuationH3API.extendsBeyond
        ν hν a ha f hf S hS u p ((solvesBelowT_eq ν a f S u p).mp hsolve) hfin)
  lifespanInfiniteOfLocallyFinite := by
    intro ν hν a ha f hf u p hmax hcrit
    rw [maximalLifespanT_eq]
    refine
      NSFormalization.Section3.T11.periodicContinuationH3API.lifespanInfiniteOfLocallyFinite
        ν hν a ha f hf u p ((isMaximalPeriodicSolution_eq ν a f u p).mp hmax)
        fun S hS hle ↦ hcrit S hS ?_
    rwa [maximalLifespanT_eq]

/-- The six-field Galilean mean reduction, transported. -/
theorem torusMeanReductionAPI : PeriodicMeanReductionAPI where
  mean_formula := fun ν hν a ha f hf T w t ht ↦
    NSFormalization.Section3.T11.mean_formula ν hν a ha f hf T (ofContract w) t ht
  mean_derivative := fun ν hν a ha f hf T w t ht ↦
    NSFormalization.Section3.T11.mean_derivative ν hν a ha f hf T
      (ofContract w) t ht
  transformed_solution := by
    intro ν hν a ha f hf T w
    obtain ⟨v, hv1, hv2, hv3⟩ :=
      NSFormalization.Section3.T11.transformed_solution ν hν a ha f hf T
        (ofContract w)
    exact ⟨toContract v, hv1, hv2, (periodicLocalRegularity_toContract v).mpr hv3⟩
  transformed_classes := fun ν hν a ha f hf T w ↦
    NSFormalization.Section3.T11.transformed_classes ν hν a ha f hf T
      (ofContract w)
  transformed_mean_zero := fun ν hν a ha f hf T w ↦
    NSFormalization.Section3.T11.transformed_mean_zero ν hν a ha f hf T
      (ofContract w)
  translation_preserves_sobolev :=
    NSFormalization.Section3.T11.translation_preserves_sobolev

/-- The four-field positive-viscosity rescaling, transported. -/
theorem torusViscosityRescalingAPI : PeriodicViscosityRescalingAPI where
  scaled_classes := NSFormalization.Section3.T11.scaled_classes
  inverse_identities := NSFormalization.Section3.T11.inverse_identities
  to_unit := by
    intro ν hν a ha f hf T w
    obtain ⟨v, hv1, hv2, hv3⟩ :=
      NSFormalization.Section3.T11.to_unit ν hν a ha f hf T (ofContract w)
    exact ⟨toContract v, hv1, hv2, (periodicLocalRegularity_toContract v).mpr hv3⟩
  from_unit := by
    intro ν hν a ha f hf T v
    obtain ⟨w, hw1, hw2, hw3⟩ :=
      NSFormalization.Section3.T11.from_unit ν hν a ha f hf T (ofContract v)
    exact ⟨toContract w, hw1, hw2, (periodicLocalRegularity_toContract w).mpr hw3⟩

/-- The contract's two named `H¹` predicates are the canonical ones; neither is
proved here or anywhere in the tree. -/
theorem periodicRestartH1_eq :
    PeriodicRestartH1 = NSFormalization.Section3.T11.PeriodicRestartH1 := by
  refine propext ⟨fun h ν hν f hf S hS K hK ↦ ?_, fun h ν hν f hf S hS K hK ↦ ?_⟩
  · obtain ⟨δ, hδ, hloc⟩ := h ν hν f hf S hS K hK
    refine ⟨δ, hδ, fun t₀ ht₀ a' ha' hK' ↦ ?_⟩
    obtain ⟨w, hw⟩ := hloc t₀ ht₀ a' ha' hK'
    exact ⟨ofContract w, (periodicLocalRegularity_eq w).mp hw⟩
  · obtain ⟨δ, hδ, hloc⟩ := h ν hν f hf S hS K hK
    refine ⟨δ, hδ, fun t₀ ht₀ a' ha' hK' ↦ ?_⟩
    obtain ⟨w, hw⟩ := hloc t₀ ht₀ a' ha' hK'
    exact ⟨toContract w, (periodicLocalRegularity_toContract w).mpr hw⟩

theorem periodicRestartBeyondH1_eq :
    PeriodicRestartBeyondH1 =
      NSFormalization.Section3.T11.PeriodicRestartBeyondH1 := by
  refine propext ⟨fun h ν hν f hf S hS K hK ↦ ?_, fun h ν hν f hf S hS K hK ↦ ?_⟩
  · obtain ⟨δ, hδ, hloc⟩ := h ν hν f hf S hS K hK
    refine ⟨δ, hδ, fun a ha u p hsolve hbound ↦ ?_⟩
    obtain ⟨v, hu, hp⟩ :=
      hloc a ha u p ((solvesBelowT_eq ν a f S u p).mpr hsolve) hbound
    exact ⟨ofContract v, hu, hp⟩
  · obtain ⟨δ, hδ, hloc⟩ := h ν hν f hf S hS K hK
    refine ⟨δ, hδ, fun a ha u p hsolve hbound ↦ ?_⟩
    obtain ⟨v, hu, hp⟩ :=
      hloc a ha u p ((solvesBelowT_eq ν a f S u p).mp hsolve) hbound
    exact ⟨toContract v, hu, hp⟩

/-- The manuscript continuation package follows from exactly the two named
`H¹` predicates, and from nothing weaker. -/
theorem torusContinuationAPI_of_h1 (h₁ : PeriodicRestartH1)
    (h₂ : PeriodicRestartBeyondH1) : PeriodicContinuationAPI where
  restart := h₁
  higherOrderBound := torusContinuationH3API.higherOrderBound
  restartBeyond := h₂
  extendsBeyond := torusContinuationH3API.extendsBeyond
  lifespanInfiniteOfLocallyFinite :=
    torusContinuationH3API.lifespanInfiniteOfLocallyFinite

end BlowupDensity.Bindings.TorusLocalTheory

namespace BlowupDensity.Bindings

/-- The registered local-theory API. -/
noncomputable def torusLocalTheoryAPI :
    Contracts.V1.TorusLocalTheory.PeriodicLocalTheoryAPI :=
  TorusLocalTheory.torusLocalTheoryAPI

/-- The registered `H³`-narrowed continuation API. -/
theorem torusContinuationH3API :
    Contracts.V1.TorusLocalTheory.PeriodicContinuationH3API :=
  TorusLocalTheory.torusContinuationH3API

/-- The registered Galilean mean-reduction API. -/
theorem torusMeanReductionAPI :
    Contracts.V1.TorusLocalTheory.PeriodicMeanReductionAPI :=
  TorusLocalTheory.torusMeanReductionAPI

/-- The registered positive-viscosity rescaling API. -/
theorem torusViscosityRescalingAPI :
    Contracts.V1.TorusLocalTheory.PeriodicViscosityRescalingAPI :=
  TorusLocalTheory.torusViscosityRescalingAPI

/-- The four registered APIs in one object. -/
noncomputable def torusLocalTheory :
    Contracts.V1.TorusLocalTheory.TorusLocalTheoryAPI where
  localTheory := torusLocalTheoryAPI
  continuation := torusContinuationH3API
  meanReduction := torusMeanReductionAPI
  viscosityRescaling := torusViscosityRescalingAPI

end BlowupDensity.Bindings
