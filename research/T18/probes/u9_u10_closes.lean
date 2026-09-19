import NSFormalization.Section3.T18.EnergyRate
import NSFormalization.Section3.T18.MixedRate
import Bindings.TorusLocalTheory
import Contracts.V1.PacketImport
import Contracts.V1.Correction

/-!
# T18 U9/U10 Spec-form conformance

The fieldwise U1 conversion below exposes the one difference between the
contract-facing Spec and canonical `InsertionData`: the contract packet still
carries `energy_isLUB` and `dissipation_eq`, from which its two real energy
constants are nonnegative.  These facts discharge the explicit raw premises
of the canonical `energyRate` theorem and close the exact Spec field.
-/

noncomputable section

namespace BlowupDensity.T18.U9U10ClosesProbe

open Set
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusLocalTheory
open NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section3.T17
open scoped ENNReal

namespace Spec

/-- The T15 Spec placement record in packet-projection form. -/
structure PlacementData {nu : ℝ} (P : PacketAPI nu) where
  T : ℝ
  time_pos : 0 < T
  chartCenter : Space
  chartRadius : ℝ
  chartRadius_pos : 0 < chartRadius
  chartBall_in_cube :
    closure (Metric.ball chartCenter chartRadius) ⊆
      interior NSFormalization.Section3.T13.fundamentalCube
  x₀ : Space
  x₀_mem : x₀ ∈ Metric.ball chartCenter chartRadius
  Kstar : Set Space
  Kstar_compact : IsCompact Kstar
  carrier_subset : P.carrier ⊆ Kstar
  force_projection_subset : ∀ t : ℝ, ∀ x : Space,
    (t, x) ∈ tsupport P.force → x ∈ Kstar
  ε₀ : ℝ
  eps_pos : 0 < ε₀
  eps_le_one : ε₀ ≤ 1
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < T
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ y ∈ Kstar,
    x₀ + ε • y ∈ Metric.ball chartCenter chartRadius

/-- The T16 Spec cutoff data. -/
structure CutoffData where
  θ : Space → ℝ
  η : ℝ → ℝ
  plateau : Set Space
  θRadius : ℝ
  ε₀ : ℝ
  potential : SpaceTimeField
  correction : ℝ → SpaceTimeField

def CutoffData.toCanonical (D : CutoffData) :
    NSFormalization.Section3.T16.CutoffData :=
  { θ := D.θ
    η := D.η
    plateau := D.plateau
    θRadius := D.θRadius
    ε₀ := D.ε₀
    potential := D.potential
    correction := D.correction }

/-- The exact five U9/U10 field types from `research/T18/Spec.lean`, after the
U1 data have been selected. -/
structure PeriodicInsertionU9U10Fields {nu : ℝ} (P : PacketImportAPI nu)
    (T : ℝ) (g v : SpaceTimeField) (ε₀ : ℝ)
    (velocity force : ℝ → VelocityField) (energyConst : ℝ) : Type where
  energyRate : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    energyENormT T (fun z => velocity ε z - v z) ≤
      ENNReal.ofReal ((P.energyBound + P.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        energyConst * ε ^ ((3 : ℝ) / 2))
  forceDiffMixedConst : ENNReal → ENNReal → ℝ
  forceDiffMixedConst_nonneg : ∀ (p q : ℝ≥0∞), 1 ≤ p → 1 ≤ q →
    0 ≤ forceDiffMixedConst p q
  forceDifference_mixed_memLp : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      NSFormalization.Section3.T15.MemMixedLebesgueT q p
        (fun z => force ε z - g z)
  forceDifference_mixed_bound : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      NSFormalization.Section3.T15.mixedLebesgueENormT q p
          (fun z => force ε z - g z) ≤
        ENNReal.ofReal (forceDiffMixedConst p q *
          (ε ^ (BlowupDensity.Contracts.V1.alpha p q) +
            ε ^ (BlowupDensity.Contracts.V1.alpha p q + 1)))

end Spec

/-- All seventeen placement fields converted to T15's raw-field record. -/
def placementOfSpec {nu : ℝ} {P : PacketAPI nu} (place : Spec.PlacementData P) :
    NSFormalization.Section3.T15.PlacementData
      P.velocity P.pressure P.force P.carrier :=
  { T := place.T
    time_pos := place.time_pos
    chartCenter := place.chartCenter
    chartRadius := place.chartRadius
    chartRadius_pos := place.chartRadius_pos
    chartBall_in_cube := place.chartBall_in_cube
    x₀ := place.x₀
    x₀_mem := place.x₀_mem
    Kstar := place.Kstar
    Kstar_compact := place.Kstar_compact
    carrier_subset := place.carrier_subset
    force_projection_subset := place.force_projection_subset
    ε₀ := place.ε₀
    eps_pos := place.eps_pos
    eps_le_one := place.eps_le_one
    eps_time := place.eps_time
    eps_space := place.eps_space }

def cutoffOfSpec (D : Spec.CutoffData) : NSFormalization.Section3.T16.CutoffData :=
  D.toCanonical

/-- Fieldwise U1 input conversion. -/
def ofSpecInputs {nu : ℝ} (P : PacketImportAPI nu)
    (place : Spec.PlacementData P.toPacketAPI)
    (scaling : ScalingAPI (ν := nu) P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound (placementOfSpec place))
    (a : SpatialField) (g : SpaceTimeField) (r delta : ℝ) (D : Spec.CutoffData)
    (reference : ClassicalSolutionT nu a g (place.T + delta))
    (correction : CorrectionAPI nu (placementOfSpec place) reference.velocity r delta
      (cutoffOfSpec D))
    (hdelta : 0 < delta) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT) :
    NSFormalization.Section3.T18.InsertionData :=
  { ν := nu
    packetVelocity := P.velocity
    packetPressure := P.pressure
    packetForce := P.force
    carrier := P.carrier
    energyBound := P.energyBound
    dissipationBound := P.dissipationBound
    place := placementOfSpec place
    scaling := scaling
    a := a
    g := g
    r := r
    δ := delta
    D := cutoffOfSpec D
    reference := BlowupDensity.Bindings.TorusLocalTheory.ofContract reference
    correction := correction
    hδ := hdelta
    hg := by
      simpa only [BlowupDensity.Bindings.TorusLocalTheory.forceClassT_eq] using hg
    ha := by
      simpa only [BlowupDensity.Bindings.TorusLocalTheory.initialClassT_eq] using ha }

/-- The Spec packet's least-upper-bound clause makes `M` nonnegative. -/
theorem packet_energyBound_nonneg {nu : ℝ} (P : PacketImportAPI nu) :
    0 ≤ P.energyBound := by
  have hmem : Real.sqrt (NavierStokesR3.CompactEnergy.l2Sq P.velocity 0) ∈
      (fun t : ℝ => Real.sqrt (NavierStokesR3.CompactEnergy.l2Sq P.velocity t)) ''
        Ico (0 : ℝ) 1 := ⟨0, ⟨le_rfl, zero_lt_one⟩, rfl⟩
  exact (Real.sqrt_nonneg _).trans (P.energy_isLUB.1 hmem)

/-- The Spec packet's exact dissipation formula makes `D` nonnegative. -/
theorem packet_dissipationBound_nonneg {nu : ℝ} (P : PacketImportAPI nu) :
    0 ≤ P.dissipationBound := by
  rw [P.dissipation_eq]
  exact Real.sqrt_nonneg _

/-- All exact Spec-form U9/U10 fields close from the canonical declarations
plus the two sign facts retained by `PacketImportAPI`. -/
def insertionU9U10OfCanonical {nu : ℝ} (P : PacketImportAPI nu)
    (place : Spec.PlacementData P.toPacketAPI)
    (scaling : ScalingAPI (ν := nu) P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound (placementOfSpec place))
    (a : SpatialField) (g : SpaceTimeField) (r delta : ℝ) (D : Spec.CutoffData)
    (reference : ClassicalSolutionT nu a g (place.T + delta))
    (correction : CorrectionAPI nu (placementOfSpec place) reference.velocity r delta
      (cutoffOfSpec D))
    (hdelta : 0 < delta) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT) :
    Spec.PeriodicInsertionU9U10Fields P place.T g reference.velocity
      (NSFormalization.Section3.T18.ε₀
        (ofSpecInputs P place scaling a g r delta D reference correction hdelta hg ha))
      (NSFormalization.Section3.T18.velocity
        (ofSpecInputs P place scaling a g r delta D reference correction hdelta hg ha))
      (NSFormalization.Section3.T18.force
        (ofSpecInputs P place scaling a g r delta D reference correction hdelta hg ha))
      correction.energyConst := by
  let data := ofSpecInputs P place scaling a g r delta D reference correction hdelta hg ha
  refine
    { energyRate := ?_
      forceDiffMixedConst := NSFormalization.Section3.T18.forceDiffMixedConst data
      forceDiffMixedConst_nonneg :=
        NSFormalization.Section3.T18.forceDiffMixedConst_nonneg data
      forceDifference_mixed_memLp :=
        NSFormalization.Section3.T18.forceDifference_mixed_memLp data
      forceDifference_mixed_bound := ?_ }
  · intro ε hε
    rw [BlowupDensity.Bindings.TorusLocalTheory.energyENormT_eq]
    exact NSFormalization.Section3.T18.energyRate data
      (packet_energyBound_nonneg P) (packet_dissipationBound_nonneg P) ε hε
  · intro p q _ hq ε hε
    change NSFormalization.Section3.T15.mixedLebesgueENormT q p
        (fun z => NSFormalization.Section3.T18.force data ε z - data.g z) ≤
      ENNReal.ofReal (NSFormalization.Section3.T18.forceDiffMixedConst data p q *
        (ε ^ (BlowupDensity.Contracts.V1.alpha p q) +
          ε ^ (BlowupDensity.Contracts.V1.alpha p q + 1)))
    simpa only [BlowupDensity.Contracts.V1.alpha,
      NSFormalization.Section3.T15.alphaT] using
      NSFormalization.Section3.T18.forceDifference_mixed_bound data p q hq ε hε

end BlowupDensity.T18.U9U10ClosesProbe
