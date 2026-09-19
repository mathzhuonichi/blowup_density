import NSFormalization.Section3.T18.SobolevRate
import Bindings.TorusLocalTheory
import Bindings.DatumLemmas
import Contracts.V1.PacketImport

/-!
# T18 U11 Spec-form conformance probe

The U1 placement, cutoff, and reference conversions are repeated here so the
probe is standalone.  The final structure consists of exactly the six U11
fields from `research/T18/Spec.lean:1926-1970`, in registered contract
vocabulary.
-/

noncomputable section

namespace BlowupDensity.T18.U11ClosesProbe

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
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

/-- Verbatim U11 honesty carrier from the reconciled T18 Spec. -/
def MemForceSobolevT (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → PeriodicSobolev s,
    IsPeriodicSobolevPath s f G ∧ MemLp G q forceTimeMeasure

/-- Exactly the six U11 field types in their Spec spelling. -/
structure PeriodicInsertionU11Fields (g : SpaceTimeField) (ε₀ : ℝ)
    (force : ℝ → VelocityField) : Type where
  forceDiffSobolevConst : ℝ → ℝ
  forceDiffSobolevConst_pos : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    0 < forceDiffSobolevConst s
  forceDifference_sobolev_memLp : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemForceSobolevT 1 s (fun z ↦ force ε z - g z)
  forceDifference_sobolev_bound : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      BlowupDensity.Contracts.V1.TorusLocalTheory.forceSobolevENormT
          1 s (fun z ↦ force ε z - g z) ≤
        ENNReal.ofReal (forceDiffSobolevConst s *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s)))
  forceDifference_negativeSobolev_tendsto : ∀ s : ℝ, s < 0 →
    Tendsto
      (fun ε : ℝ ↦
        BlowupDensity.Contracts.V1.TorusLocalTheory.forceSobolevENormT
          1 s (fun z ↦ force ε z - g z))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℝ≥0∞))
  negative_s_memLp : ∀ s : ℝ, s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemForceSobolevT 1 s (fun z ↦ force ε z - g z)

end Spec

/-- U1's complete placement conversion. -/
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

/-- U1's complete cutoff conversion. -/
def cutoffOfSpec (D : Spec.CutoffData) : NSFormalization.Section3.T16.CutoffData :=
  D.toCanonical

/-- The U1 fieldwise conversion of all Spec-threaded inputs. -/
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

/-- All six exact Spec-form U11 fields are supplied by the canonical module
after the U1 fieldwise conversions. -/
def insertionU11OfCanonical {nu : ℝ} (P : PacketImportAPI nu)
    (place : Spec.PlacementData P.toPacketAPI)
    (scaling : ScalingAPI (ν := nu) P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound (placementOfSpec place))
    (a : SpatialField) (g : SpaceTimeField) (r delta : ℝ) (D : Spec.CutoffData)
    (reference : ClassicalSolutionT nu a g (place.T + delta))
    (correction : CorrectionAPI nu (placementOfSpec place) reference.velocity r delta
      (cutoffOfSpec D))
    (hdelta : 0 < delta) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT) :
    let data := ofSpecInputs P place scaling a g r delta D reference correction hdelta hg ha
    Spec.PeriodicInsertionU11Fields g
      (NSFormalization.Section3.T18.ε₀ data)
      (NSFormalization.Section3.T18.force data) := by
  let data := ofSpecInputs P place scaling a g r delta D reference correction hdelta hg ha
  refine
    { forceDiffSobolevConst :=
        NSFormalization.Section3.T18.forceDiffSobolevConst data
      forceDiffSobolevConst_pos :=
        NSFormalization.Section3.T18.forceDiffSobolevConst_pos data
      forceDifference_sobolev_memLp := ?_
      forceDifference_sobolev_bound := ?_
      forceDifference_negativeSobolev_tendsto := ?_
      negative_s_memLp := ?_ }
  · intro s hs hsHalf ε hε
    obtain ⟨G, hG, hGLp⟩ :=
      NSFormalization.Section3.T18.forceDifference_sobolev_memLp
        data s hs hsHalf ε hε
    refine ⟨G, ?_, ?_⟩
    · exact (BlowupDensity.Bindings.TorusLocalTheory.isPeriodicSobolevPath_eq
        s (fun z ↦ NSFormalization.Section3.T18.force data ε z - data.g z) G).mpr hG
    · rw [← BlowupDensity.Bindings.datumLemmas_forceTimeMeasure_eq]
      exact hGLp
  · simpa only [data, ofSpecInputs,
      BlowupDensity.Bindings.TorusLocalTheory.forceSobolevENormT_eq] using
      NSFormalization.Section3.T18.forceDifference_sobolev_bound data
  · simpa only [data, ofSpecInputs,
      BlowupDensity.Bindings.TorusLocalTheory.forceSobolevENormT_eq] using
      NSFormalization.Section3.T18.forceDifference_negativeSobolev_tendsto data
  · intro s hs ε hε
    obtain ⟨G, hG, hGLp⟩ :=
      NSFormalization.Section3.T18.negative_s_memLp data s hs ε hε
    refine ⟨G, ?_, ?_⟩
    · exact (BlowupDensity.Bindings.TorusLocalTheory.isPeriodicSobolevPath_eq
        s (fun z ↦ NSFormalization.Section3.T18.force data ε z - data.g z) G).mpr hG
    · rw [← BlowupDensity.Bindings.datumLemmas_forceTimeMeasure_eq]
      exact hGLp

end BlowupDensity.T18.U11ClosesProbe
