import NSFormalization.Section3.T18.Support
import NSFormalization.Section3.T18.Lifespan
import NSFormalization.Section3.T18.EnergyRate
import NSFormalization.Section3.T18.MixedRate
import NSFormalization.Section3.T18.SobolevRate

/-! The complete 45-field insertion family, assembled from U1–U11.
The three raw packet clauses erased by InsertionData remain explicit premises. -/
noncomputable section
namespace NSFormalization.Section3.T18
open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T11
open NSFormalization.Section3.T15 NSFormalization.Section3.T16 NSFormalization.Section3.T17
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open scoped ContDiff ENNReal

structure PeriodicInsertionAPI (data : InsertionData) where

  delta_pos : 0 < data.δ

  reference_force_mem : data.g ∈ forceClassT

  initial_mem : data.a ∈ initialClassT

  ε₀ : ℝ

  eps_pos : 0 < ε₀

  eps_le_scaling : ε₀ ≤ data.place.ε₀

  eps_le_cutoff : ε₀ ≤ data.D.ε₀

  velocity : ℝ → VelocityField

  pressure : ℝ → SpaceTimeScalar

  force : ℝ → VelocityField

  velocity_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    velocity ε z = data.reference.velocity z + data.D.correction ε z +
      periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε z

  pressure_formula : ∀ ε : ℝ,
    pressure ε = normalizePressureT
      (fun z => data.reference.pressure z +
        periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε z)

  force_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    force ε z = data.g z + correctionForce data.ν data.reference.velocity data.D ε z +
      periodizedScaledForce data.packetForce data.place.x₀ data.place.T ε z

  force_mem : ∀ ε ∈ Ioc (0 : ℝ) ε₀, force ε ∈ forceClassT

  forceDifference_mem : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    (fun z => force ε z - data.g z) ∈ forceClassT

  velocity_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ContDiffOn ℝ ∞ (velocity ε) (Ico (0 : ℝ) data.place.T ×ˢ (univ : Set Space))

  pressure_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ContDiffOn ℝ ∞ (pressure ε) (Ico (0 : ℝ) data.place.T ×ˢ (univ : Set Space))

  initial : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ x : Space, velocity ε (0, x) = data.a x

  incompressible : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) data.place.T, ∀ x : Space,
      spatialDivergence (velocity ε) t x = 0

  momentum : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ioo (0 : ℝ) data.place.T, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual data.ν (velocity ε) (pressure ε) t x = force ε (t, x)

  history : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ, 0 ≤ t →
    t ≤ data.place.T - 2 * ε ^ 2 → ∀ x : Space,
      velocity ε (t, x) = data.reference.velocity (t, x)

  velocity_periodic : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    IsPeriodicOn (Ico (0 : ℝ) data.place.T) (velocity ε)

  solution : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∃ w : ClassicalSolutionT data.ν data.a (force ε) data.place.T,
      w.velocity = velocity ε ∧ w.pressure = pressure ε

  maximal : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    IsMaximalPeriodicSolution data.ν data.a (force ε) (velocity ε) (pressure ε)

  lifespan : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    maximalLifespanT data.ν data.a (force ε) = ENNReal.ofReal data.place.T

  blowup : ∀ ε ∈ Ioc (0 : ℝ) ε₀, NSFormalization.Source.PacketScaling.SpeedUnboundedAt data.place.T (velocity ε)

  blowup_limsup : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    NSFormalization.Section4.A02.limsupLeft data.place.T
        (fun t => NSFormalization.Section4.A02.speedENorm
          (fun x : Space => velocity ε (t, x))) = ⊤

  crossTransport_background_advects_packet : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) data.place.T, ∀ x : Space,
      spatialDerivative
          (periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε) t x
          (correctedBackground data.reference.velocity data.D.correction ε (t, x)) = 0

  crossTransport_packet_advects_background : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) data.place.T, ∀ x : Space,
      spatialDerivative
          (correctedBackground data.reference.velocity data.D.correction ε) t x
          (periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε (t, x)) = 0

  velocityDifference_divFree : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) data.place.T, ∀ x : Space,
      spatialDivergence (fun z => velocity ε z - data.reference.velocity z) t x = 0

  diffSupportRadius : ℝ

  diffSupportRadius_pos : 0 < diffSupportRadius

  velocityDifference_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) data.place.T,
      tsupport (fun x : Space => velocity ε (t, x) - data.reference.velocity (t, x)) ⊆
        periodicSet (Metric.ball data.place.x₀ (ε * diffSupportRadius))

  diffSupport_in_chart : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Metric.ball data.place.x₀ (ε * diffSupportRadius) ⊆
      Metric.ball data.place.chartCenter data.place.chartRadius

  energyRate : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    energyENormT data.place.T (fun z => velocity ε z - data.reference.velocity z) ≤
      ENNReal.ofReal ((data.energyBound + data.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        data.correction.energyConst * ε ^ ((3 : ℝ) / 2))

  forceDiffMixedConst : ℝ≥0∞ → ℝ≥0∞ → ℝ

  forceDiffMixedConst_nonneg : ∀ (p q : ℝ≥0∞), 1 ≤ p → 1 ≤ q →
    0 ≤ forceDiffMixedConst p q

  forceDifference_mixed_memLp : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemMixedLebesgueT q p (fun z => force ε z - data.g z)

  forceDifference_mixed_bound : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      mixedLebesgueENormT q p (fun z => force ε z - data.g z) ≤
        ENNReal.ofReal (forceDiffMixedConst p q *
          (ε ^ (alphaT p q) +
            ε ^ (alphaT p q + 1)))

  forceDiffSobolevConst : ℝ → ℝ

  forceDiffSobolevConst_pos : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    0 < forceDiffSobolevConst s

  forceDifference_sobolev_memLp : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemForceSobolevT 1 s (fun z => force ε z - data.g z)

  forceDifference_sobolev_bound : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      forceSobolevENormT 1 s (fun z => force ε z - data.g z) ≤
        ENNReal.ofReal (forceDiffSobolevConst s *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s)))

  forceDifference_negativeSobolev_tendsto : ∀ s : ℝ, s < 0 →
    Tendsto (fun ε : ℝ => forceSobolevENormT 1 s (fun z => force ε z - data.g z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))

  negative_s_memLp : ∀ s : ℝ, s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemForceSobolevT 1 s (fun z => force ε z - data.g z)

/-- Exactly the raw support and sign clauses consumed by U7 and U9. -/
structure RawPremises (data : InsertionData) : Prop where
  hsupp : ∀ s ∈ Ico (0 : ℝ) 1,
    tsupport (fun y : Space ↦ data.packetVelocity (s, y)) ⊆ data.carrier
  hM : 0 ≤ data.energyBound
  hD : 0 ≤ data.dissipationBound

def assemble (data : InsertionData) (h : RawPremises data) : PeriodicInsertionAPI data where
  delta_pos := delta_pos data
  reference_force_mem := reference_force_mem data
  initial_mem := initial_mem data
  ε₀ := ε₀ data
  eps_pos := eps_pos data
  eps_le_scaling := eps_le_scaling data
  eps_le_cutoff := eps_le_cutoff data
  velocity := velocity data
  pressure := pressure data
  force := force data
  velocity_formula := velocity_formula data
  pressure_formula := pressure_formula data
  force_formula := force_formula data
  force_mem := force_mem data
  forceDifference_mem := forceDifference_mem data
  velocity_smooth := velocity_smooth data
  pressure_smooth := pressure_smooth data
  initial := initial data
  incompressible := incompressible data
  momentum := momentum data
  history := history data
  velocity_periodic := velocity_periodic data
  solution := solution data
  maximal := maximal data
  lifespan := lifespan data
  blowup := blowup data
  blowup_limsup := blowup_limsup data
  crossTransport_background_advects_packet := crossTransport_background_advects_packet data
  crossTransport_packet_advects_background := crossTransport_packet_advects_background data
  velocityDifference_divFree := velocityDifference_divFree data
  diffSupportRadius := diffSupportRadius data
  diffSupportRadius_pos := diffSupportRadius_pos data
  velocityDifference_support := velocityDifference_support data h.hsupp
  diffSupport_in_chart := diffSupport_in_chart data
  energyRate := energyRate data h.hM h.hD
  forceDiffMixedConst := forceDiffMixedConst data
  forceDiffMixedConst_nonneg := forceDiffMixedConst_nonneg data
  forceDifference_mixed_memLp := forceDifference_mixed_memLp data
  forceDifference_mixed_bound := forceDifference_mixed_bound data
  forceDiffSobolevConst := forceDiffSobolevConst data
  forceDiffSobolevConst_pos := forceDiffSobolevConst_pos data
  forceDifference_sobolev_memLp := forceDifference_sobolev_memLp data
  forceDifference_sobolev_bound := forceDifference_sobolev_bound data
  forceDifference_negativeSobolev_tendsto := forceDifference_negativeSobolev_tendsto data
  negative_s_memLp := negative_s_memLp data

/-- Quantification over the canonical raw packet fields and all threaded records. -/
def periodicInsertionStatement : Prop :=
  ∀ (ν : ℝ), 0 < ν →
  ∀ (u : VelocityField) (p : PressureField) (f : VelocityField) (K : Set Space)
    (M E : ℝ) (place : PlacementData u p f K)
    (scaling : ScalingAPI (ν := ν) u p f K M E place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction : CorrectionAPI ν place reference.velocity r δ D)
    (hδ : 0 < δ) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT),
    let data : InsertionData := ⟨ν,u,p,f,K,M,E,place,scaling,a,g,r,δ,D,reference,correction,hδ,hg,ha⟩
    RawPremises data → Nonempty (PeriodicInsertionAPI data)

theorem periodicInsertionStatement_holds : periodicInsertionStatement := by
  intro ν _ u p f K M E place scaling a g r δ D reference correction hδ hg ha data h
  exact ⟨assemble _ h⟩

/-- Staged non-vacuity: a full scaling/correction/reference witness is still
required from T15 U15 and T17 U12. T13 is already inhabited. -/
theorem nonvacuity_of_witnesses
    (h : ∃ data : InsertionData, RawPremises data) :
    Nonempty (Σ data : InsertionData, PeriodicInsertionAPI data) := by
  obtain ⟨data, hd⟩ := h
  exact ⟨⟨data, assemble data hd⟩⟩

end NSFormalization.Section3.T18
