import NSFormalization.Section3.T15.Energy

-- Mutation: energy exponent 1/2 becomes 1; original proof unchanged.
noncomputable section

namespace NSFormalization.Section3.T15

open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NavierStokesR3.CompactEnergy (l2Sq dissipation)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section4.I02 (spatialGradient)
open NSFormalization.Source
open NSFormalization.Source.PacketScaling
open NavierStokes.PeriodicIntegration (Coords toSpace)
open scoped ContDiff ENNReal BigOperators Topology

theorem rev439_bad_energy
    {u f : VelocityField} {p : PressureField} {K : Set Space} {M D : ℝ}
    (hP : NSFormalization.Section4.I03.PacketData u K M D)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      energyEssSupT place.T
          (periodizedScaledVelocity u place.x₀ place.T ε) =
        ENNReal.ofReal (ε ^ (1 : ℝ) * M) := by
  intro ε hε
  have hT : 2 * ε ^ 2 < place.T := place.eps_time ε hε
  have key : essSup (fun t : ℝ => eLpNorm (torusLift
        (fun x : Space => periodizedScaledVelocity u place.x₀ place.T ε (t, x))) 2
        periodicTorusMeasure) (volume.restrict (Ioo (0 : ℝ) place.T))
      = essSup (fun t : ℝ => eLpNorm (fun x : Space =>
          Source.parabolicVelocity ε⁻¹ (place.T - ε ^ 2) place.x₀
            (zeroPastField u) (t, x)) 2 volume)
        (volume.restrict (Ioo (0 : ℝ) place.T)) := by
    refine essSup_congr_ae ?_
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioo (a := (0 : ℝ)) (b := place.T))] with t ht
    have hsupp : tsupport (fun x : Space => scaledVelocity u place.x₀ place.T ε (t, x))
        ⊆ interior fundamentalCube :=
      scaledVelocity_slice_subset_cube hε hP.carrier_compact hu place.carrier_subset
        place.eps_space place.chartBall_in_cube ht.2
    have hsm : ContDiff ℝ ∞ (fun x : Space => scaledVelocity u place.x₀ place.T ε (t, x)) :=
      scaledVelocity_slice_contDiff hP.extension_smooth hε.1 ht.2
    exact eLpNorm_torusLift_periodize
      (fun x : Space => scaledVelocity u place.x₀ place.T ε (t, x)) hsm hsupp
  show essSup (fun t : ℝ => eLpNorm (torusLift
      (fun x : Space => periodizedScaledVelocity u place.x₀ place.T ε (t, x))) 2
      periodicTorusMeasure) (volume.restrict (Ioo (0 : ℝ) place.T)) = _
  rw [key, NSFormalization.Section4.I03.energyEssSup_scaled_eq hP place.x₀ hε.1 hT,
    NSFormalization.Section4.I03.sqrt_mul_eq_rpow_half hε.1.le M]


end NSFormalization.Section3.T15
