import NSFormalization.Section3.T15.Placement
import Bindings.Packet

/-!
# T15 U2 non-vacuity / consumer probe — `PlacementData` on the selected packet

This probe instantiates the U2 placement lemmas from the **actual selected
source packet** `BlowupDensity.Bindings.packet ν hν : Contracts.V1.PacketAPI ν`
(`verification/Bindings/Packet.lean:104`), together with the geometric
`PlacementData` fields (`research/T15/Spec.lean:560-643`) as hypotheses over that
packet — building the full placement is unit U15, which is gated on
T13.localization and is not attempted here.

At the concrete admissible scale `ε = ε₀/2` it shows:
* the admissible interval `Ioc 0 ε₀` is nonempty (`ε₀/2 ∈ Ioc 0 ε₀`);
* the rescaled velocity slice lands in the affine image `x₀ + ε • K_*`
  (the main U2 theorem fires on the real packet's `velocity_support`);
* velocity, pressure and force slices are placed strictly inside
  `interior fundamentalCube`, using the packet's real `carrier_compact`,
  `velocity_support`, `pressure_support`, `force_support` clauses; and
* each relevant slice has compact support.

Since every conclusion is a derived support/placement fact (none is assumed),
and the admissible scale genuinely exists, the U2 API is non-vacuous on the
selected packet.  A concrete *nonzero* slice witness is supplied separately in
`research/T15/probes/rev376_nonvacuity.lean`.

Run: `cd verification && lake env lean ../research/T15/probes/placement_closes.lean`.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T13

/-- The U2 placement API instantiated on the selected packet at `ε = ε₀/2`. -/
theorem placement_closes
    (ν : ℝ) (hν : 0 < ν)
    (chartCenter x₀ : Space) (chartRadius ε₀ T : ℝ) (Kstar : Set Space)
    (_hchartRadius_pos : 0 < chartRadius)
    (hchartBall_in_cube :
      closure (Metric.ball chartCenter chartRadius) ⊆ interior fundamentalCube)
    (hKstar_compact : IsCompact Kstar)
    (hcarrier_subset : (BlowupDensity.Bindings.packet ν hν).carrier ⊆ Kstar)
    (hforce_proj : ∀ t : ℝ, ∀ x : Space,
      (t, x) ∈ tsupport (BlowupDensity.Bindings.packet ν hν).force → x ∈ Kstar)
    (hT : 0 < T) (hε₀_pos : 0 < ε₀) (_hε₀_le : ε₀ ≤ 1)
    (heps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ y ∈ Kstar,
      x₀ + ε • y ∈ Metric.ball chartCenter chartRadius) :
    (ε₀ / 2 ∈ Ioc (0 : ℝ) ε₀) ∧
    (tsupport (fun x : Space =>
        scaledVelocity (BlowupDensity.Bindings.packet ν hν).velocity x₀ T (ε₀ / 2) (0, x)) ⊆
      (fun y : Space => x₀ + (ε₀ / 2) • y) '' Kstar) ∧
    (tsupport (fun x : Space =>
        scaledVelocity (BlowupDensity.Bindings.packet ν hν).velocity x₀ T (ε₀ / 2) (0, x)) ⊆
      interior fundamentalCube) ∧
    (tsupport (fun x : Space =>
        scaledPressure (BlowupDensity.Bindings.packet ν hν).pressure x₀ T (ε₀ / 2) (0, x)) ⊆
      interior fundamentalCube) ∧
    (∀ t : ℝ, tsupport (fun x : Space =>
        scaledForce (BlowupDensity.Bindings.packet ν hν).force x₀ T (ε₀ / 2) (t, x)) ⊆
      interior fundamentalCube) ∧
    HasCompactSupport (fun x : Space =>
        scaledVelocity (BlowupDensity.Bindings.packet ν hν).velocity x₀ T (ε₀ / 2) (0, x)) ∧
    HasCompactSupport (fun x : Space =>
        scaledForce (BlowupDensity.Bindings.packet ν hν).force x₀ T (ε₀ / 2) (0, x)) := by
  set P := BlowupDensity.Bindings.packet ν hν with hP
  have hε_mem : ε₀ / 2 ∈ Ioc (0 : ℝ) ε₀ := ⟨by linarith, by linarith⟩
  have ht0 : (0 : ℝ) ∈ Ico (0 : ℝ) T := ⟨le_refl _, hT⟩
  refine ⟨hε_mem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact scaledVelocity_tsupp_subset hε_mem.1 P.carrier_compact P.velocity_support
      hcarrier_subset ht0
  · exact scaledVelocity_slice_subset_cube hε_mem P.carrier_compact P.velocity_support
      hcarrier_subset heps_space hchartBall_in_cube ht0
  · exact scaledPressure_slice_subset_cube hε_mem P.carrier_compact P.pressure_support
      hcarrier_subset heps_space hchartBall_in_cube ht0
  · exact fun t => scaledForce_slice_subset_cube hε_mem hKstar_compact P.force_support.1
      hforce_proj heps_space hchartBall_in_cube t
  · exact scaledVelocity_slice_hasCompactSupport hε_mem.1 P.carrier_compact P.velocity_support
      hcarrier_subset hKstar_compact ht0
  · exact scaledForce_slice_hasCompactSupport hε_mem.1 hKstar_compact P.force_support.1
      hforce_proj 0

end NSFormalization.Section3.T15
