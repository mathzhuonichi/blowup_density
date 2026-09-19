import NSFormalization.Section3.T15.Placement
import NSFormalization.Section3.T17.CorrectionProfile
import NSFormalization.Section3.T18.Insertion

/-!
# T18 U7: support localization

The cutoff radius already bounds the packet placement set: `Kstar` lies in
the cutoff plateau, and the plateau lies in `ball 0 θRadius`.  Consequently it
is also a valid packet-carrier radius; no additional radius field is needed.

This module proves the radius, its positivity, the requested chart inclusion,
and the sharp `O(ε)` support bound for the correction slice.  The packet half
of `velocityDifference_support` additionally needs the raw packet clause
`tsupport (packetVelocity (s,·)) ⊆ carrier` (or `Kstar`).  That clause is a
premise of `T15.scalingStatement`, but is not retained by either
`T15.ScalingAPI` or `T18.InsertionData`; see `research/T18/ATTEMPTS_U7.md`.
-/

noncomputable section

namespace NSFormalization.Section3.T18

open Set Filter Metric
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section3.T17
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Paper1.CorrectionProfile (physicalCorrection)
open NSFormalization.Source.PhysicalRemoval (physical_support)
open scoped Topology

/-- The cutoff ball is also the packet-carrier ball: the placement set lies
in the cutoff plateau, and the cutoff support lies in this ball. -/
def packetCarrierRadius (data : InsertionData) : ℝ := data.D.θRadius

/-- One radius controlling both the correction and packet copies. -/
def diffSupportRadius (data : InsertionData) : ℝ :=
  max data.D.θRadius (packetCarrierRadius data)

theorem packetCarrierRadius_spec (data : InsertionData) :
    data.place.Kstar ⊆ Metric.ball (0 : Space) (packetCarrierRadius data) := by
  exact data.correction.potential.prescribed_subset_plateau.trans
    (plateau_subset_ball data.correction.potential.theta_support
      data.correction.potential.theta_one)

theorem diffSupportRadius_eq (data : InsertionData) :
    diffSupportRadius data = data.D.θRadius := by
  simp [diffSupportRadius, packetCarrierRadius]

theorem diffSupportRadius_pos (data : InsertionData) :
    0 < diffSupportRadius data := by
  rw [diffSupportRadius_eq]
  exact data.correction.potential.theta_radius_pos

/-- A spatial-slice support point is a support point of the spacetime field at
the corresponding time. -/
theorem slice_tsupport_subset_spacetime_tsupport
    (F : SpaceTimeField) (t : ℝ) :
    tsupport (fun x : Space => F (t, x)) ⊆
      {x : Space | (t, x) ∈ tsupport F} := by
  intro x hx
  by_contra htx
  have hzero : F =ᶠ[𝓝 (t, x)] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp htx
  have hmap : Tendsto (fun y : Space => (t, y)) (𝓝 x) (𝓝 (t, x)) :=
    continuousAt_const.prodMk continuousAt_id
  exact (notMem_tsupport_iff_eventuallyEq.mpr (hmap.eventually hzero)) hx

/-- The correction slice has the sharp scaled support promised by its cutoff,
rather than only the coarser chart-radius bound stored in
`LocalPotentialAPI.correction_support_ball`. -/
theorem correction_slice_support (data : InsertionData) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data), ∀ t : ℝ,
      tsupport (fun x : Space => data.D.correction ε (t, x)) ⊆
        periodicSet (Metric.ball data.place.x₀
          (ε * diffSupportRadius data)) := by
  intro ε hε t x hx
  have hεD : ε ∈ Ioc (0 : ℝ) data.D.ε₀ :=
    ⟨hε.1, hε.2.trans (eps_le_cutoff data)⟩
  obtain ⟨k, hk⟩ := data.correction.potential.correction_support_ball ε hεD t hx
  have hshifted : x - latticeVector k ∈ tsupport (fun y : Space =>
      physicalCorrection data.reference.velocity data.place.x₀ data.place.T
        data.D.θ data.D.η ε (t, y)) := by
    by_contra hnot
    have hshift : Tendsto (fun y : Space => y - latticeVector k) (𝓝 x)
        (𝓝 (x - latticeVector k)) :=
      continuousAt_id.sub continuousAt_const
    have hball : ∀ᶠ y in 𝓝 x,
        y - latticeVector k ∈ Metric.ball data.place.x₀ data.r :=
      hshift.eventually (isOpen_ball.mem_nhds hk)
    have hphysicalZero :
        (fun y : Space => physicalCorrection data.reference.velocity
          data.place.x₀ data.place.T data.D.θ data.D.η ε (t, y))
            =ᶠ[𝓝 (x - latticeVector k)] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp hnot
    have hphysicalZero' := hshift.eventually hphysicalZero
    have hcorrectionZero :
        (fun y : Space => data.D.correction ε (t, y)) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hball, hphysicalZero'] with y hyball hyzero
      rw [← isPeriodicOn_sub_latticeVector
        (data.correction.potential.correction_periodic ε hεD) t y k]
      rw [correction_eq_physicalCorrection data.correction.potential hεD hyball]
      exact hyzero
    exact (notMem_tsupport_iff_eventuallyEq.mpr hcorrectionZero) hx
  refine ⟨k, ?_⟩
  have hspace := (physical_support hε.1 data.reference.velocity data.place.x₀
    data.place.T data.correction.potential.theta_compactSupport
    data.correction.potential.eta_compactSupport
    data.correction.potential.theta_support
    data.correction.potential.eta_support
    (slice_tsupport_subset_spacetime_tsupport
      (physicalCorrection data.reference.velocity data.place.x₀ data.place.T
        data.D.θ data.D.η ε) t hshifted)).2
  simpa [diffSupportRadius_eq] using hspace

/-- The scaled support ball is contained in the chosen placement chart. -/
theorem diffSupport_in_chart (data : InsertionData) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
      Metric.ball data.place.x₀ (ε * diffSupportRadius data) ⊆
        Metric.ball data.place.chartCenter data.place.chartRadius := by
  intro ε hε
  have hεD : ε ∈ Ioc (0 : ℝ) data.D.ε₀ :=
    ⟨hε.1, hε.2.trans (eps_le_cutoff data)⟩
  rw [diffSupportRadius_eq]
  exact (Metric.ball_subset_ball
    (data.correction.potential.eps_space ε hεD).le).trans
      data.correction.ball_in_chart

end NSFormalization.Section3.T18
