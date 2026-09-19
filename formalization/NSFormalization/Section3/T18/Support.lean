import NSFormalization.Section3.T15.Placement
import NSFormalization.Section3.T17.CorrectionProfile
import NSFormalization.Section3.T18.Insertion

/-!
# T18 U7: support localization

The cutoff radius already bounds the packet placement set: `Kstar` lies in
the cutoff plateau, and the plateau lies in `ball 0 θRadius`.  Consequently it
is also a valid packet-carrier radius; no additional radius field is needed.

This module proves the radius, its positivity, the requested chart inclusion,
and the sharp `O(ε)` support bound for the correction slice.  Following the
lead ruling, `velocityDifference_support` takes the raw packet clause
`tsupport (packetVelocity (s,·)) ⊆ carrier` explicitly.  This is the exact
clause on the registered `PacketImportAPI`; U12 assembly supplies it while
constructing the Spec record.  It is intentionally not added to
`InsertionData`, on which other lanes already depend.
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

/-- The periodized scaled packet is supported in the periodic `O(ε)` ball.

The explicit raw support clause uses `data.carrier`, matching the registered
packet contract.  `PlacementData.carrier_subset` transports it to `Kstar`,
whose compactness is retained by the canonical placement record and is what
the T15/T16 support bridge consumes. -/
theorem periodizedScaledVelocity_support (data : InsertionData)
    (hsupp : ∀ s ∈ Ico (0 : ℝ) 1,
      tsupport (fun y : Space ↦ data.packetVelocity (s, y)) ⊆ data.carrier) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data), ∀ t ∈ Ico (0 : ℝ) data.place.T,
      tsupport (fun x : Space ↦ periodizedScaledVelocity data.packetVelocity
        data.place.x₀ data.place.T ε (t, x)) ⊆
          periodicSet (Metric.ball data.place.x₀ (ε * diffSupportRadius data)) := by
  intro ε hε t ht
  let C : Set Space := (fun y : Space ↦ data.place.x₀ + ε • y) '' data.place.Kstar
  have hpacket : ∀ s ∈ Ico (0 : ℝ) 1,
      tsupport (fun y : Space ↦ data.packetVelocity (s, y)) ⊆ data.place.Kstar := by
    intro s hs
    exact (hsupp s hs).trans data.place.carrier_subset
  have hscaled :
      tsupport (fun y : Space ↦ scaledVelocity data.packetVelocity data.place.x₀
        data.place.T ε (t, y)) ⊆ C :=
    scaledVelocity_tsupp_subset hε.1 data.place.Kstar_compact hpacket
      (subset_refl data.place.Kstar) ht.2
  have hCcompact : IsCompact C :=
    data.place.Kstar_compact.image (by fun_prop)
  have hCball : C ⊆ Metric.ball data.place.x₀
      (ε * diffSupportRadius data) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyball := packetCarrierRadius_spec data hy
    rw [diffSupportRadius_eq]
    rw [mem_ball, dist_eq_norm]
    have hynorm : ‖y‖ < data.D.θRadius := by
      simpa [mem_ball, packetCarrierRadius] using hyball
    simpa [norm_smul, abs_of_pos hε.1] using
      (mul_lt_mul_of_pos_left hynorm hε.1)
  let w : SpaceTimeField := fun z ↦
    scaledVelocity data.packetVelocity data.place.x₀ data.place.T ε (t, z.2)
  have hslice : ∀ (s : ℝ) (y : Space), w (s, y) ≠ 0 → y ∈ C := by
    intro s y hy
    exact hscaled (subset_tsupport _ hy)
  have hlift := latticeLift_sliceSupport_closed hCcompact hCball hslice 0
  have heq : (fun x : Space ↦ latticeLift w (0, x)) =
      (fun x : Space ↦ periodizedScaledVelocity data.packetVelocity
        data.place.x₀ data.place.T ε (t, x)) := by
    funext x
    rfl
  rw [heq] at hlift
  exact hlift.trans (periodicSet_mono hCball)

/-- `03-torus.tex:293-295`: the velocity difference is supported in integer
translates of one ball of radius `ε * diffSupportRadius data`.

The raw packet support hypothesis is explicit because the contract-free
`InsertionData` deliberately does not retain it.  Assembly from the registered
packet contract discharges it with `PacketImportAPI.velocity_support`. -/
theorem velocityDifference_support (data : InsertionData)
    (hsupp : ∀ s ∈ Ico (0 : ℝ) 1,
      tsupport (fun y : Space ↦ data.packetVelocity (s, y)) ⊆ data.carrier) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data), ∀ t ∈ Ico (0 : ℝ) data.place.T,
      tsupport (fun x : Space ↦ velocity data ε (t, x) -
        data.reference.velocity (t, x)) ⊆
          periodicSet (Metric.ball data.place.x₀
            (ε * diffSupportRadius data)) := by
  intro ε hε t ht
  have heq : (fun x : Space ↦ velocity data ε (t, x) -
      data.reference.velocity (t, x)) =
      (fun x : Space ↦ data.D.correction ε (t, x) +
        periodizedScaledVelocity data.packetVelocity data.place.x₀
          data.place.T ε (t, x)) := by
    funext x
    simp only [velocity]
    abel
  rw [heq]
  exact (tsupport_add _ _).trans (union_subset
    (correction_slice_support data ε hε t)
    (periodizedScaledVelocity_support data hsupp ε hε t ht))

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
