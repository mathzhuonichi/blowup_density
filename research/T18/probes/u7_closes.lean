import NSFormalization.Section3.T18.Support

/-!
Diagnostic U7 probe.

The target closes from the existing T15/T16 bridges once the raw packet
velocity-support clause is supplied.  The final example records the exact
residual premise which is present on `PacketImportAPI` in the Spec layer but
is not a projection of canonical `T18.InsertionData`.
-/

noncomputable section

namespace NSFormalization.Section3.T18.U7Probe

open Set Metric
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section3.T18
open NSFormalization.Section4.A02 (SpaceTimeField)

private theorem periodizedScaledVelocity_support
    (data : InsertionData)
    (hpacket : ∀ s ∈ Ico (0 : ℝ) 1,
      tsupport (fun y : Space => data.packetVelocity (s, y)) ⊆ data.place.Kstar) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data), ∀ t ∈ Ico (0 : ℝ) data.place.T,
      tsupport (fun x : Space => periodizedScaledVelocity data.packetVelocity
        data.place.x₀ data.place.T ε (t, x)) ⊆
          periodicSet (Metric.ball data.place.x₀ (ε * diffSupportRadius data)) := by
  intro ε hε t ht
  have hεplace : ε ∈ Ioc (0 : ℝ) data.place.ε₀ :=
    ⟨hε.1, hε.2.trans (eps_le_scaling data)⟩
  let C : Set Space := (fun y : Space => data.place.x₀ + ε • y) '' data.place.Kstar
  have hscaled :
      tsupport (fun y : Space => scaledVelocity data.packetVelocity data.place.x₀
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
  let w : SpaceTimeField := fun z =>
    scaledVelocity data.packetVelocity data.place.x₀ data.place.T ε (t, z.2)
  have hslice : ∀ (s : ℝ) (y : Space), w (s, y) ≠ 0 → y ∈ C := by
    intro s y hy
    exact hscaled (subset_tsupport _ hy)
  have hlift := latticeLift_sliceSupport_closed hCcompact hCball hslice 0
  have heq : (fun x : Space => latticeLift w (0, x)) =
      (fun x : Space => periodizedScaledVelocity data.packetVelocity
        data.place.x₀ data.place.T ε (t, x)) := by
    funext x
    rfl
  rw [heq] at hlift
  exact hlift.trans (periodicSet_mono hCball)

/-- Exact residual: this has the requested Spec field after projecting U1,
with only the packet clause omitted by `InsertionData` supplied explicitly. -/
example (data : InsertionData)
    (hpacket : ∀ s ∈ Ico (0 : ℝ) 1,
      tsupport (fun y : Space => data.packetVelocity (s, y)) ⊆ data.place.Kstar) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data), ∀ t ∈ Ico (0 : ℝ) data.place.T,
      tsupport (fun x : Space => velocity data ε (t, x) -
        data.reference.velocity (t, x)) ⊆
          periodicSet (Metric.ball data.place.x₀
            (ε * diffSupportRadius data)) := by
  intro ε hε t ht
  have heq : (fun x : Space => velocity data ε (t, x) -
      data.reference.velocity (t, x)) =
      (fun x : Space => data.D.correction ε (t, x) +
        periodizedScaledVelocity data.packetVelocity data.place.x₀
          data.place.T ε (t, x)) := by
    funext x
    simp only [velocity]
    abel
  rw [heq]
  exact (tsupport_add _ _).trans (union_subset
    (correction_slice_support data ε hε t)
    (periodizedScaledVelocity_support data hpacket ε hε t ht))

end NSFormalization.Section3.T18.U7Probe
