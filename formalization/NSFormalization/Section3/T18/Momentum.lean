import NSFormalization.Section3.T18.CrossTransport

/-! T18 U6: the momentum equation of the inserted triple is exact.
The reference equation plus the definition of the correction force gives the
corrected background equation; adding the periodized packet equation produces
the inserted residual up to the two cross terms of U5.  Both the inserted
pressure and the packet's own pressure are normalized by a spatially constant
mean, which the Euclidean gradient does not see. -/

noncomputable section
namespace NSFormalization.Section3.T18
open Set
open scoped ContDiff
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section3.T17
open NSFormalization.Section4.A02 (SpaceTimeField SpaceTimeScalar SpatialField)

/-! ## Calculus helpers for the threaded slab regularity -/

/-- Smoothness of order two follows from infinite smoothness. -/
theorem contDiff_two_of_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Space → V} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 2 f :=
  hf.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))

/-- A spatial slice of a slab-smooth field is globally smooth in space, at the
closed time endpoint as well. -/
theorem slice_contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {u : SpaceTime → V} {T t : ℝ}
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space))) (ht : t ∈ Ico (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun y : Space ↦ u (t, y)) :=
  hu.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun y ↦ ⟨ht, mem_univ y⟩)

/-- Two spatial derivatives of a slab-smooth slice. -/
theorem slice_contDiff_two {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {u : SpaceTime → V} {T t : ℝ}
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space))) (ht : t ∈ Ico (0 : ℝ) T) :
    ContDiff ℝ 2 (fun y : Space ↦ u (t, y)) :=
  contDiff_two_of_smooth (slice_contDiff hu ht)

/-- Interior times of the slab are interior points of its domain, so the time
slice is differentiable there. -/
theorem slab_temporal_differentiable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {u : SpaceTime → V} {T t : ℝ}
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space))) (ht : t ∈ Ioo (0 : ℝ) T)
    (x : Space) : DifferentiableAt ℝ (fun s : ℝ ↦ u (s, x)) t := by
  have hsub : Ioo (0 : ℝ) T ×ˢ (univ : Set Space) ⊆ Ico (0 : ℝ) T ×ˢ (univ : Set Space) :=
    fun z hz ↦ ⟨⟨hz.1.1.le, hz.1.2⟩, hz.2⟩
  have hmem : Ioo (0 : ℝ) T ×ˢ (univ : Set Space) ∈ nhds (t, x) :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩
  have hcda : ContDiffAt ℝ ∞ u (t, x) := (hu.mono hsub).contDiffAt hmem
  exact (hcda.differentiableAt (by simp)).comp t
    (differentiableAt_id.prodMk (differentiableAt_const x))

/-- `02-preliminaries.tex:84-88`: the mean-zero gauge is a spatially constant
shift, so it leaves the Euclidean pressure gradient unchanged. -/
theorem pressureGradient_normalizePressureT (q : SpaceTimeScalar) (t : ℝ) (x : Space) :
    pressureGradient (normalizePressureT q) t x = pressureGradient q t x := by
  have h : (fun y : Space ↦ normalizePressureT q (t, y))
      = fun y : Space ↦ q (t, y) - pressureMeanT q t := rfl
  unfold pressureGradient
  simp only [h, fderiv_sub_const]

/-- Consequently the Navier–Stokes residual is insensitive to the gauge. -/
theorem residual_normalizePressureT (ν : ℝ) (u : VelocityField) (q : SpaceTimeScalar)
    (t : ℝ) (x : Space) :
    NSFormalization.Source.residual ν u (normalizePressureT q) t x =
      NSFormalization.Source.residual ν u q t x := by
  simp only [NSFormalization.Source.residual, pressureGradient_normalizePressureT]

/-! ## The momentum equation -/

/-- Presingular times are interior times of the reference horizon. -/
theorem reference_interior_time (data : InsertionData) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) data.place.T) : t ∈ Ioo (0 : ℝ) (data.place.T + data.δ) :=
  ⟨ht.1, by linarith [ht.2, data.hδ]⟩

/-- `03-torus.tex:319-321`: the corrected background solves the reference
equation with the correction force as its inhomogeneity. -/
theorem corrected_background_momentum (data : InsertionData) {ε : ℝ}
    (hε : ε ∈ Ioc (0 : ℝ) (ε₀ data)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) data.place.T) (x : Space) :
    NSFormalization.Source.residual data.ν
        (correctedBackground data.reference.velocity data.D.correction ε)
        data.reference.pressure t x =
      data.g (t, x) + correctionForce data.ν data.reference.velocity data.D ε (t, x) := by
  have hti := reference_interior_time data ht
  have htc : t ∈ Ico (0 : ℝ) (data.place.T + data.δ) := ⟨hti.1.le, hti.2⟩
  have hcsm := data.correction.potential.correction_smooth ε (correction_range data hε)
  have hvt := slab_temporal_differentiable data.reference.velocity_smooth hti x
  have hwt : DifferentiableAt ℝ (fun s : ℝ ↦ data.D.correction ε (s, x)) t :=
    ((hcsm.differentiable (by simp)).differentiableAt).comp t
      (differentiableAt_id.prodMk (differentiableAt_const x))
  have hv := slice_contDiff_two data.reference.velocity_smooth htc
  have hw : ContDiff ℝ 2 (fun y : Space ↦ data.D.correction ε (t, y)) :=
    contDiff_two_of_smooth (hcsm.comp (contDiff_const.prodMk contDiff_id))
  have hp : DifferentiableAt ℝ (fun y : Space ↦ data.reference.pressure (t, y)) x :=
    ((slice_contDiff data.reference.pressure_smooth htc).differentiable (by simp)) x
  have hbg := NSFormalization.Source.corrected_background data.ν data.reference.velocity
    (data.D.correction ε) data.reference.pressure t x hvt hwt hv hw hp
  have href : NSFormalization.Source.residual data.ν data.reference.velocity
      data.reference.pressure t x = data.g (t, x) := data.reference.momentum t hti x
  rw [show correctedBackground data.reference.velocity data.D.correction ε
      = fun z ↦ data.reference.velocity z + data.D.correction ε z from rfl, hbg, href,
    correctionForce_eq_source]

/-- `research/T18/Spec.lean:1774`: `eq:NS` holds exactly for the inserted
triple at every interior time. -/
theorem momentum (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    ∀ t ∈ Ioo (0 : ℝ) data.place.T, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual data.ν
        (velocity data ε) (pressure data ε) t x = force data ε (t, x) := by
  intro ε hε t ht x
  obtain ⟨S, hSv, hSp⟩ := data.scaling.solution ε (scaling_range data hε)
  have htc : t ∈ Ico (0 : ℝ) data.place.T := ⟨ht.1.le, ht.2⟩
  have hti := reference_interior_time data ht
  have htcr : t ∈ Ico (0 : ℝ) (data.place.T + data.δ) := ⟨hti.1.le, hti.2⟩
  have hcsm := data.correction.potential.correction_smooth ε (correction_range data hε)
  -- regularity of the corrected background
  have hbt : DifferentiableAt ℝ (fun s : ℝ ↦
      correctedBackground data.reference.velocity data.D.correction ε (s, x)) t := by
    have hvt := slab_temporal_differentiable data.reference.velocity_smooth hti x
    have hwt : DifferentiableAt ℝ (fun s : ℝ ↦ data.D.correction ε (s, x)) t :=
      ((hcsm.differentiable (by simp)).differentiableAt).comp t
        (differentiableAt_id.prodMk (differentiableAt_const x))
    exact hvt.add hwt
  have hb : ContDiff ℝ 2 (fun y : Space ↦
      correctedBackground data.reference.velocity data.D.correction ε (t, y)) := by
    have hv := slice_contDiff_two data.reference.velocity_smooth htcr
    have hw : ContDiff ℝ 2 (fun y : Space ↦ data.D.correction ε (t, y)) :=
      contDiff_two_of_smooth (hcsm.comp (contDiff_const.prodMk contDiff_id))
    exact hv.add hw
  -- regularity of the periodized packet, transported through the scaling record
  have hUsm : ContDiffOn ℝ ∞
      (periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε)
      (Ico (0 : ℝ) data.place.T ×ˢ (univ : Set Space)) := hSv ▸ S.velocity_smooth
  have hUt := slab_temporal_differentiable hUsm ht x
  have hU := slice_contDiff_two hUsm htc
  -- regularity of the two pressures
  have hp : DifferentiableAt ℝ (fun y : Space ↦ data.reference.pressure (t, y)) x :=
    ((slice_contDiff data.reference.pressure_smooth htcr).differentiable (by simp)) x
  have hPeq : (fun y : Space ↦
      periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε (t, y))
      = fun y : Space ↦ S.pressure (t, y) +
        pressureMeanT (periodizedScaledPressure data.packetPressure data.place.x₀
          data.place.T ε) t := by
    funext y
    rw [hSp]
    simp [normalizedScaledPressure, normalizePressureT]
  have hP : DifferentiableAt ℝ (fun y : Space ↦
      periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε (t, y)) x := by
    rw [hPeq]
    exact (((slice_contDiff S.pressure_smooth htc).differentiable (by simp)) x).add_const _
  -- the packet's own momentum equation, in the raw pressure gauge
  have hpacket : NSFormalization.Source.residual data.ν
      (periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε)
      (periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε) t x =
      periodizedScaledForce data.packetForce data.place.x₀ data.place.T ε (t, x) := by
    have h := S.momentum t ht x
    rw [hSv, hSp] at h
    rw [← residual_normalizePressureT data.ν
      (periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε)
      (periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε) t x]
    exact h
  -- expand the residual of the sum
  have hsplit := NSFormalization.Source.residual_add data.ν
    (correctedBackground data.reference.velocity data.D.correction ε)
    (periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε)
    data.reference.pressure
    (periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε)
    t x hbt hUt hb hU hp hP
  have hgoal : NavierStokesR3.ProblemStatement.navierStokesResidual data.ν
      (velocity data ε) (pressure data ε) t x =
      NSFormalization.Source.residual data.ν
        (fun z ↦ correctedBackground data.reference.velocity data.D.correction ε z +
          periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε z)
        (fun z ↦ data.reference.pressure z +
          periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε z) t x := by
    show NSFormalization.Source.residual data.ν
        (fun z ↦ correctedBackground data.reference.velocity data.D.correction ε z +
          periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε z)
        (normalizePressureT (fun z ↦ data.reference.pressure z +
          periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε z)) t x = _
    exact residual_normalizePressureT data.ν _ _ t x
  rw [hgoal, hsplit, corrected_background_momentum data hε ht x, hpacket,
    crossTransport_packet_advects_background data ε hε t htc x,
    crossTransport_background_advects_packet data ε hε t htc x]
  simp only [force]
  abel

end NSFormalization.Section3.T18
