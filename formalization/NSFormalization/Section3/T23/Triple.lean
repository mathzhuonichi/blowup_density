import NSFormalization.Section3.T23.PressureNormalization
import NavierStokes.ResidualStability

/-! The actual un-periodized triple. Supplier facts are threaded at the same
raw packet, correction, center and horizon; no replacement insertion record. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T15 (scaledVelocity scaledPressure scaledForce)
open scoped ContDiff

/-- Addition uses the intersection of the two genuine open neighborhoods. -/
theorem SmoothOnClosedSlab.add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Set ℝ} {Ω : Set Space} {f g : SpaceTime → E}
    (hf : SmoothOnClosedSlab I Ω f) (hg : SmoothOnClosedSlab I Ω g) :
    SmoothOnClosedSlab I Ω (fun z => f z + g z) := by
  obtain ⟨N, hN, hn, hf⟩ := hf
  obtain ⟨M, hM, hm, hg⟩ := hg
  exact ⟨N ∩ M, hN.inter hM, fun z hz => ⟨hn hz, hm hz⟩,
    (hf.mono inter_subset_left).add (hg.mono inter_subset_right)⟩

/-- Shrinking the time interval preserves the same neighborhood. -/
theorem SmoothOnClosedSlab.mono_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I J : Set ℝ} {Ω : Set Space} {f : SpaceTime → E}
    (hf : SmoothOnClosedSlab I Ω f) (hJI : J ⊆ I) : SmoothOnClosedSlab J Ω f := by
  obtain ⟨N, hN, hn, hf⟩ := hf
  exact ⟨N, hN, fun z hz => hn ⟨hJI hz.1, hz.2⟩, hf⟩

/-- Globally smooth summands satisfy every domain slab convention. -/
theorem smoothOnClosedSlab_of_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : SpaceTime → E} (hf : ContDiff ℝ ∞ f) (I : Set ℝ) (Ω : Set Space) :
    SmoothOnClosedSlab I Ω f := ⟨univ, isOpen_univ, subset_univ _, hf.contDiffOn⟩

/-- Compact positive temporal supports combine by finite union. -/
theorem MemForceOmega.add {Ω : Set Space} {f g : SpaceTimeField}
    (hf : MemForceOmega Ω f) (hg : MemForceOmega Ω g) :
    MemForceOmega Ω (fun z => f z + g z) := by
  obtain ⟨hfs, K, hK, hKpos, hfK⟩ := hf
  obtain ⟨hgs, L, hL, hLpos, hgL⟩ := hg
  refine ⟨fun T => (hfs T).add (hgs T), K ∪ L, hK.union hL,
    union_subset hKpos hLpos, ?_⟩
  intro z hz
  rcases tsupport_add f g hz with hz | hz
  · exact ⟨Or.inl (hfK hz).1, mem_univ _⟩
  · exact ⟨Or.inr (hgL hz).1, mem_univ _⟩

/-- Whole-spacetime compact positive support yields the domain force class. -/
theorem memForceOmega_of_compactPositiveTimeSupport {Ω : Set Space} {f : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f)
    (hs : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f) :
    MemForceOmega Ω f := by
  refine ⟨fun T => smoothOnClosedSlab_of_contDiff hf _ _,
    Prod.fst '' tsupport f, hs.1.isCompact.image continuous_fst, ?_, ?_⟩
  · rintro t ⟨z, hz, rfl⟩
    exact (hs.2 hz).1
  · intro z hz
    exact ⟨⟨z, hz, rfl⟩, mem_univ _⟩

/-- Local residual addition with viscosity; all calculus stays on one open set. -/
theorem domain_residual_add {N : Set SpaceTime} (hN : IsOpen N)
    {v w : VelocityField} {p q : PressureField}
    (hv : ContDiffOn ℝ ∞ v N) (hw : ContDiffOn ℝ ∞ w N)
    (hp : ContDiffOn ℝ ∞ p N) (hq : ContDiffOn ℝ ∞ q N)
    (ν : ℝ) {z : SpaceTime} (hz : z ∈ N) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν
      (fun y => v y + w y) (fun y => p y + q y) z.1 z.2 =
    NavierStokesR3.ProblemStatement.navierStokesResidual ν v p z.1 z.2 +
    NavierStokesR3.ProblemStatement.navierStokesResidual ν w q z.1 z.2 +
      spatialDerivative v z.1 z.2 (w z) + spatialDerivative w z.1 z.2 (v z) := by
  unfold NavierStokesR3.ProblemStatement.navierStokesResidual
  rw [ResidualCalculus.temporalDerivative_add v w z.1 z.2
      (ResidualStability.timeSlice_differentiable hN hv hz)
      (ResidualStability.timeSlice_differentiable hN hw hz),
    ResidualCalculus.advection_add v w z.1 z.2
      (ResidualStability.spatialSlice_differentiable hN hv hz)
      (ResidualStability.spatialSlice_differentiable hN hw hz),
    ResidualStability.spatialLaplacian_add_on hN hv hw hz,
    ResidualCalculus.pressureGradient_add p q z.1 z.2
      (ResidualStability.spatialSlice_differentiable hN hp hz)
      (ResidualStability.spatialSlice_differentiable hN hq hz), smul_add]
  abel

namespace InsertedTriple
variable {ν δ r : ℝ} {Ω K : Set Space} {a : SpatialField} {g : SpaceTimeField}
  {u f : VelocityField} {p : PressureField}
  (place : DomainPlacementData u p f K) (D : CutoffData)
  (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))

/-- One threshold retains placement, correction, I03, and further geometric bounds. -/
def threshold (scalingBound geometryBound : ℝ) : ℝ :=
  min (min place.ε₀ D.ε₀) (min scalingBound geometryBound)

def velocity (ε : ℝ) : VelocityField := fun z =>
  reference.velocity z + D.correction ε z + scaledVelocity u place.x₀ place.T ε z

def pressure (ε : ℝ) : SpaceTimeScalar := domainNormalizePressure Ω
  (fun z => reference.pressure z + scaledPressure p place.x₀ place.T ε z)

def force (ε : ℝ) : VelocityField := fun z =>
  g z + correctionForce ν reference.velocity D ε z + scaledForce f place.x₀ place.T ε z

theorem velocity_formula (ε : ℝ) (z : SpaceTime) :
    velocity place D reference ε z = reference.velocity z + D.correction ε z +
      scaledVelocity u place.x₀ place.T ε z := rfl

theorem pressure_formula (ε : ℝ) :
    pressure place reference ε = domainNormalizePressure Ω
      (fun z => reference.pressure z + scaledPressure p place.x₀ place.T ε z) := rfl

theorem force_formula (ε : ℝ) (z : SpaceTime) :
    force place D reference ε z = g z + correctionForce ν reference.velocity D ε z +
      scaledForce f place.x₀ place.T ε z := rfl

theorem eps_pos {s b : ℝ} (hD : 0 < D.ε₀) (hs : 0 < s) (hb : 0 < b) :
    0 < threshold place D s b := lt_min (lt_min place.eps_pos hD) (lt_min hs hb)

theorem eps_le_scaling (s b : ℝ) : threshold place D s b ≤ place.ε₀ :=
  (min_le_left _ _).trans (min_le_left _ _)

theorem eps_le_cutoff (s b : ℝ) : threshold place D s b ≤ D.ε₀ :=
  (min_le_left _ _).trans (min_le_right _ _)

theorem eps_le_supplier (s b : ℝ) : threshold place D s b ≤ s :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem eps_le_geometry (s b : ℝ) : threshold place D s b ≤ b :=
  (min_le_right _ _).trans (min_le_right _ _)

variable {place D reference}

/-- The raw zero-past packet regularity transports to the full open presingular slab. -/
theorem packet_velocity_smooth
    (hu : ContDiffOn ℝ ∞ (NSFormalization.Source.PacketScaling.zeroPastField u)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space))) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (scaledVelocity u place.x₀ place.T ε)
      (Iio place.T ×ˢ (univ : Set Space)) := by
  have h := NSFormalization.Source.PacketScaling.dilate_smoothOn ε⁻¹
    (inv_pos.mpr hε) (place.T - ε ^ 2) place.x₀ hu
  have he : (place.T - ε ^ 2) + ((ε⁻¹) ^ 2)⁻¹ = place.T := by
    simp only [inv_pow, inv_inv, sub_add_cancel]
  rw [he] at h
  exact h

/-- The same affine transport applies to the scalar packet pressure. -/
theorem packet_pressure_smooth
    (hp : ContDiffOn ℝ ∞ (NSFormalization.Source.PacketScaling.zeroPastField p)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space))) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (scaledPressure p place.x₀ place.T ε)
      (Iio place.T ×ˢ (univ : Set Space)) := by
  have h := NSFormalization.Source.PacketScaling.dilate_smoothOn ((ε⁻¹) ^ 2)
    (inv_pos.mpr hε) (place.T - ε ^ 2) place.x₀ hp
  have he : (place.T - ε ^ 2) + ((ε⁻¹) ^ 2)⁻¹ = place.T := by
    simp only [inv_pow, inv_inv, sub_add_cancel]
  rw [he] at h
  exact h

/-- Quiet history is global, including its closed right endpoint. -/
theorem history (C : WindowedCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
    {ε : ℝ} (hε : ε ∈ Ioc 0 D.ε₀) {t : ℝ}
    (ht : t ≤ place.T - 2 * ε ^ 2) (x : Space) :
    velocity place D reference ε (t, x) = reference.velocity (t, x) := by
  have hw : D.correction ε (t, x) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hz => (not_lt_of_ge ht) (C.correction_support ε hε hz).1.1)
  have hU := congrFun (packet_slice_zero u place.x₀ place.T ε t
    (by nlinarith [sq_nonneg ε])) x
  simp only [velocity, hw, hU, add_zero]

/-- The initial datum follows from quiet history and the placement time bound. -/
theorem initial (C : WindowedCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
    {ε : ℝ} (hε : ε ∈ Ioc 0 D.ε₀) (hplace : ε ∈ Ioc 0 place.ε₀)
    {x : Space} (hx : x ∈ Ω) : velocity place D reference ε (0, x) = a x := by
  rw [history C hε (by linarith [place.eps_time ε hplace]) x]
  exact reference.initial x hx

/-- Restrict the reference horizon, then add the smooth correction and packet. -/
theorem velocity_smooth (hδ : 0 < δ)
    (C : WindowedCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
    {ε : ℝ} (hε : ε ∈ Ioc 0 D.ε₀)
    (hU : ContDiffOn ℝ ∞ (scaledVelocity u place.x₀ place.T ε)
      (Iio place.T ×ˢ (univ : Set Space))) :
    SmoothOnClosedSlab (Ico 0 place.T) Ω (velocity place D reference ε) := by
  exact ((reference.velocity_smooth.mono_time
    (fun t ht => ⟨ht.1, by linarith [ht.2]⟩)).add
      (smoothOnClosedSlab_of_contDiff (C.correction_smooth ε hε) _ _)).add
    ⟨_, isOpen_Iio.prod isOpen_univ, fun z hz => ⟨hz.1.2, mem_univ _⟩, hU⟩

/-- The pressure is smooth with the domain-average gauge. -/
theorem pressure_smooth (hδ : 0 < δ) (hb : Bornology.IsBounded Ω) (hm : MeasurableSet Ω)
    {ε : ℝ} (hP : ContDiffOn ℝ ∞ (scaledPressure p place.x₀ place.T ε)
      (Iio place.T ×ˢ (univ : Set Space))) :
    SmoothOnClosedSlab (Ico 0 place.T) Ω (pressure place reference ε) := by
  exact ((reference.pressure_smooth.mono_time
    (fun t ht => ⟨ht.1, by linarith [ht.2]⟩)).add
    ⟨_, isOpen_Iio.prod isOpen_univ, fun z hz => ⟨hz.1.2, mem_univ _⟩, hP⟩).domainNormalizePressure hb hm

/-- The actual correction force is smooth and has compact positive temporal support. -/
theorem correction_force_mem
    (C : WindowedCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
    (hball : Metric.ball place.x₀ r ⊆ Ω)
    {ε : ℝ} (hε : ε ∈ Ioc 0 D.ε₀) :
    MemForceOmega Ω (correctionForce ν reference.velocity D ε) := by
  have href : ContDiffOn ℝ ∞ reference.velocity
      (Ioo 0 (place.T + δ) ×ˢ Metric.ball place.x₀ r) :=
    fun z hz => (reference.velocity_smooth.contDiffAt
      ⟨⟨hz.1.1.le, hz.1.2⟩, subset_closure (hball hz.2)⟩).contDiffWithinAt
  have hs := force_smooth_of_local ν reference.velocity D ε
    (isOpen_Ioo.prod Metric.isOpen_ball) href (C.correction_smooth ε hε)
    (C.correction_support_interior hε)
  refine ⟨fun T => smoothOnClosedSlab_of_contDiff hs _ _,
    Icc (place.T - 2 * ε ^ 2) (place.T + 2 * ε ^ 2), isCompact_Icc, ?_, ?_⟩
  · intro t ht
    have htime := (lt_min_iff.mp (C.eps_time ε hε)).1
    change 0 < t
    linarith [ht.1]
  · intro z hz
    have h := C.correction_support ε hε (force_support ν reference.velocity D ε hz)
    exact ⟨⟨h.1.1.le, h.1.2.le⟩, mem_univ _⟩

/-- The packet force remains in the domain force class after the positive delay. -/
theorem packet_force_mem (hf : ContDiff ℝ ∞ f)
    (hs : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    {ε : ℝ} (hε : ε ∈ Ioc 0 place.ε₀) :
    MemForceOmega Ω (scaledForce f place.x₀ place.T ε) := by
  apply memForceOmega_of_compactPositiveTimeSupport
    (NSFormalization.Source.PacketScaling.parabolicForce_smooth hf _ _ _)
  exact NSFormalization.Source.PacketScaling.parabolicForce_positive_support hs
    (inv_pos.mpr hε.1) (by change 0 ≤ place.T - ε ^ 2; nlinarith [place.eps_time ε hε, sq_nonneg ε]) _

theorem force_mem
    (C : WindowedCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
    (hball : Metric.ball place.x₀ r ⊆ Ω) (hg : g ∈ forceClassOmega Ω)
    (hf : ContDiff ℝ ∞ f) (hs : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    {ε : ℝ} (hε : ε ∈ Ioc 0 D.ε₀) (hplace : ε ∈ Ioc 0 place.ε₀) :
    force place D reference ε ∈ forceClassOmega Ω :=
  (hg.add (correction_force_mem C hball hε)).add (packet_force_mem hf hs hplace)

theorem forceDifference_mem
    (C : WindowedCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
    (hball : Metric.ball place.x₀ r ⊆ Ω)
    (hf : ContDiff ℝ ∞ f) (hs : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    {ε : ℝ} (hε : ε ∈ Ioc 0 D.ε₀) (hplace : ε ∈ Ioc 0 place.ε₀) :
    (fun z => force place D reference ε z - g z) ∈ forceClassOmega Ω := by
  have he : (fun z => force place D reference ε z - g z) =
      (fun z => correctionForce ν reference.velocity D ε z + scaledForce f place.x₀ place.T ε z) := by
    funext z
    simp only [force]
    abel
  rw [he]
  exact (correction_force_mem C hball hε).add (packet_force_mem hf hs hplace)

/-- Incompressibility is the sum of the three physical divergences in Ω. -/
theorem incompressible (hδ : 0 < δ)
    (C : WindowedCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
    {ε : ℝ} (hε : ε ∈ Ioc 0 D.ε₀)
    (hU : ContDiffOn ℝ ∞ (scaledVelocity u place.x₀ place.T ε)
      (Iio place.T ×ˢ (univ : Set Space)))
    (hdiv : ∀ t : ℝ, t < place.T → ∀ x : Space,
      spatialDivergence (scaledVelocity u place.x₀ place.T ε) t x = 0)
    {t : ℝ} (ht : t ∈ Ico 0 place.T) {x : Space} (hx : x ∈ Ω) :
    spatialDivergence (velocity place D reference ε) t x = 0 := by
  have htr : t ∈ Ico 0 (place.T + δ) := ⟨ht.1, by linarith [ht.2]⟩
  have hv := (reference.velocity_smooth.contDiffAt_slice htr (subset_closure hx)).differentiableAt (by simp)
  have hw := ((C.correction_smooth ε hε).comp ((contDiff_const (c := t)).prodMk contDiff_id)).differentiable (by simp) x
  have hUs := ResidualStability.spatialSlice_differentiable (isOpen_Iio.prod isOpen_univ)
    hU (show (t, x) ∈ Iio place.T ×ˢ (univ : Set Space) from ⟨ht.2, mem_univ _⟩)
  change spatialDivergence (fun z => reference.velocity z + D.correction ε z +
    scaledVelocity u place.x₀ place.T ε z) t x = 0
  rw [ResidualCalculus.spatialDivergence_add _ _ t x (hv.add hw) hUs,
    ResidualCalculus.spatialDivergence_add _ _ t x hv hw,
    reference.divergence t htr x hx, C.correction_divergence_free ε hε t x, hdiv t ht.2 x]
  simp

/-- The corrected background equation, computed using only local smoothness. -/
theorem corrected_background_momentum (hδ : 0 < δ)
    (C : WindowedCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
    {ε : ℝ} (hε : ε ∈ Ioc 0 D.ε₀)
    {t : ℝ} (ht : t ∈ Ioo 0 place.T) {x : Space} (hx : x ∈ Ω) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν
      (fun z => reference.velocity z + D.correction ε z) reference.pressure t x =
      g (t, x) + correctionForce ν reference.velocity D ε (t, x) := by
  have htr : t ∈ Ico 0 (place.T + δ) := ⟨ht.1.le, by linarith [ht.2]⟩
  obtain ⟨N, hN, hn, hv⟩ := reference.velocity_smooth
  have hz : (t, x) ∈ N := hn ⟨htr, subset_closure hx⟩
  have hw := (C.correction_smooth ε hε).contDiffOn (s := N)
  have hvt := ResidualStability.timeSlice_differentiable hN hv hz
  have hwt := ResidualStability.timeSlice_differentiable hN hw hz
  have hvs := ResidualStability.spatialSlice_differentiable hN hv hz
  have hws := ResidualStability.spatialSlice_differentiable hN hw hz
  have hr := reference.momentum t ⟨ht.1, htr.2⟩ x hx
  unfold NavierStokesR3.ProblemStatement.navierStokesResidual at hr ⊢
  rw [ResidualCalculus.temporalDerivative_add _ _ t x hvt hwt,
    ResidualCalculus.advection_add _ _ t x hvs hws,
    ResidualStability.spatialLaplacian_add_on hN hv hw hz, smul_add]
  unfold correctionForce
  rw [← hr]
  abel

/-- The exact inserted momentum equation: local residual addition, U2 cross
cancellation and the same-scale I03 packet equation, followed by gauge invariance. -/
theorem momentum (hδ : 0 < δ)
    (C : WindowedCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
    {ε : ℝ} (hε : ε ∈ Ioc 0 D.ε₀)
    (hU : ContDiffOn ℝ ∞ (scaledVelocity u place.x₀ place.T ε)
      (Iio place.T ×ˢ (univ : Set Space)))
    (hP : ContDiffOn ℝ ∞ (scaledPressure p place.x₀ place.T ε)
      (Iio place.T ×ˢ (univ : Set Space)))
    (heq : ∀ t : ℝ, t < place.T → ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (scaledVelocity u place.x₀ place.T ε) (scaledPressure p place.x₀ place.T ε) t x =
        scaledForce f place.x₀ place.T ε (t, x))
    {t : ℝ} (ht : t ∈ Ioo 0 place.T) {x : Space} (hx : x ∈ Ω) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν
      (velocity place D reference ε) (pressure place reference ε) t x =
      force place D reference ε (t, x) := by
  have htr : t ∈ Ico 0 (place.T + δ) := ⟨ht.1.le, by linarith [ht.2]⟩
  obtain ⟨N, hN, hn, hv⟩ := reference.velocity_smooth
  obtain ⟨M, hM, hm, hp⟩ := reference.pressure_smooth
  let O := (N ∩ M) ∩ (Iio place.T ×ˢ (univ : Set Space))
  have hO : IsOpen O := (hN.inter hM).inter (isOpen_Iio.prod isOpen_univ)
  have hz : (t, x) ∈ O := ⟨⟨hn ⟨htr, subset_closure hx⟩,
    hm ⟨htr, subset_closure hx⟩⟩, ht.2, mem_univ _⟩
  have hvO := hv.mono (show O ⊆ N from fun z hz => hz.1.1)
  have hpO := hp.mono (show O ⊆ M from fun z hz => hz.1.2)
  have hwO := (C.correction_smooth ε hε).contDiffOn (s := O)
  have hUO := hU.mono (show O ⊆ Iio place.T ×ˢ univ from inter_subset_right)
  have hPO := hP.mono (show O ⊆ Iio place.T ×ˢ univ from inter_subset_right)
  change NavierStokesR3.ProblemStatement.navierStokesResidual ν
    (fun z => (reference.velocity z + D.correction ε z) + scaledVelocity u place.x₀ place.T ε z)
    (domainNormalizePressure Ω (fun z => reference.pressure z + scaledPressure p place.x₀ place.T ε z)) t x = _
  rw [residual_domainNormalizePressure,
    domain_residual_add hO (hvO.add hwO) hUO hpO hPO ν hz,
    corrected_background_momentum hδ C hε ht hx, heq t ht.2 x]
  have hc₁ := C.crossTransport_background_advects_packet ε hε t ⟨ht.1.le, ht.2⟩ x
  have hc₂ := C.crossTransport_packet_advects_background ε hε t ⟨ht.1.le, ht.2⟩ x
  change spatialDerivative (scaledVelocity u place.x₀ place.T ε) t x
    (reference.velocity (t, x) + D.correction ε (t, x)) = 0 at hc₁
  change spatialDerivative (fun z => reference.velocity z + D.correction ε z) t x
    (scaledVelocity u place.x₀ place.T ε (t, x)) = 0 at hc₂
  rw [hc₂, hc₁, add_zero, add_zero]
  rfl

end InsertedTriple
end NSFormalization.Section3.T23
