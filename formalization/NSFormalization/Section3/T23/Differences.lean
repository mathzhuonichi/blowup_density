import NSFormalization.Section3.T23.Boundary
import NSFormalization.Section3.T15.Placement

/-!
# T23 U4: localized differences and boundary retention

The U3 insertion formulas are accepted only as explicit hypotheses.  This
module proves the eight U4 fields from those formulas and the already proved
placement, local-correction, packet-support, and domain-geometry facts.
-/

noncomputable section

namespace NSFormalization.Section3.T23

open Set Metric Filter
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T15
open NSFormalization.Section3.T22 (zeroExtension)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open scoped Topology

/-- One radius strictly larger than both the correction cutoff radius and the
packet-carrier radius supplied by the scaling API. -/
def diffSupportRadius (cutoffRadius packetRadius : ℝ) : ℝ :=
  max cutoffRadius packetRadius + 1

/-- The correction cutoff radius is strictly below the common radius. -/
theorem cutoffRadius_lt_diffSupportRadius (cutoffRadius packetRadius : ℝ) :
    cutoffRadius < diffSupportRadius cutoffRadius packetRadius := by
  unfold diffSupportRadius
  linarith [le_max_left cutoffRadius packetRadius]

/-- The packet-carrier radius is strictly below the common radius. -/
theorem packetRadius_lt_diffSupportRadius (cutoffRadius packetRadius : ℝ) :
    packetRadius < diffSupportRadius cutoffRadius packetRadius := by
  unfold diffSupportRadius
  linarith [le_max_right cutoffRadius packetRadius]

/-- The API's common support radius is positive as soon as the actual cutoff
radius is positive. -/
theorem diffSupportRadius_pos {cutoffRadius packetRadius : ℝ}
    (hcutoff : 0 < cutoffRadius) :
    0 < diffSupportRadius cutoffRadius packetRadius :=
  hcutoff.trans (cutoffRadius_lt_diffSupportRadius cutoffRadius packetRadius)

/-- Shrink any already-compatible family threshold so its closed upper
endpoint still places the entire open `ε ρ` ball inside the chart ball. -/
def differenceThreshold {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    (place : DomainPlacementData u p f K) (base cutoffRadius packetRadius : ℝ) : ℝ :=
  min base (domainPlacementMargin place.chartCenter place.x₀ place.chartRadius /
    (2 * diffSupportRadius cutoffRadius packetRadius))

/-- The shrunk threshold remains positive. -/
theorem differenceThreshold_pos {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    (place : DomainPlacementData u p f K) {base cutoffRadius packetRadius : ℝ}
    (hbase : 0 < base) (hcutoff : 0 < cutoffRadius) :
    0 < differenceThreshold place base cutoffRadius packetRadius := by
  unfold differenceThreshold
  apply lt_min hbase
  exact div_pos (domainPlacementMargin_pos place.x₀_mem)
    (mul_pos (by norm_num) (diffSupportRadius_pos hcutoff))

/-- Shrinking preserves every supplier fact already valid up to `base`. -/
theorem differenceThreshold_le_base {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    (place : DomainPlacementData u p f K) (base cutoffRadius packetRadius : ℝ) :
    differenceThreshold place base cutoffRadius packetRadius ≤ base := by
  exact min_le_left _ _

/-- The `O(ε)` difference-support ball lies in the prescribed chart ball on
the shrunk range, including the closed upper endpoint. -/
theorem diffSupport_in_chart {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    (place : DomainPlacementData u p f K) (base cutoffRadius packetRadius : ℝ)
    (hcutoff : 0 < cutoffRadius) :
    ∀ ε ∈ Ioc (0 : ℝ)
        (differenceThreshold place base cutoffRadius packetRadius),
      ball place.x₀ (ε * diffSupportRadius cutoffRadius packetRadius) ⊆
        ball place.chartCenter place.chartRadius := by
  intro ε hε x hx
  have hρ : 0 < diffSupportRadius cutoffRadius packetRadius :=
    diffSupportRadius_pos hcutoff
  have hden : 0 < 2 * diffSupportRadius cutoffRadius packetRadius := by
    positivity
  have he : ε * (2 * diffSupportRadius cutoffRadius packetRadius) ≤
      domainPlacementMargin place.chartCenter place.x₀ place.chartRadius :=
    (le_div_iff₀ hden).mp
      (hε.2.trans (min_le_right _ _))
  have heρ : ε * diffSupportRadius cutoffRadius packetRadius <
      domainPlacementMargin place.chartCenter place.x₀ place.chartRadius := by
    nlinarith [mul_pos hε.1 hρ]
  have hxρ := mem_ball.mp hx
  apply mem_ball.mpr
  calc
    dist x place.chartCenter ≤ dist x place.x₀ + dist place.x₀ place.chartCenter :=
      dist_triangle _ _ _
    _ < place.chartRadius := by
      rw [domainPlacementMargin] at heρ
      linarith

/-- A support point of a fixed-time slice is a support point of the spacetime
field at that time. -/
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

/-- Every correction slice lies in the common `ε ρ` ball; this uses the sharp
I02/local-correction spacetime support, not merely its fixed-radius corollary. -/
theorem correction_slice_support {v u : SpaceTimeField} {K : Set Space}
    {x₀ : Space} {r T δ ε packetRadius : ℝ} {D : CutoffData}
    (core : LocalCorrectionCore v u K x₀ r T δ D)
    (hε : ε ∈ Ioc (0 : ℝ) D.ε₀) (t : ℝ) :
    tsupport (fun x : Space => D.correction ε (t, x)) ⊆
      ball x₀ (ε * diffSupportRadius D.θRadius packetRadius) := by
  intro x hx
  have hz := core.correction_support ε hε
    (slice_tsupport_subset_spacetime_tsupport (D.correction ε) t hx)
  exact ball_subset_ball
    (mul_le_mul_of_nonneg_left
      (cutoffRadius_lt_diffSupportRadius D.θRadius packetRadius).le hε.1.le) hz.2

/-- I03's carrier inclusion transports the scaled packet carrier into the same
strictly larger `ε ρ` ball. -/
theorem affineCarrier_subset_commonBall {K : Set Space} {x₀ : Space}
    {ε cutoffRadius packetRadius : ℝ} (hε : 0 < ε)
    (hcarrier : K ⊆ ball (0 : Space) packetRadius) :
    (fun y : Space => x₀ + ε • y) '' K ⊆
      ball x₀ (ε * diffSupportRadius cutoffRadius packetRadius) := by
  rintro _ ⟨y, hy, rfl⟩
  have hynorm : ‖y‖ < packetRadius := by
    simpa only [mem_ball, dist_zero_right] using hcarrier hy
  rw [mem_ball, dist_eq_norm]
  have hsub : x₀ + ε • y - x₀ = ε • y := by abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  exact (mul_lt_mul_of_pos_left hynorm hε).trans
    (mul_lt_mul_of_pos_left
      (packetRadius_lt_diffSupportRadius cutoffRadius packetRadius) hε)

/-- The unperiodized scaled packet slice is supported in the common `ε ρ`
ball, using the raw packet support clause and I03's `carrier_subset`. -/
theorem scaledPacket_slice_support {u : VelocityField} {K : Set Space}
    {x₀ : Space} {T ε cutoffRadius packetRadius : ℝ}
    (hK : IsCompact K)
    (hu : ∀ s ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (s, x)) ⊆ K)
    (hcarrier : K ⊆ ball (0 : Space) packetRadius)
    (hε : 0 < ε) {t : ℝ} (ht : t < T) :
    tsupport (fun x : Space => scaledVelocity u x₀ T ε (t, x)) ⊆
      ball x₀ (ε * diffSupportRadius cutoffRadius packetRadius) :=
  (scaledVelocity_tsupp_subset hε hK hu Subset.rfl ht).trans
    (affineCarrier_subset_commonBall hε hcarrier)

/-- The velocity difference has the API's sharp single-ball support.  The U3
velocity formula is threaded verbatim; the support of its two perturbation
summands is bounded by their union. -/
theorem velocityDifference_support {v u : SpaceTimeField}
    {K : Set Space} {x₀ : Space} {r T δ ε₀ packetRadius : ℝ}
    {D : CutoffData} {velocity : ℝ → VelocityField}
    (core : LocalCorrectionCore v u K x₀ r T δ D)
    (hK : IsCompact K)
    (hu : ∀ s ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (s, x)) ⊆ K)
    (hcarrier : K ⊆ ball (0 : Space) packetRadius)
    (hle : ε₀ ≤ D.ε₀)
    (hvelocity : ∀ ε : ℝ, ∀ z : SpaceTime,
      velocity ε z = v z + D.correction ε z + scaledVelocity u x₀ T ε z) :
    ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ico (0 : ℝ) T,
      tsupport (fun x : Space => velocity ε (t, x) - v (t, x)) ⊆
        ball x₀ (ε * diffSupportRadius D.θRadius packetRadius) := by
  intro ε hε t ht
  have hεD : ε ∈ Ioc (0 : ℝ) D.ε₀ := ⟨hε.1, hε.2.trans hle⟩
  have heq : (fun x : Space => velocity ε (t, x) - v (t, x)) =
      (fun x : Space => D.correction ε (t, x) +
        scaledVelocity u x₀ T ε (t, x)) := by
    funext x
    rw [hvelocity]
    abel
  rw [heq]
  exact (tsupport_add _ _).trans (union_subset
    (correction_slice_support core hεD t)
    (scaledPacket_slice_support hK hu hcarrier hε.1 ht.2))

/-- Outside the fixed chart ball the inserted velocity agrees with the
reference.  This is the boundary-collar field, derived from the threaded U3
formula and the two supplier support clauses. -/
theorem collar_agreement {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    (place : DomainPlacementData u p f K)
    {v : SpaceTimeField} {r δ base packetRadius : ℝ} {D : CutoffData}
    {velocity : ℝ → VelocityField}
    (core : LocalCorrectionCore v u K place.x₀ r place.T δ D)
    (hK : IsCompact K)
    (hu : ∀ s ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (s, x)) ⊆ K)
    (hcarrier : K ⊆ ball (0 : Space) packetRadius)
    (hbaseD : base ≤ D.ε₀)
    (hvelocity : ∀ ε : ℝ, ∀ z : SpaceTime,
      velocity ε z = v z + D.correction ε z +
        scaledVelocity u place.x₀ place.T ε z) :
    ∀ ε ∈ Ioc (0 : ℝ)
        (differenceThreshold place base D.θRadius packetRadius),
      ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
        x ∉ ball place.chartCenter place.chartRadius →
          velocity ε (t, x) = v (t, x) := by
  intro ε hε t ht x hx
  have hle : differenceThreshold place base D.θRadius packetRadius ≤ D.ε₀ :=
    (differenceThreshold_le_base place base D.θRadius packetRadius).trans hbaseD
  have hsupp := velocityDifference_support core hK hu hcarrier hle hvelocity ε hε t ht
  have hchart := diffSupport_in_chart place base D.θRadius packetRadius
    core.theta_radius_pos ε hε
  have hxnot : x ∉ tsupport (fun y : Space => velocity ε (t, y) - v (t, y)) :=
    fun hxs => hx (hchart (hsupp hxs))
  exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
    (f := fun y : Space => velocity ε (t, y) - v (t, y)) hxnot)

/-- The inserted velocity retains the no-slip boundary values.  The prescribed
closed chart ball is disjoint from the frontier of the open domain, so collar
agreement reduces the claim to the reference solution's no-slip field. -/
theorem noSlip_preserved {ν : ℝ} {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K Ω : Set Space}
    (place : DomainPlacementData u p f K)
    {a : SpatialField} {g : SpaceTimeField} {r δ base packetRadius : ℝ}
    {D : CutoffData}
    (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
    {velocity : ℝ → VelocityField}
    (core : LocalCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
    (hΩ : IsOpen Ω) (hδ : 0 < δ)
    (hball : closure (ball place.chartCenter place.chartRadius) ⊆ Ω)
    (hK : IsCompact K)
    (hu : ∀ s ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (s, x)) ⊆ K)
    (hcarrier : K ⊆ ball (0 : Space) packetRadius)
    (hbaseD : base ≤ D.ε₀)
    (hvelocity : ∀ ε : ℝ, ∀ z : SpaceTime,
      velocity ε z = reference.velocity z + D.correction ε z +
        scaledVelocity u place.x₀ place.T ε z) :
    ∀ ε ∈ Ioc (0 : ℝ)
        (differenceThreshold place base D.θRadius packetRadius),
      ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x ∈ frontier Ω,
        velocity ε (t, x) = 0 := by
  intro ε hε t ht x hxfront
  have hclosed : closedBall place.chartCenter place.chartRadius ⊆ Ω := by
    rw [← closure_ball place.chartCenter place.chartRadius_pos.ne']
    exact hball
  have hdisjoint := prescribed_closedBall_disjoint_frontier hΩ hclosed
  have hxout : x ∉ ball place.chartCenter place.chartRadius := by
    intro hxball
    exact Set.disjoint_left.mp hdisjoint (ball_subset_closedBall hxball) hxfront
  rw [collar_agreement place core hK hu hcarrier hbaseD hvelocity ε hε t ht x hxout]
  exact reference.no_slip t ⟨ht.1, ht.2.trans (lt_add_of_pos_right place.T hδ)⟩ x hxfront

/-- The velocity difference is divergence free in the domain.  This consumes
the U3 smoothness and divergence conclusions directly, without packaging an
inserted solution record. -/
theorem velocityDifference_divFree {ν : ℝ} {u : VelocityField}
    {p : PressureField} {f : VelocityField} {K Ω : Set Space}
    (place : DomainPlacementData u p f K)
    {a : SpatialField} {g : SpaceTimeField} {δ ε₀ : ℝ}
    (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
    {velocity : ℝ → VelocityField} (hδ : 0 < δ)
    (hvelocity_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      SmoothOnClosedSlab (Ico (0 : ℝ) place.T) Ω (velocity ε))
    (hincompressible : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x ∈ Ω,
        spatialDivergence (velocity ε) t x = 0) :
    ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x ∈ Ω,
      spatialDivergence
        (fun z => velocity ε z - reference.velocity z) t x = 0 := by
  intro ε hε t ht x hx
  change spatialDivergence (velocity ε - reference.velocity) t x = 0
  have htref : t ∈ Ico (0 : ℝ) (place.T + δ) :=
    ⟨ht.1, ht.2.trans (lt_add_of_pos_right place.T hδ)⟩
  have hd := spatialDerivative_sub_at
    ((hvelocity_smooth ε hε).contDiffAt_slice ht (subset_closure hx))
    (reference.velocity_smooth.contDiffAt_slice htref (subset_closure hx))
  simp only [spatialDivergence, hd, _root_.sub_apply, PiLp.sub_apply,
    Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr
    ((hincompressible ε hε t ht x hx).trans
      (reference.divergence t htref x hx).symm)

/-- Every correction-force slice, including slices after `T`, lies in the
common `ε ρ` ball.  The proof uses I02's force-support-in-correction-support
fact followed by the sharp correction cutoff support. -/
theorem correctionForce_slice_support (ν : ℝ)
    {v u : SpaceTimeField} {K : Set Space}
    {x₀ : Space} {r T δ ε packetRadius : ℝ} {D : CutoffData}
    (core : LocalCorrectionCore v u K x₀ r T δ D)
    (hε : ε ∈ Ioc (0 : ℝ) D.ε₀) (t : ℝ) :
    tsupport (fun x : Space => correctionForce ν v D ε (t, x)) ⊆
      ball x₀ (ε * diffSupportRadius D.θRadius packetRadius) := by
  intro x hx
  have hz : (t, x) ∈ tsupport (correctionForce ν v D ε) :=
    slice_tsupport_subset_spacetime_tsupport (correctionForce ν v D ε) t hx
  have hw := core.correction_support ε hε (force_support ν v D ε hz)
  exact ball_subset_ball
    (mul_le_mul_of_nonneg_left
      (cutoffRadius_lt_diffSupportRadius D.θRadius packetRadius).le hε.1.le) hw.2

end NSFormalization.Section3.T23
