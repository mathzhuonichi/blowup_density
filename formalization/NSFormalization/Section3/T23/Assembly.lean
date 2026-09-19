import NSFormalization.Section3.T23.SpatialExtension
import NSFormalization.Section3.T23.MatchingSupplier
import NSFormalization.Section3.T23.Solution
import NSFormalization.Section3.T23.Differences
import NSFormalization.Section3.T23.Rates
import NSFormalization.Section3.T23.Lifespan
import NSFormalization.Section3.T23.DomainComparison
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! U9: windowed supplier transport and the complete 48-field assembly. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set Filter Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T16
open NSFormalization.Paper1.RadialPotential (timePotential)
open scoped ContDiff Topology

/-- Preserve any prescribed inner radius, using the positive outer margin. -/
theorem exists_spatial_solenoidal_extension_between {v : VelocityField} {I : Set ℝ}
    {x₀ : Space} {r s : ℝ} (hI : IsOpen I) (hs : 0 < s) (hsr : s < r)
    (hv : ContDiffOn ℝ ∞ v (I ×ˢ ball x₀ r))
    (hdiv : ∀ t ∈ I, ∀ x ∈ ball x₀ r, spatialDivergence v t x = 0) :
    ∃ V : VelocityField,
      ContDiffOn ℝ ∞ V (I ×ˢ (univ : Set Space)) ∧
      (∀ t ∈ I, ∀ x, spatialDivergence V t x = 0) ∧
      EqOn V v (I ×ˢ ball x₀ s) := by
  let χ : ContDiffBump x₀ := ⟨s, (s + r) / 2, hs, by linarith⟩
  have hs : tsupport (χ : Space → ℝ) ⊆ ball x₀ r := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by change (s + r) / 2 < r; linarith)
  let A : VelocityField := fun z => χ z.2 • timePotential v x₀ z
  have hA : ContDiffOn ℝ ∞ A (I ×ˢ (univ : Set Space)) :=
    contDiffOn_bumpSmul hI (timePotential_contDiffOn_ball hI hv) χ.contDiff hs
  refine ⟨SpatialCurl.spatialCurl A,
    SpatialCurl.contDiffOn_spatialCurl hA (by simp), ?_, ?_⟩
  · intro t ht x
    exact SpatialCurl.spatialDivergence_spatialCurl A t x
      ((SpatialCurl.contDiff_spatialSlice hA ht).contDiffAt.of_le (by norm_num))
  · rintro ⟨t, x⟩ ⟨ht, hx⟩
    have hχ : ∀ᶠ y in 𝓝 x, χ y = 1 := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact χ.one_of_mem_closedBall (ball_subset_closedBall hy)
    change SpatialCurl.curl (fun y => χ y • timePotential v x₀ (t, y)) x = v (t, x)
    rw [SpatialCurl.curl_cutoff_eq hχ]
    exact spatialCurl_timePotential_on_ball hv hdiv ht
      (ball_subset_ball (by linarith : s ≤ r) hx)


/-- The original radial core requires global potential agreement. This
historical diagnostic remains valid; U3 now uses the weaker windowed core. -/
theorem supplierCutoff_core_requires_global_potential
    {ν : ℝ} {u v : VelocityField} {K : Set Space}
    (C : WholeSpaceCorrectionAPI ν u K)
    (h : LocalCorrectionCore v u K C.x₀ C.r C.T C.δ C.supplierCutoff) :
    C.potential = timePotential v C.x₀ := by
  funext z
  exact h.potential_formula z.1 z.2

/-- The literal matched supplier satisfies every U3 operational hypothesis.
Only agreement on the open interior cylinder is required. -/
theorem WholeSpaceCorrectionAPI.windowedCore {ν : ℝ} {u v : VelocityField}
    {K : Set Space} (C : WholeSpaceCorrectionAPI ν u K) (hK : IsCompact K)
    (heq : EqOn v C.v (Ioo (0 : ℝ) (C.T + C.δ) ×ˢ ball C.x₀ C.r))
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (C.T + C.δ) ×ˢ ball C.x₀ C.r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (C.T + C.δ), ∀ x ∈ ball C.x₀ C.r,
      spatialDivergence v t x = 0)
    (hu : ∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => u (t, x)) ⊆ K) :
    WindowedCorrectionCore v u K C.x₀ C.r C.T C.δ C.supplierCutoff := by
  have hm (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) C.ε₀) :=
    (C.local_match (e := C.ε₀) heq hε).1
  have hcross := C.local_crossTransport hK hv hdiv hu (e := C.ε₀) le_rfl
  refine {
    theta_radius_pos := C.theta_radius_pos
    eps_time := C.eps_time
    eps_space := C.eps_space
    correction_smooth := C.correction_smooth
    correction_divergence_free := C.correction_divergence_free
    correction_compactSupport := C.correction_compactSupport
    correction_support := C.correction_support
    correction_cancels := ?_
    crossTransport_background_advects_packet := ?_
    crossTransport_packet_advects_background := ?_ }
  · intro ε hε t ht
    have hc := physicalCorrection_cancels_packet hK hv hdiv hu
      C.plateau_open C.carrier_subset_plateau C.theta_support C.theta_one C.eta_one
      (C.eps_time ε hε) (C.eps_space ε hε) hε.1 ht
    change ∃ O, IsOpen O ∧ O ⊆ ball C.x₀ C.r ∧
      tsupport (fun x => NSFormalization.Section3.T15.scaledVelocity u C.x₀ C.T ε (t, x)) ⊆ O ∧
      ∀ x ∈ O, v (t, x) + C.correction ε (t, x) = 0
    rw [← hm ε hε]
    exact hc
  · intro ε hε t ht x
    have hc := (hcross ε hε t ht x).1
    unfold correctedBackground at hc
    rw [hm ε hε] at hc
    exact hc
  · intro ε hε t ht x
    have hc := (hcross ε hε t ht x).2
    unfold correctedBackground at hc
    rw [hm ε hε] at hc
    exact hc

namespace Windowed
open NSFormalization.Section3.T15
open NSFormalization.Section3.T22 (zeroExtension)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)

theorem correction_slice_support {v u : SpaceTimeField} {K : Set Space}
    {x₀ : Space} {r T δ ε packetRadius : ℝ} {D : CutoffData}
    (core : WindowedCorrectionCore v u K x₀ r T δ D)
    (hε : ε ∈ Ioc (0 : ℝ) D.ε₀) (t : ℝ) :
    tsupport (fun x : Space => D.correction ε (t, x)) ⊆
      ball x₀ (ε * diffSupportRadius D.θRadius packetRadius) := by
  intro x hx
  have hz := core.correction_support ε hε
    (slice_tsupport_subset_spacetime_tsupport (D.correction ε) t hx)
  exact ball_subset_ball
    (mul_le_mul_of_nonneg_left
      (cutoffRadius_lt_diffSupportRadius D.θRadius packetRadius).le hε.1.le) hz.2


theorem velocityDifference_support {v u : SpaceTimeField}
    {K : Set Space} {x₀ : Space} {r T δ ε₀ packetRadius : ℝ}
    {D : CutoffData} {velocity : ℝ → VelocityField}
    (core : WindowedCorrectionCore v u K x₀ r T δ D)
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


theorem collar_agreement {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    (place : DomainPlacementData u p f K)
    {v : SpaceTimeField} {r δ base packetRadius : ℝ} {D : CutoffData}
    {velocity : ℝ → VelocityField}
    (core : WindowedCorrectionCore v u K place.x₀ r place.T δ D)
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


theorem noSlip_preserved {ν : ℝ} {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K Ω : Set Space}
    (place : DomainPlacementData u p f K)
    {a : SpatialField} {g : SpaceTimeField} {r δ base packetRadius : ℝ}
    {D : CutoffData}
    (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
    {velocity : ℝ → VelocityField}
    (core : WindowedCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
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


theorem correctionForce_slice_support (ν : ℝ)
    {v u : SpaceTimeField} {K : Set Space}
    {x₀ : Space} {r T δ ε packetRadius : ℝ} {D : CutoffData}
    (core : WindowedCorrectionCore v u K x₀ r T δ D)
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


theorem forceDifference_spatialSupport {ν : ℝ} {u : VelocityField}
    {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : DomainPlacementData u p f K)
    {v g : SpaceTimeField} {r δ base packetRadius : ℝ} {D : CutoffData}
    {force : ℝ → VelocityField}
    (core : WindowedCorrectionCore v u K place.x₀ r place.T δ D)
    (hpacketForce : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hbaseD : base ≤ D.ε₀) (hbasePlace : base ≤ place.ε₀)
    (hforce : ∀ ε : ℝ, ∀ z : SpaceTime,
      force ε z = g z + correctionForce ν v D ε z +
        scaledForce f place.x₀ place.T ε z) :
    ∀ ε ∈ Ioc (0 : ℝ)
        (differenceThreshold place base D.θRadius packetRadius),
      ∀ t : ℝ, ∀ x : Space, force ε (t, x) - g (t, x) ≠ 0 →
        x ∈ closure (ball place.chartCenter place.chartRadius) := by
  intro ε hε t x hx
  have hεD : ε ∈ Ioc (0 : ℝ) D.ε₀ :=
    ⟨hε.1, hε.2.trans
      ((differenceThreshold_le_base place base D.θRadius packetRadius).trans hbaseD)⟩
  have hεplace : ε ∈ Ioc (0 : ℝ) place.ε₀ :=
    ⟨hε.1, hε.2.trans
      ((differenceThreshold_le_base place base D.θRadius packetRadius).trans hbasePlace)⟩
  have heq : (fun y : Space => force ε (t, y) - g (t, y)) =
      (fun y : Space => correctionForce ν v D ε (t, y) +
        scaledForce f place.x₀ place.T ε (t, y)) := by
    funext y
    rw [hforce]
    abel
  have hxsum : x ∈ tsupport (fun y : Space =>
      correctionForce ν v D ε (t, y) +
        scaledForce f place.x₀ place.T ε (t, y)) := by
    apply subset_tsupport
    intro hzero
    apply hx
    rw [congrFun heq x]
    exact hzero
  rcases tsupport_add _ _ hxsum with hcorrection | hscaled
  · apply subset_closure
    exact diffSupport_in_chart place base D.θRadius packetRadius
      core.theta_radius_pos ε hε
        (correctionForce_slice_support ν core hεD t hcorrection)
  · apply subset_closure
    exact scaledForce_slice_support_chart place hpacketForce hεplace t hscaled


theorem forceDifference_zeroExtension_support {ν : ℝ}
    {u : VelocityField} {p : PressureField} {f : VelocityField}
    {K Ω : Set Space} (place : DomainPlacementData u p f K)
    {v g : SpaceTimeField} {r δ base packetRadius : ℝ} {D : CutoffData}
    {force : ℝ → VelocityField}
    (core : WindowedCorrectionCore v u K place.x₀ r place.T δ D)
    (hpacketForce : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hbaseD : base ≤ D.ε₀) (hbasePlace : base ≤ place.ε₀)
    (hforce : ∀ ε : ℝ, ∀ z : SpaceTime,
      force ε z = g z + correctionForce ν v D ε z +
        scaledForce f place.x₀ place.T ε z) :
    ∀ ε ∈ Ioc (0 : ℝ)
        (differenceThreshold place base D.θRadius packetRadius),
      ∀ t : ℝ,
        tsupport (zeroExtension Ω
          (fun x : Space => force ε (t, x) - g (t, x))) ⊆
            closure (ball place.chartCenter place.chartRadius) := by
  intro ε hε t
  exact zeroExtension_tsupport_subset_of_nonzero isClosed_closure
    (forceDifference_spatialSupport place core hpacketForce hbaseD hbasePlace
      hforce ε hε t)


end Windowed

open MeasureTheory
open NSFormalization.Section3.T15 (scaledVelocity scaledPressure scaledForce)
open NSFormalization.Section3.T22 (BoundedDomainNormAPI)
open NSFormalization.Section4.A02 (SpatialField)
open scoped ENNReal

/-- Fieldwise assembly at one matching supplier family. The proof-side
supplier parameters are discharged by the registered binding. -/
def boundaryInsertionAPI
    {ν : ℝ} {u f : VelocityField} {p : PressureField} {K Ω : Set Space}
    {a : SpatialField} {g : VelocityField} {r δ : ℝ}
    (place : DomainPlacementData u p f K) (norms : BoundedDomainNormAPI)
    (D : CutoffData) (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
    (hν : 0 < ν) (hΩ : IsBoundedBoxOrSmoothDomain Ω) (hI : IBP Ω)
    (hδ : 0 < δ) (hg : g ∈ forceClassOmega Ω) (ha : a ∈ initialClassOmega Ω)
    (hball : closure (ball place.chartCenter place.chartRadius) ⊆ Ω)
    (hrball : ball place.x₀ r ⊆ Ω)
    (core : WindowedCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
    (hD : 0 < D.ε₀) (hK : IsCompact K)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x => u (t, x)) ⊆ K)
    (hf : ContDiff ℝ ∞ f)
    (hfs : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hus : ContDiffOn ℝ ∞ (NSFormalization.Source.PacketScaling.zeroPastField u)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hps : ContDiffOn ℝ ∞ (NSFormalization.Source.PacketScaling.zeroPastField p)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hspeed : NavierStokes.ProblemStatement.SpeedUnboundedAtOne u)
    (packetRadius s M E B : ℝ) (hs : 0 < s)
    (hcarrier : K ⊆ ball (0 : Space) packetRadius)
    (hdiv : ∀ ε ∈ Ioc (0 : ℝ) s, ∀ t : ℝ, t < place.T → ∀ x : Space,
      spatialDivergence (scaledVelocity u place.x₀ place.T ε) t x = 0)
    (heq : ∀ ε ∈ Ioc (0 : ℝ) s, ∀ t : ℝ, t < place.T → ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (scaledVelocity u place.x₀ place.T ε) (scaledPressure p place.x₀ place.T ε) t x =
        scaledForce f place.x₀ place.T ε (t, x))
    (hwhole : ∀ ε ∈ Ioc (0 : ℝ) s,
      NSFormalization.Section3.T24.energyENorm place.T
        (fun z => D.correction ε z + scaledVelocity u place.x₀ place.T ε z) ≤
        ENNReal.ofReal ((M + E) * ε ^ ((1 : ℝ) / 2) + B * ε ^ ((3 : ℝ) / 2)))
    (A F : ℝ → ℝ)
    (hpacket : ∀ q, 0 ≤ q → q < 1 / 2 → ∀ ε ∈ Ioc (0 : ℝ) s,
      NSFormalization.Section4.D01.forceSobolevENorm 1 q
        (scaledForce f place.x₀ place.T ε) ≤
      ENNReal.ofReal (A q * (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - q))))
    (hcorr : ∀ q, 0 ≤ q → q < 1 / 2 → ∀ ε ∈ Ioc (0 : ℝ) s,
      NSFormalization.Section4.D01.forceSobolevENorm 1 q
        (correctionForce ν reference.velocity D ε) ≤
      ENNReal.ofReal (F q * (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - q)))) :
    BoundaryInsertionAPI ν u p f K M E place Ω norms a g r δ D reference := by
  let base := min (min place.ε₀ D.ε₀) s
  let e := differenceThreshold place base D.θRadius packetRadius
  have hepos : 0 < e := differenceThreshold_pos place
    (lt_min (lt_min place.eps_pos hD) hs) core.theta_radius_pos
  have heb : e ≤ base := differenceThreshold_le_base place base D.θRadius packetRadius
  have hbp : base ≤ place.ε₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hbd : base ≤ D.ε₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hbs : base ≤ s := min_le_right _ _
  have ep {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) e) : ε ∈ Ioc (0 : ℝ) place.ε₀ :=
    ⟨hε.1, hε.2.trans (heb.trans hbp)⟩
  have ed {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) e) : ε ∈ Ioc (0 : ℝ) D.ε₀ :=
    ⟨hε.1, hε.2.trans (heb.trans hbd)⟩
  have es {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) e) : ε ∈ Ioc (0 : ℝ) s :=
    ⟨hε.1, hε.2.trans (heb.trans hbs)⟩
  let V := InsertedTriple.velocity place D reference
  let P := InsertedTriple.pressure place reference
  let G := InsertedTriple.force place D reference
  have vformula := InsertedTriple.velocity_formula place D reference
  have gformula := InsertedTriple.force_formula place D reference
  have hU {ε : ℝ} (hε : 0 < ε) :=
    InsertedTriple.packet_velocity_smooth (place := place) hus hε
  have hP {ε : ℝ} (hε : 0 < ε) :=
    InsertedTriple.packet_pressure_smooth (place := place) hps hε
  have hno := Windowed.noSlip_preserved place reference core hΩ.1 hδ hball hK hu
    hcarrier hbd vformula
  have hsolution : ∀ ε ∈ Ioc (0 : ℝ) e,
      ∃ w : ClassicalSolutionOmega ν Ω a (G ε) place.T,
        w.velocity = V ε ∧ w.pressure = P ε := by
    intro ε hε
    exact ⟨InsertedTriple.classicalSolution hδ hΩ.1 hΩ.2.1 hΩ.2.2.1 core
      (ed hε) (ep hε) (hU hε.1) (hP hε.1) (hdiv ε (es hε)) (heq ε (es hε))
      (hno ε hε), rfl, rfl⟩
  have hfm : ∀ ε ∈ Ioc (0 : ℝ) e, (fun z => G ε z - g z) ∈ forceClassOmega Ω :=
    fun ε hε => InsertedTriple.forceDifference_mem core hrball hf hfs (ed hε) (ep hε)
  have hsupport := Windowed.forceDifference_spatialSupport place core hfs hbd hbp gformula
    (packetRadius := packetRadius)
  have hcomp := domain_zeroExt_comparison norms hΩ.1 place.chartRadius_pos hball hfm hsupport
  have hrate := forceDifference_sobolev_bound place D reference G e A F
    ((heb.trans hbp).trans place.eps_le_one) gformula
    (fun ε hε t x hx => hball (hsupport ε hε t x hx))
    (fun q ε hε => (Classical.choose_spec (hcomp q)).2 ε hε |>.1)
    (fun ε _ t _ => ((NSFormalization.Source.PacketScaling.parabolicForce_smooth hf _ _ _).continuous.comp
      (continuous_const.prodMk continuous_id)))
    (fun ε hε _ _ => ((force_smooth_of_local ν reference.velocity D ε
      (isOpen_Ioo.prod isOpen_ball) (reference.local_velocity place.x₀ hrball).1
      (core.correction_smooth ε (ed hε)) (core.correction_support_interior (ed hε))).continuous.comp
        (continuous_const.prodMk continuous_id)))
    (fun q hq hq' ε hε => hpacket q hq hq' ε (es hε))
    (fun q hq hq' ε hε => hcorr q hq hq' ε (es hε))
  have hpackSupport : ∀ ε ∈ Ioc (0 : ℝ) e, ∀ t ∈ Ioo (0 : ℝ) place.T,
      tsupport (fun x => scaledVelocity u place.x₀ place.T ε (t, x)) ⊆
        ball place.chartCenter place.chartRadius := by
    intro ε hε t ht
    exact (scaledPacket_slice_support hK hu hcarrier hε.1 ht.2).trans
      (diffSupport_in_chart place base D.θRadius packetRadius core.theta_radius_pos ε hε)
  have hcancel : ∀ ε ∈ Ioc (0 : ℝ) e, ∀ t ∈ Ico (place.T - ε ^ 2) place.T,
      ∀ x ∈ tsupport (fun y => scaledVelocity u place.x₀ place.T ε (t, y)),
        reference.velocity (t, x) + D.correction ε (t, x) = 0 := by
    intro ε hε t ht x hx
    obtain ⟨O, _, _, hO, hc⟩ := core.correction_cancels ε (ed hε) t ht
    exact hc x (hO hx)
  exact {
    domain := hΩ
    delta_pos := hδ
    reference_force_mem := hg
    initial_mem := ha
    interiorBall_in_domain := hball
    ε₀ := e
    eps_pos := hepos
    eps_le_scaling := heb.trans hbp
    eps_le_cutoff := heb.trans hbd
    velocity := V
    pressure := P
    force := G
    velocity_formula := vformula
    pressure_formula := InsertedTriple.pressure_formula place reference
    force_formula := gformula
    force_mem := fun ε hε => InsertedTriple.force_mem core hrball hg hf hfs (ed hε) (ep hε)
    forceDifference_mem := hfm
    velocity_smooth := fun ε hε => InsertedTriple.velocity_smooth hδ core (ed hε) (hU hε.1)
    pressure_smooth := fun ε hε => InsertedTriple.pressure_smooth hδ hΩ.2.1 hΩ.1.measurableSet (hP hε.1)
    initial := fun ε hε _ hx => InsertedTriple.initial core (ed hε) (ep hε) hx
    incompressible := fun ε hε _ ht _ hx => InsertedTriple.incompressible hδ core (ed hε)
      (hU hε.1) (hdiv ε (es hε)) ht hx
    momentum := fun ε hε _ ht _ hx => InsertedTriple.momentum hδ core (ed hε)
      (hU hε.1) (hP hε.1) (heq ε (es hε)) ht hx
    history := fun ε hε _ _ ht x => InsertedTriple.history core (ed hε) ht x
    collar_agreement := Windowed.collar_agreement place core hK hu hcarrier hbd vformula
    noSlip_preserved := hno
    solution := hsolution
    lifespan := U8.lifespan place D reference hspeed (heb.trans hbp) hball vformula
      hpackSupport hcancel hsolution hν hΩ.1 hΩ.2.1 hI
    maximal := U8.maximal place D reference hspeed (heb.trans hbp) hball vformula
      hpackSupport hcancel hsolution hν hΩ.1 hΩ.2.1 hI
    blowup := U8.blowup place D reference hspeed (heb.trans hbp) hball vformula hpackSupport hcancel
    blowup_limsup := U8.blowup_limsup place D reference hspeed (heb.trans hbp) hball vformula
      hpackSupport hcancel hsolution
    crossTransport_background_advects_packet := fun ε hε => core.crossTransport_background_advects_packet ε (ed hε)
    crossTransport_packet_advects_background := fun ε hε => core.crossTransport_packet_advects_background ε (ed hε)
    velocityDifference_divFree := velocityDifference_divFree place reference hδ
      (fun ε hε => InsertedTriple.velocity_smooth hδ core (ed hε) (hU hε.1))
      (fun ε hε _ ht _ hx => InsertedTriple.incompressible hδ core (ed hε)
        (hU hε.1) (hdiv ε (es hε)) ht hx)
    diffSupportRadius := diffSupportRadius D.θRadius packetRadius
    diffSupportRadius_pos := diffSupportRadius_pos core.theta_radius_pos
    velocityDifference_support := Windowed.velocityDifference_support core hK hu hcarrier (heb.trans hbd) vformula
    diffSupport_in_chart := diffSupport_in_chart place base D.θRadius packetRadius core.theta_radius_pos
    forceDifference_spatialSupport := hsupport
    energyConst := energyConst B
    energyConst_nonneg := energyConst_nonneg B
    energyRate := energyRate place D reference V M E B e vformula (fun ε hε => hwhole ε (es hε))
    forceDiffSobolevConst := forceDiffSobolevConst A F
    forceDiffSobolevConst_pos := fun q _ _ => forceDiffSobolevConst_pos A F q
    forceDifference_sobolev_bound := hrate
    domain_zeroExt_comparison := hcomp
    forceDifference_negativeSobolev_tendsto := forceDifference_negativeSobolev_tendsto Ω G g e _ hepos hrate
    forceDifference_convergence := forceDifference_convergence Ω G g e _ hepos hrate
    noSlip_uniqueness := noSlip_uniqueness_of_ibp ν hν Ω hΩ hI }

/-- The prescribed closed ball leaves enough room for the extension's outer radius. -/
theorem exists_outer_ball {Ω : Set Space} (hΩ : IsOpen Ω) {x : Space} {r : ℝ}
    (hr : 0 < r) (hball : closure (ball x r) ⊆ Ω) :
    ∃ R : ℝ, r < R ∧ ball x R ⊆ Ω := by
  rw [closure_ball x hr.ne'] at hball
  obtain ⟨d, hd, hb⟩ := (isCompact_closedBall x r).exists_thickening_subset_open hΩ hball
  rw [thickening_closedBall hd hr.le] at hb
  exact ⟨d + r, by linarith, hb⟩

end NSFormalization.Section3.T23
