import NSFormalization.Section3.T15.SingleCopy
import NSFormalization.Section3.T15.HaarBridge
import NSFormalization.Section3.T10.ForcePaths
import NSFormalization.Section4.I03.Energy

/-!
# T15 U4 — the two packet-energy identities on the torus, with honest slices

`paper/sections/03-torus.tex:125-128,145-146` (`eq:packetEscale`) states, for the
periodized rescaled packet `U_ε`,
`‖U_ε‖_{L^∞(0,T;L²(T³))} = ε^{1/2} M` and `‖∇U_ε‖_{L²(0,T;L²(T³))} = ε^{1/2} D`,
with `M` the packet's least upper energy bound and `D` its dissipation constant.

This module proves the three canonical `ScalingAPI` fields
`energySlices_memLp`, `packetEnergyIdentity`, `packetDissipationIdentity`
(`Section3/T15/Scaling.lean:353,364` and `research/T15/Spec.lean:793-818`) over
the raw packet clauses and the canonical `PlacementData`.

Route (`research/T15/T15_SPLIT.md` U4):

* `Placement` puts every rescaled velocity slice with `t < T` strictly inside
  `interior fundamentalCube`, and `SingleCopy` collapses the periodization to
  its zero-lattice copy there;
* the canonical torus chart always produces a representative in the *closed*
  fundamental cube (`torusChart_mem_fundamentalCube`), so the Haar lift of the
  periodization is literally the Haar lift of the rescaled slice;
* `HaarBridge`'s `eLpNorm_torusLift_periodize` and
  `eLpNorm_torusLift_spatialGradient_periodize` move the two Haar `L²` norms to
  the whole-space Lebesgue norms of the rescaled slice (`|Q| = 1`);
* the Section 4 identities `I03.energyEssSup_scaled_eq` (`Energy.lean:487`) and
  `I03.energyGradient_scaled_eq` (`:304`) — both already stated over the *same*
  time interval `Ioo 0 T` as `energyEssSupT`/`energyGradientT` — give the exact
  scalings, and `I03.sqrt_mul_eq_rpow_half` rewrites `√ε` as `ε^{1/2}`.

The `MemLp` guards do not use any of that: the periodization of a slice
supported strictly inside the cube is globally smooth (vendor
`contDiff_periodize` through the lane-352 `rfl` bridge), and the Haar lift of a
continuous field on a probability space lies in every `L^q`
(`T10.memLp_torusLift_vector`, extended here to the `WithLp 2 (Fin 3 → Space)`
gradient vector).

No `sorry`, no named input, no new mathematical alias.
-/

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

/-! ## §1  The canonical torus chart lands in the closed fundamental cube -/

/-- The representative `NSFormalization.Paper1.torusLift` evaluates at always has
all three coordinates in `Ioc 0 1`, hence lies in `fundamentalCube = [0,1]³`. -/
theorem torusChart_mem_fundamentalCube (z : PeriodicTorus) :
    toSpace ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).val) ∈ fundamentalCube := by
  intro i
  have h := (UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).property i
  simp only [Pi.zero_apply, zero_add] at h
  exact ⟨h.1.le, h.2⟩

/-- Two fields agreeing on the closed fundamental cube have the *same* Haar
lift, pointwise on the torus. -/
theorem torusLift_congr_cube {E : Type*} {g h : Space → E}
    (hgh : ∀ x ∈ fundamentalCube, g x = h x) : torusLift g = torusLift h := by
  funext z
  exact hgh _ (torusChart_mem_fundamentalCube z)

/-! ## §2  Regularity of a periodization supported strictly inside the cube -/

/-- A smooth field supported strictly inside the fundamental cube has a globally
smooth periodization.  This is the vendor locally finite sum theorem
`NavierStokes.PeriodicLocalization.contDiff_periodize` read through the lane-352
bridge `Bridges.periodize_eq_vendor`. -/
theorem contDiff_periodize_of_subset_interior {g : SpatialField}
    (hg : ContDiff ℝ ∞ g) (hsupp : tsupport g ⊆ interior fundamentalCube) :
    ContDiff ℝ ∞ (periodize g) := by
  have hv : ContDiff ℝ ∞ (fun z : SpaceTime => g z.2) := hg.comp contDiff_snd
  have h := NavierStokes.PeriodicLocalization.contDiff_periodize
    (supportedInCube_of_tsupport_subset_interior hsupp) hv
  have he : periodize g = fun x : Space =>
      NavierStokes.PeriodicLocalization.periodize (fun z : SpaceTime => g z.2) (0, x) := by
    funext x
    exact periodize_eq_vendor g 0 x
  rw [he]
  exact h.comp (contDiff_const.prodMk contDiff_id)

/-- The Haar lift of a continuous gradient vector field lies in every `L^q(T³)`;
the componentwise form of `T10.memLp_torusLift_vector` on the assembled
`WithLp 2 (Fin 3 → Space)` gradient. -/
theorem memLp_torusLift_gradientVector {G : Space → WithLp 2 (Fin 3 → Space)}
    (hG : Continuous G) (q : ℝ≥0∞) :
    MemLp (torusLift G) q periodicTorusMeasure := by
  apply MemLp.of_eval_piLp
  intro i
  exact memLp_torusLift_vector (by fun_prop : Continuous fun x : Space => G x i) q

/-! ## §3  Smoothness of the rescaled velocity slice -/

/-- Every spatial slice of the rescaled velocity strictly before `T` is smooth;
`Source.PacketScaling.dilate_smoothOn` read through `I03.parabolic_window`, then
sliced by `I03.slice_contDiff_of_slab`.  The only packet clause used is the
smoothness of the zero-past extension. -/
theorem scaledVelocity_slice_contDiff {u : VelocityField} {x₀ : Space} {T ε : ℝ}
    (hext : ContDiffOn ℝ ∞ (zeroPastField u) (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hε : 0 < ε) {t : ℝ} (ht : t < T) :
    ContDiff ℝ ∞ (fun x : Space => scaledVelocity u x₀ T ε (t, x)) := by
  have h := dilate_smoothOn (f := zeroPastField u) ε⁻¹ (inv_pos.2 hε) (T - ε ^ 2) x₀ hext
  rw [NSFormalization.Section4.I03.parabolic_window ε T] at h
  exact NSFormalization.Section4.I03.slice_contDiff_of_slab h ht

/-! ## §4  `energySlices_memLp` -/

/-- `03-torus.tex:125-128`, the `MemLp` guard of `eq:packetEscale`: every
velocity slice and every full-gradient slice of the periodized rescaled packet
on `(0,T)` is an honest Haar-`L²(T³)` function.

The extra arguments are the verbatim packet clauses used by `Placement`. -/
theorem energySlices_memLp
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hext : ContDiffOn ℝ ∞ (zeroPastField u) (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hK : IsCompact K)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      EnergySlicesMemLpT place.T
        (periodizedScaledVelocity u place.x₀ place.T ε) := by
  intro ε hε
  refine ⟨?_, ?_⟩
  · intro t ht
    have hsm : ContDiff ℝ ∞ (fun x : Space => scaledVelocity u place.x₀ place.T ε (t, x)) :=
      scaledVelocity_slice_contDiff hext hε.1 ht.2
    have hlift : torusLift
        (fun x : Space => periodizedScaledVelocity u place.x₀ place.T ε (t, x))
        = torusLift (fun x : Space => scaledVelocity u place.x₀ place.T ε (t, x)) :=
      torusLift_congr_cube (fun x hx =>
        velocity_singleCopy hK hu place ε hε t ht.2 x hx)
    rw [hlift]
    exact memLp_torusLift_vector hsm.continuous 2
  · intro t ht
    have hsupp : tsupport (fun x : Space => scaledVelocity u place.x₀ place.T ε (t, x))
        ⊆ interior fundamentalCube :=
      scaledVelocity_slice_subset_cube hε hK hu place.carrier_subset place.eps_space
        place.chartBall_in_cube ht.2
    have hsm : ContDiff ℝ ∞ (fun x : Space => scaledVelocity u place.x₀ place.T ε (t, x)) :=
      scaledVelocity_slice_contDiff hext hε.1 ht.2
    have hper : ContDiff ℝ ∞ (periodize
        (fun y : Space => scaledVelocity u place.x₀ place.T ε (t, y))) :=
      contDiff_periodize_of_subset_interior hsm hsupp
    have hw : ContDiff ℝ ∞ (fun z : SpaceTime => periodize
        (fun y : Space => scaledVelocity u place.x₀ place.T ε (t, y)) z.2) :=
      hper.comp contDiff_snd
    refine memLp_torusLift_gradientVector ?_ 2
    exact NSFormalization.Section4.I02.continuous_spatialGradient hw t

/-! ## §5  The two identities -/

/-- `03-torus.tex:125-126,145`, the first identity of `eq:packetEscale`:
`‖U_ε‖_{L^∞(0,T;L²(T³))} = ε^{1/2} M`. -/
theorem packetEnergyIdentity
    {u f : VelocityField} {p : PressureField} {K : Set Space} {M D : ℝ}
    (hP : NSFormalization.Section4.I03.PacketData u K M D)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      energyEssSupT place.T
          (periodizedScaledVelocity u place.x₀ place.T ε) =
        ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * M) := by
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

/-- `03-torus.tex:127-128,145-146`, the second identity of `eq:packetEscale`:
`‖∇U_ε‖_{L²(0,T;L²(T³))} = ε^{1/2} D`. -/
theorem packetDissipationIdentity
    {u f : VelocityField} {p : PressureField} {K : Set Space} {M D : ℝ}
    (hP : NSFormalization.Section4.I03.PacketData u K M D)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      energyGradientT place.T
          (periodizedScaledVelocity u place.x₀ place.T ε) =
        ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * D) := by
  intro ε hε
  have hT : 2 * ε ^ 2 < place.T := place.eps_time ε hε
  have key : (∫⁻ t in Ioo (0 : ℝ) place.T,
        (eLpNorm (torusLift (fun x : Space =>
          spatialGradient (periodizedScaledVelocity u place.x₀ place.T ε) t x)) 2
          periodicTorusMeasure) ^ (2 : ℝ))
      = ∫⁻ t in Ioo (0 : ℝ) place.T,
        (eLpNorm (fun x : Space => NSFormalization.Section4.I02.spatialGradient
          (Source.parabolicVelocity ε⁻¹ (place.T - ε ^ 2) place.x₀
            (zeroPastField u)) t x) 2 volume) ^ (2 : ℝ) := by
    refine setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    have hsupp : tsupport (fun x : Space => scaledVelocity u place.x₀ place.T ε (t, x))
        ⊆ interior fundamentalCube :=
      scaledVelocity_slice_subset_cube hε hP.carrier_compact hu place.carrier_subset
        place.eps_space place.chartBall_in_cube ht.2
    have hsm : ContDiff ℝ ∞ (fun x : Space => scaledVelocity u place.x₀ place.T ε (t, x)) :=
      scaledVelocity_slice_contDiff hP.extension_smooth hε.1 ht.2
    congr 1
    rw [show (fun x : Space =>
          spatialGradient (periodizedScaledVelocity u place.x₀ place.T ε) t x)
        = (fun x : Space => spatialGradient (fun z : SpaceTime =>
            periodize (fun y : Space =>
              scaledVelocity u place.x₀ place.T ε (t, y)) z.2) t x) from rfl,
      eLpNorm_torusLift_spatialGradient_periodize
        (fun y : Space => scaledVelocity u place.x₀ place.T ε (t, y)) hsm t hsupp,
      ← eLpNorm_gradientVector_eq_gradientENorm hsm volume]
    rfl
  show ((∫⁻ t in Ioo (0 : ℝ) place.T,
      (eLpNorm (torusLift (fun x : Space =>
        spatialGradient (periodizedScaledVelocity u place.x₀ place.T ε) t x)) 2
        periodicTorusMeasure) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)) = _
  rw [key, NSFormalization.Section4.I03.energyGradient_scaled_eq hP place.x₀ hε.1 hT,
    NSFormalization.Section4.I03.sqrt_mul_eq_rpow_half hε.1.le D]

end NSFormalization.Section3.T15
