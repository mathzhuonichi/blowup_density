import NSFormalization.Section3.T16.BallPotential
import NSFormalization.Section3.T16.LatticeLift
import NSFormalization.Source.PhysicalRemoval

/-!
# T16 (`lem:potential`): the assembly `localPotential : localPotentialStatement`

This module assembles the general local divergence-free cutoff lemma
(`paper/sections/03-torus.tex:176-217`, `research/T16/Spec.lean:328-336`) over the
canonical Section 3 / Section 4 vocabulary, from the three preceding lanes:

* the cutoffs and the small-scale threshold (`exists_originCutoff`,
  `exists_timeCutoff`, `exists_threshold`, `Section3/T16/LocalPotential.lean`);
* the radial vector potential on the chart ball (`exists_potential_on_ball`,
  `timePotential_contDiffOn_ball`, `spatialCurl_timePotential_on_ball`,
  `Section3/T16/BallPotential.lean`);
* the unit-periodic lattice lift of a chart correction and its seven canonical
  `correction_*` fields (`correction_fields_of_chart`,
  `Section3/T16/LatticeLift.lean`).

The concrete chart correction is
`W ε = physicalCorrection v x₀ T θ η ε = localCorrection v x₀ (θ_ε) (η_ε)`
(`NSFormalization.Paper1.CorrectionProfile`), so the chart curl formula
`W ε = -∇×(η_ε θ_ε A)` with `A = timePotential v x₀` holds by `rfl`.  Its
compact support and product support bound come from
`NSFormalization.Source.PhysicalRemoval.{physical_compact, physical_support}`
(no smoothness of the reference is used there).  Its *global* smoothness and
divergence-freeness — which the `PhysicalRemoval` versions derive from
`ContDiff ℝ ∞ v` on all of space — are re-derived here from the *local*
hypothesis (`v` smooth only on the chart cylinder) through a joint spacetime
truncation of the inner field `(η_ε θ_ε) • A`, whose support is inside the open
cylinder where `A` is smooth (`cutoffPotential_contDiff`,
`physicalCorrection_contDiff`, `physicalCorrection_divergence`).  The
cancellation datum uses the *scaled plateau* `x₀ + ε•O` where `θ_ε = 1`, the
local curl identity `spatialCurl_timePotential_on_ball`, and the packet-support
bound `periodicScaledPacket = latticeLift (scaledPacket)` with
`delayed_full_support`/`parabolic_support` (`physicalCorrection_cancels`).
-/

noncomputable section

namespace NSFormalization.Section3.T16

open Set MeasureTheory Metric Filter
open NavierStokes NavierStokes.ProblemStatement
open NavierStokes.PeriodicLocalization
open NSFormalization.Section3.T10 (IsPeriodicOn)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField)
open NSFormalization.Paper1.RadialPotential (cross timePotential centeredPotential_eq_integral)
open NSFormalization.Paper1.CorrectionProfile (spatialCutoff temporalCutoff physicalCorrection)
open NSFormalization.Source.PhysicalRemoval (physical_compact physical_support
  spatial_cutoff_support temporal_cutoff_support spaceMap timeMap)
open NSFormalization.Source (parabolicVelocity)
open NSFormalization.Source.PacketScaling (scaledSupport parabolic_support zeroPast_dilate_early
  zeroPastField_of_pos zeroPastField)
open scoped ContDiff Topology

/-! ## 1. Global smoothness of the truncated cutoff potential (local reference) -/

/-- A smooth scalar cutoff `c` supported inside an open box `I ×ˢ B`, multiplied
by a field `A` that is smooth only on that box, is globally smooth: on the box
`A` is smooth, and off `tsupport c` the product vanishes. -/
theorem contDiff_cutoffSmul_of_ballSmooth
    {A : SpaceTime → Space} {I : Set ℝ} {B : Set Space}
    (hI : IsOpen I) (hB : IsOpen B)
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ B))
    {c : SpaceTime → ℝ} (hc : ContDiff ℝ ∞ c)
    (hsupp : tsupport c ⊆ I ×ˢ B) :
    ContDiff ℝ ∞ (fun z => c z • A z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ I ×ˢ B
  · have hAz : ContDiffAt ℝ ∞ A z := hA.contDiffAt ((hI.prod hB).mem_nhds hz)
    exact hc.contDiffAt.smul hAz
  · have hznot : z ∉ tsupport c := fun h => hz (hsupp h)
    have heq : (fun z => c z • A z) =ᶠ[𝓝 z] (fun _ => (0 : Space)) := by
      filter_upwards [(isClosed_tsupport c).isOpen_compl.mem_nhds hznot] with w hw
      rw [image_eq_zero_of_notMem_tsupport hw, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- The scaled spatial cutoff is supported in the chart ball once
`ε·θRadius < r`. -/
theorem spatialCutoff_tsupport_ball {θ : Space → ℝ} {x₀ : Space} {θRadius r ε : ℝ}
    (hε : 0 < ε) (hθcs : HasCompactSupport θ) (hθsupp : tsupport θ ⊆ ball (0 : Space) θRadius)
    (hεspace : ε * θRadius < r) :
    tsupport (spatialCutoff θ x₀ ε) ⊆ ball x₀ r := by
  refine (spatial_cutoff_support hε.ne' x₀ hθcs).trans ?_
  rintro _ ⟨y, hy, rfl⟩
  have hyR : ‖y‖ < θRadius := by
    have := hθsupp hy; rwa [mem_ball, dist_zero_right] at this
  rw [mem_ball, dist_eq_norm]
  have hsub : spaceMap ε x₀ y - x₀ = ε • y := by simp only [spaceMap]; abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  exact lt_trans (mul_lt_mul_of_pos_left hyR hε) hεspace

/-- The scaled temporal cutoff is supported in the regular time slab once
`2ε² < min T δ`. -/
theorem temporalCutoff_tsupport_Ioo {η : ℝ → ℝ} {T δ ε : ℝ}
    (hε : 0 < ε) (hηcs : HasCompactSupport η) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hεtime : 2 * ε ^ 2 < min T δ) :
    tsupport (temporalCutoff η T ε) ⊆ Ioo (0 : ℝ) (T + δ) := by
  refine (temporal_cutoff_support hε.ne' T hηcs).trans ?_
  rintro _ ⟨s, hs, rfl⟩
  have hsI : s ∈ Ioo (-2 : ℝ) 2 := hηsupp hs
  have hεsq : 0 < ε ^ 2 := by positivity
  have hmin1 : min T δ ≤ T := min_le_left T δ
  have hmin2 : min T δ ≤ δ := min_le_right T δ
  change T + ε ^ 2 * s ∈ Ioo (0 : ℝ) (T + δ)
  constructor
  · nlinarith [mul_lt_mul_of_pos_left hsI.1 hεsq]
  · nlinarith [mul_lt_mul_of_pos_left hsI.2 hεsq]

/-- The inner field `(η_ε θ_ε) • A` of the physical correction is globally
smooth, using the reference only on the chart cylinder. -/
theorem cutoffPotential_contDiff {v : SpaceTimeField} {x₀ : Space} {θ : Space → ℝ} {η : ℝ → ℝ}
    {T r δ ε θRadius : ℝ}
    (hθsm : ContDiff ℝ ∞ θ) (hηsm : ContDiff ℝ ∞ η)
    (hθcs : HasCompactSupport θ) (hηcs : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θRadius) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r))
    (hεtime : 2 * ε ^ 2 < min T δ) (hεspace : ε * θRadius < r) (hε : 0 < ε) :
    ContDiff ℝ ∞ (fun z : SpaceTime =>
      (temporalCutoff η T ε z.1 * spatialCutoff θ x₀ ε z.2) • timePotential v x₀ z) := by
  have hA : ContDiffOn ℝ ∞ (timePotential v x₀) (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r) :=
    timePotential_contDiffOn_ball isOpen_Ioo hv
  have htc : ContDiff ℝ ∞ (temporalCutoff η T ε) :=
    hηsm.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  have hsc : ContDiff ℝ ∞ (spatialCutoff θ x₀ ε) :=
    hθsm.comp ((contDiff_id.sub contDiff_const).const_smul ε⁻¹)
  have hc : ContDiff ℝ ∞ (fun z : SpaceTime =>
      temporalCutoff η T ε z.1 * spatialCutoff θ x₀ ε z.2) :=
    (htc.comp contDiff_fst).mul (hsc.comp contDiff_snd)
  have hcsupp : tsupport (fun z : SpaceTime =>
      temporalCutoff η T ε z.1 * spatialCutoff θ x₀ ε z.2)
        ⊆ Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r := by
    have hsub : Function.support (fun z : SpaceTime =>
        temporalCutoff η T ε z.1 * spatialCutoff θ x₀ ε z.2)
          ⊆ Function.support (temporalCutoff η T ε) ×ˢ Function.support (spatialCutoff θ x₀ ε) := by
      intro z hz
      refine ⟨fun h => hz ?_, fun h => hz ?_⟩
      · show temporalCutoff η T ε z.1 * spatialCutoff θ x₀ ε z.2 = 0
        rw [h, zero_mul]
      · show temporalCutoff η T ε z.1 * spatialCutoff θ x₀ ε z.2 = 0
        rw [h, mul_zero]
    calc tsupport (fun z : SpaceTime =>
            temporalCutoff η T ε z.1 * spatialCutoff θ x₀ ε z.2)
          ⊆ closure (Function.support (temporalCutoff η T ε) ×ˢ
              Function.support (spatialCutoff θ x₀ ε)) := closure_mono hsub
      _ = tsupport (temporalCutoff η T ε) ×ˢ tsupport (spatialCutoff θ x₀ ε) := closure_prod_eq
      _ ⊆ Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r :=
          Set.prod_mono (temporalCutoff_tsupport_Ioo hε hηcs hηsupp hεtime)
            (spatialCutoff_tsupport_ball hε hθcs hθsupp hεspace)
  exact contDiff_cutoffSmul_of_ballSmooth isOpen_Ioo isOpen_ball hA hc hcsupp

/-- Local companion of `PhysicalRemoval.physical_smooth`: the physical correction
is globally smooth even when the reference is smooth only on the chart cylinder. -/
theorem physicalCorrection_contDiff {v : SpaceTimeField} {x₀ : Space} {θ : Space → ℝ} {η : ℝ → ℝ}
    {T r δ ε θRadius : ℝ}
    (hθsm : ContDiff ℝ ∞ θ) (hηsm : ContDiff ℝ ∞ η)
    (hθcs : HasCompactSupport θ) (hηcs : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θRadius) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r))
    (hεtime : 2 * ε ^ 2 < min T δ) (hεspace : ε * θRadius < r) (hε : 0 < ε) :
    ContDiff ℝ ∞ (physicalCorrection v x₀ T θ η ε) :=
  (SpatialCurl.contDiff_spatialCurl
    (cutoffPotential_contDiff hθsm hηsm hθcs hηcs hθsupp hηsupp hv hεtime hεspace hε)
    (by norm_num)).neg

/-- Local companion of `PhysicalRemoval.physical_divergence`: the physical
correction is divergence-free because it is a spatial curl of a globally smooth
field, again using the reference only on the chart cylinder. -/
theorem physicalCorrection_divergence {v : SpaceTimeField} {x₀ : Space} {θ : Space → ℝ} {η : ℝ → ℝ}
    {T r δ ε θRadius : ℝ}
    (hθsm : ContDiff ℝ ∞ θ) (hηsm : ContDiff ℝ ∞ η)
    (hθcs : HasCompactSupport θ) (hηcs : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θRadius) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r))
    (hεtime : 2 * ε ^ 2 < min T δ) (hεspace : ε * θRadius < r) (hε : 0 < ε) :
    ∀ t x, spatialDivergence (physicalCorrection v x₀ T θ η ε) t x = 0 := by
  have hΦ := cutoffPotential_contDiff hθsm hηsm hθcs hηcs hθsupp hηsupp hv hεtime hεspace hε
  intro t x
  have hp : ContDiff ℝ ∞ (fun y : Space =>
      -((temporalCutoff η T ε t * spatialCutoff θ x₀ ε y) • timePotential v x₀ (t, y))) :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).neg
  have heq : (fun y => physicalCorrection v x₀ T θ η ε (t, y)) =
      SpatialCurl.curl (fun y =>
        -((temporalCutoff η T ε t * spatialCutoff θ x₀ ε y) • timePotential v x₀ (t, y))) := by
    funext y
    exact (NSFormalization.Source.curl_neg _ y).symm
  change (∑ i : Fin 3,
    (fderiv ℝ (fun y => physicalCorrection v x₀ T θ η ε (t, y)) x (coordinateVector i)) i) = 0
  rw [heq]
  exact SpatialCurl.divergence_curl (hp.contDiffAt.of_le (by norm_num))

/-! ## 2. The lattice slice-support bound for a compactly supported chart field -/

/-- Closed-support companion of `latticeLift_sliceSupport`: if the slice support
of `w` is contained in a compact set `C ⊆ ball x₀ ρ`, the spatial slice of the
lift is supported in the periodic lift of `C`.  (`C` compact makes the per
translate closed support exact, so no `ρ < r` slack is needed.) -/
theorem latticeLift_sliceSupport_closed {w : SpaceTimeField} {C : Set Space} {x₀ : Space} {ρ : ℝ}
    (hCcompact : IsCompact C) (hCball : C ⊆ ball x₀ ρ)
    (hslice : ∀ (t : ℝ) (y : Space), w (t, y) ≠ 0 → y ∈ C) (t : ℝ) :
    tsupport (fun x => latticeLift w (t, x)) ⊆ periodicSet C := by
  have hsc : SupportedInCube (ρ + ‖x₀‖) w :=
    supportedInCube_of_ball (fun z hz => hCball (hslice z.1 z.2 hz))
  intro x hx
  by_contra hxnot
  obtain ⟨N, hN⟩ := periodize_locally_eq_sum hsc (t, x)
  have hNs : (fun y => latticeLift w (t, y)) =ᶠ[𝓝 x]
      (fun y => ∑ n ∈ latticeBoxFinset N, translate w n (t, y)) := by
    have htend : Tendsto (fun y : Space => (t, y)) (𝓝 x) (𝓝 (t, x)) :=
      (continuousAt_const.prodMk continuousAt_id)
    filter_upwards [htend.eventually hN] with y hy
    rw [latticeLift_eq_periodize]
    exact hy
  have hterm : ∀ n ∈ latticeBoxFinset N,
      (fun y => translate w n (t, y)) =ᶠ[𝓝 x] 0 := by
    intro n hn
    rw [← notMem_tsupport_iff_eventuallyEq]
    intro hxin
    have hsuppn : Function.support (fun y : Space => translate w n (t, y))
        ⊆ (fun y => y - lattice n) ⁻¹' C := by
      intro y hy
      have hyne : w (t, y - lattice n) ≠ 0 := hy
      exact hslice t (y - lattice n) hyne
    have hclosed : IsClosed ((fun y : Space => y - lattice n) ⁻¹' C) :=
      hCcompact.isClosed.preimage (continuous_id.sub continuous_const)
    have htsuppn : tsupport (fun y : Space => translate w n (t, y))
        ⊆ (fun y => y - lattice n) ⁻¹' C := closure_minimal hsuppn hclosed
    have hxin' := htsuppn hxin
    exact hxnot ⟨n, hxin'⟩
  have hzero : (fun y => ∑ n ∈ latticeBoxFinset N, translate w n (t, y)) =ᶠ[𝓝 x] 0 := by
    have hall : ∀ᶠ y in 𝓝 x, ∀ n ∈ latticeBoxFinset N, translate w n (t, y) = 0 :=
      (eventually_all_finset _).mpr (fun n hn => hterm n hn)
    filter_upwards [hall] with y hy
    simp only [Pi.zero_apply]
    exact Finset.sum_eq_zero hy
  exact absurd hx (notMem_tsupport_iff_eventuallyEq.mpr (hNs.trans hzero))

/-! ## 3. The cancellation datum for the physical correction -/

/-- `periodicSet` is monotone in its argument set. -/
theorem periodicSet_mono {S S' : Set Space} (h : S ⊆ S') : periodicSet S ⊆ periodicSet S' := by
  rintro x ⟨k, hk⟩
  exact ⟨k, h hk⟩

/-- The plateau of the origin cutoff sits inside the fixed reference ball. -/
theorem plateau_subset_ball {θ : Space → ℝ} {θRadius : ℝ} {O : Set Space}
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θRadius) (hθone : EqOn θ (fun _ => 1) O) :
    O ⊆ ball (0 : Space) θRadius := by
  intro y hy
  apply hθsupp
  apply subset_tsupport
  show θ y ≠ 0
  rw [hθone hy]; norm_num

/-- The cancellation datum of `correction_cancels` for the concrete physical
correction, with the scaled plateau `O = x₀ + ε•(θ-plateau)` on which `θ_ε = 1`
and `η_ε = 1`, and the packet-support bound obtained from
`periodicScaledPacket = latticeLift (scaledPacket)`, `parabolic_support` and
`latticeLift_sliceSupport_closed`. -/
theorem physicalCorrection_cancels {v U : SpaceTimeField} {x₀ : Space}
    {θ : Space → ℝ} {η : ℝ → ℝ} {K O : Set Space} {T r δ ε θRadius : ℝ}
    (hK : IsCompact K)
    (hcont : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ ball x₀ r, spatialDivergence v t x = 0)
    (hUsupp : ∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => U (t, x)) ⊆ K)
    (hOopen : IsOpen O) (hKO : K ⊆ O)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θRadius) (hθone : EqOn θ (fun _ => 1) O)
    (hηone : EqOn η (fun _ => 1) (Icc (-1 : ℝ) 1))
    (hεtime : 2 * ε ^ 2 < min T δ) (hεspace : ε * θRadius < r) (hε : 0 < ε)
    {t : ℝ} (ht : t ∈ Ico (T - ε ^ 2) T) :
    ∃ O' : Set Space, IsOpen O' ∧ O' ⊆ ball x₀ r ∧
      tsupport (fun x => periodicScaledPacket U x₀ T ε (t, x)) ⊆ periodicSet O' ∧
      ∀ x ∈ O', v (t, x) + physicalCorrection v x₀ T θ η ε (t, x) = 0 := by
  -- The scaled plateau, expressed as a preimage of the open plateau.
  have hOeq : spaceMap ε x₀ '' O = (fun x => ε⁻¹ • (x - x₀)) ⁻¹' O := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [spaceMap, mem_preimage, add_sub_cancel_left, smul_smul,
        inv_mul_cancel₀ hε.ne', one_smul]
      exact hy
    · intro hx
      exact ⟨ε⁻¹ • (x - x₀), hx, by
        simp only [spaceMap, smul_smul, mul_inv_cancel₀ hε.ne', one_smul]; abel⟩
  have hO'open : IsOpen (spaceMap ε x₀ '' O) := by
    rw [hOeq]; exact hOopen.preimage (by fun_prop)
  -- `O ⊆ ball 0 θRadius`, hence the scaled plateau sits in the chart ball.
  have hOball : O ⊆ ball (0 : Space) θRadius := plateau_subset_ball hθsupp hθone
  have hO'sub : spaceMap ε x₀ '' O ⊆ ball x₀ r := by
    rintro _ ⟨y, hy, rfl⟩
    have hyR : ‖y‖ < θRadius := by
      have := hOball hy; rwa [mem_ball, dist_zero_right] at this
    rw [mem_ball, dist_eq_norm]
    have hsub : spaceMap ε x₀ y - x₀ = ε • y := by simp only [spaceMap]; abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    exact lt_trans (mul_lt_mul_of_pos_left hyR hε) hεspace
  -- The rescaled compact packet-support set `Kε = x₀ + ε•K`.
  have hsc_eq : scaledSupport ε⁻¹ x₀ K = spaceMap ε x₀ '' K := by
    ext x; simp only [scaledSupport, spaceMap, Set.mem_image, inv_inv]
  have hKε_compact : IsCompact (spaceMap ε x₀ '' K) :=
    hK.image (by unfold spaceMap; fun_prop)
  have hKε_ball : spaceMap ε x₀ '' K ⊆ ball x₀ r := by
    rintro _ ⟨y, hy, rfl⟩
    have hyR : ‖y‖ < θRadius := by
      have := (hOball (hKO hy)); rwa [mem_ball, dist_zero_right] at this
    rw [mem_ball, dist_eq_norm]
    have hsub : spaceMap ε x₀ y - x₀ = ε • y := by simp only [spaceMap]; abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    exact lt_trans (mul_lt_mul_of_pos_left hyR hε) hεspace
  have hKε_O : spaceMap ε x₀ '' K ⊆ spaceMap ε x₀ '' O := Set.image_mono hKO
  -- Truncated packet `w'`, agreeing with the packet before `T`, with an
  -- all-time slice-support bound in `Kε`.
  set w' : SpaceTimeField := fun z =>
    if z.1 < T then
      parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀
        (zeroPastField U) z
    else 0 with hw'def
  have hslice_w' : ∀ (s : ℝ) (y : Space), w' (s, y) ≠ 0 → y ∈ spaceMap ε x₀ '' K := by
    intro s y hy
    have hsT : s < T := by
      by_contra h
      apply hy
      simp only [hw'def]
      exact if_neg h
    have hspacket : parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀
        (zeroPastField U) (s, y) ≠ 0 := by
      have hy' := hy
      simp only [hw'def] at hy'
      rwa [if_pos hsT] at hy'
    by_cases hs0 : s ≤ T - ε ^ 2
    · exact absurd (zeroPast_dilate_early U ε⁻¹ ((ε⁻¹) ^ 2) ε⁻¹ (T - ε ^ 2)
        (sq_nonneg _) x₀ hs0 y) hspacket
    · have hs0' : T - ε ^ 2 < s := lt_of_not_ge hs0
      have hspos : 0 < (ε⁻¹) ^ 2 * (s - (T - ε ^ 2)) :=
        mul_pos (pow_pos (inv_pos.mpr hε) 2) (by linarith)
      have hs1 : (ε⁻¹) ^ 2 * (s - (T - ε ^ 2)) < 1 := by
        have hkey : (ε⁻¹) ^ 2 * ε ^ 2 = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ hε.ne', one_pow]
        have hexpand : (ε⁻¹) ^ 2 * (s - (T - ε ^ 2))
            = (ε⁻¹) ^ 2 * (s - T) + (ε⁻¹) ^ 2 * ε ^ 2 := by ring
        rw [hexpand, hkey]
        have hneg : (ε⁻¹) ^ 2 * (s - T) < 0 :=
          mul_neg_of_pos_of_neg (pow_pos (inv_pos.mpr hε) 2) (by linarith)
        linarith
      have hsupp_s : tsupport (fun y => parabolicVelocity ε⁻¹
          (T - ε ^ 2) x₀ (zeroPastField U) (s, y))
            ⊆ spaceMap ε x₀ '' K := by
        rw [← hsc_eq]
        apply parabolic_support hK (inv_pos.mpr hε) x₀
        rw [funext (fun y => zeroPastField_of_pos U hspos y)]
        exact hUsupp _ ⟨hspos, hs1⟩
      exact hsupp_s (subset_tsupport _ hspacket)
  -- The periodic packet slice equals the truncated lift before `T`.
  have hpacket_eq : (fun x => periodicScaledPacket U x₀ T ε (t, x))
      = (fun x => latticeLift w' (t, x)) := by
    funext x
    refine tsum_congr (fun k => ?_)
    simp only [hw'def]
    exact (if_pos ht.2).symm
  have hpacket : tsupport (fun x => periodicScaledPacket U x₀ T ε (t, x))
      ⊆ periodicSet (spaceMap ε x₀ '' O) := by
    rw [hpacket_eq]
    exact (latticeLift_sliceSupport_closed hKε_compact hKε_ball hslice_w' t).trans
      (periodicSet_mono hKε_O)
  -- The cancellation on the scaled plateau, via the local curl identity.
  refine ⟨spaceMap ε x₀ '' O, hO'open, hO'sub, hpacket, ?_⟩
  intro x hx
  obtain ⟨z, hzO, rfl⟩ := hx
  have hηt : temporalCutoff η T ε t = 1 := by
    apply hηone
    change -1 ≤ (ε ^ 2)⁻¹ * (t - T) ∧ (ε ^ 2)⁻¹ * (t - T) ≤ 1
    have hp := sq_pos_of_pos hε
    rw [mul_comm, ← div_eq_mul_inv]
    refine ⟨(le_div_iff₀ hp).mpr ?_, (div_le_iff₀ hp).mpr ?_⟩
    · linarith [ht.1]
    · linarith [ht.2, hp.le]
  have hχnear : ∀ᶠ y in 𝓝 (spaceMap ε x₀ z),
      temporalCutoff η T ε t * spatialCutoff θ x₀ ε y = 1 := by
    have hA : Continuous (fun y : Space => ε⁻¹ • (y - x₀)) := by fun_prop
    have hAz : ε⁻¹ • (spaceMap ε x₀ z - x₀) ∈ O := by
      simpa only [spaceMap, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hε.ne',
        one_smul] using hzO
    filter_upwards [hA.continuousAt.preimage_mem_nhds (hOopen.mem_nhds hAz)] with y hy
    rw [hηt, one_mul]
    exact hθone hy
  have hxball : spaceMap ε x₀ z ∈ ball x₀ r := hO'sub ⟨z, hzO, rfl⟩
  have htIoo : t ∈ Ioo (0 : ℝ) (T + δ) := by
    have hεsq : 0 < ε ^ 2 := by positivity
    have hmin1 : min T δ ≤ T := min_le_left T δ
    have hδpos : 0 < δ := by nlinarith [hεtime, min_le_right T δ, hεsq]
    refine ⟨by nlinarith [ht.1, hεtime, hmin1, hεsq], by linarith [ht.2, hδpos]⟩
  have hW : physicalCorrection v x₀ T θ η ε (t, spaceMap ε x₀ z) = -v (t, spaceMap ε x₀ z) := by
    change -SpatialCurl.curl (fun y =>
      (temporalCutoff η T ε t * spatialCutoff θ x₀ ε y) • timePotential v x₀ (t, y))
        (spaceMap ε x₀ z) = -v (t, spaceMap ε x₀ z)
    rw [SpatialCurl.curl_cutoff_eq hχnear,
      spatialCurl_timePotential_on_ball hcont hdiv htIoo hxball]
  rw [hW]; abel

/-! ## 4. The assembled statement -/

/-- The construction data of `lem:potential`: the two Urysohn cutoffs `θ, η`
with the plateau `O`, the support radius `θR`, the threshold `ε₀`, the radial
potential `timePotential v x₀`, and the unit-periodic lift
`fun ε => latticeLift (physicalCorrection v x₀ T θ η ε)` of the concrete chart
correction.  This is the `CutoffData` witness assembled by `localPotential`. -/
def localPotentialData (v : SpaceTimeField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ) : CutoffData :=
  ⟨θ, η, O, θR, ε₀, timePotential v x₀,
    fun ε => latticeLift (physicalCorrection v x₀ T θ η ε)⟩

/-- The reconciled `LocalPotentialAPI` for `localPotentialData`, given the two
Urysohn cutoffs, the threshold, and the reference's local regularity /
periodicity / packet-support hypotheses.  The seven `correction_*` fields come
from `correction_fields_of_chart` with the concrete
`physicalCorrection v x₀ T θ η ε`; the three chart facts requiring a *global*
reference are supplied by the local-reference companions
`physicalCorrection_contDiff`/`physicalCorrection_divergence` and the
scaled-plateau datum `physicalCorrection_cancels`. -/
theorem localPotentialAPI (v U : SpaceTimeField) (K : Set Space) (x₀ : Space) (r T δ : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ)
    (hr2 : r < 1 / 2) (hK : IsCompact K) (hper : IsPeriodicOn univ v)
    (hcont : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ ball x₀ r, spatialDivergence v t x = 0)
    (hUsupp : ∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => U (t, x)) ⊆ K)
    (hθsm : ContDiff ℝ ∞ θ) (hθcs : HasCompactSupport θ)
    (hθrange : ∀ x, θ x ∈ Icc (0 : ℝ) 1) (hOopen : IsOpen O) (hKO : K ⊆ O)
    (hθone : EqOn θ (fun _ => 1) O) (hθRpos : 0 < θR)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsm : ContDiff ℝ ∞ η) (hηcs : HasCompactSupport η)
    (hηrange : ∀ t, η t ∈ Icc (0 : ℝ) 1) (hηone : EqOn η (fun _ => 1) (Icc (-1 : ℝ) 1))
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hε₀pos : 0 < ε₀) (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    LocalPotentialAPI v U K x₀ r T δ (localPotentialData v x₀ T θ η O θR ε₀) := by
  -- The seven canonical `correction_*` fields for the concrete correction.
  have hcorr := correction_fields_of_chart v U x₀ θ η (timePotential v x₀) r T ε₀ θR
    (fun ε => physicalCorrection v x₀ T θ η ε) hr2 hper hεspace
    (fun ε hε => physicalCorrection_contDiff hθsm hηsm hθcs hηcs hθsupp hηsupp hcont
      (hεtime ε hε) (hεspace ε hε) hε.1)
    (fun ε hε => physical_compact hε.1.ne' v x₀ T hθcs hηcs)
    (fun ε hε => physicalCorrection_divergence hθsm hηsm hθcs hηcs hθsupp hηsupp hcont
      (hεtime ε hε) (hεspace ε hε) hε.1)
    (fun ε hε => physical_support hε.1 v x₀ T hθcs hηcs hθsupp hηsupp)
    (fun ε _ t x _ => rfl)
    (fun ε hε t ht => physicalCorrection_cancels hK hcont hdiv hUsupp hOopen hKO
      hθsupp hθone hηone (hεtime ε hε) (hεspace ε hε) hε.1 ht)
  obtain ⟨hcf, hcs, hcp, hcd, hcsupp, hcsb, hcc⟩ := hcorr
  exact
    { theta_smooth := hθsm
      theta_compactSupport := hθcs
      theta_range := hθrange
      plateau_open := hOopen
      prescribed_subset_plateau := hKO
      theta_one := hθone
      theta_radius_pos := hθRpos
      theta_support := hθsupp
      eta_smooth := hηsm
      eta_compactSupport := hηcs
      eta_range := hηrange
      eta_one := hηone
      eta_support := hηsupp
      eps_pos := hε₀pos
      eps_time := hεtime
      eps_space := hεspace
      potential_smooth := timePotential_contDiffOn_ball isOpen_Ioo hcont
      potential_formula := fun t x => centeredPotential_eq_integral (fun y => v (t, y)) x₀ x
      potential_curl := fun t ht x hx => spatialCurl_timePotential_on_ball hcont hdiv ht hx
      correction_formula := hcf
      correction_smooth := hcs
      correction_periodic := hcp
      correction_divergence_free := hcd
      correction_support := hcsupp
      correction_support_ball := hcsb
      correction_cancels := hcc }

/-- **Lemma `lem:potential`** (`paper/sections/03-torus.tex:176-217`,
`research/T16/Spec.lean:328-336`): the general local divergence-free cutoff on the
three-torus, assembled as `⟨localPotentialData …, localPotentialAPI …⟩`. -/
theorem localPotential : localPotentialStatement := by
  intro v U K x₀ r T δ hr hr2 hT hδ hK hper hcont hdiv hUsupp
  obtain ⟨θR, θ, O, hθRpos, hθsm, hθcs, hθsupp, hOopen, hKO, hθone, hθrange⟩ :=
    exists_originCutoff hK
  obtain ⟨η, hηsm, hηcs, hηrange, hηone, hηsupp⟩ := exists_timeCutoff
  obtain ⟨ε₀, hε₀pos, hεtime, hεspace⟩ := exists_threshold hθRpos hr hT hδ
  exact ⟨localPotentialData v x₀ T θ η O θR ε₀,
    localPotentialAPI v U K x₀ r T δ θ η O θR ε₀ hr2 hK hper hcont hdiv hUsupp
      hθsm hθcs hθrange hOopen hKO hθone hθRpos hθsupp
      hηsm hηcs hηrange hηone hηsupp hε₀pos hεtime hεspace⟩

end NSFormalization.Section3.T16
