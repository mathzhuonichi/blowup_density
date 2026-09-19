import NSFormalization.Section3.T16.Assembly
import NSFormalization.Section3.T15.Bridges
import NSFormalization.Source.Insertion

/-! Raw, un-periodised local correction vocabulary for T23.
The seven fields are copied verbatim from research/T23/Spec.lean.
No placement record or contract is imported. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set Filter
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff Topology

structure CutoffData where
  /-- Spatial cutoff from the Urysohn construction;
  `paper/sections/03-torus.tex:167-172,181`.

  Non-vacuity: this is a concrete real-valued function on physical space. -/
  θ : Space → ℝ
  /-- Temporal cutoff used in `eq:cutoff`;
  `paper/sections/03-torus.tex:173-174,182-186`.

  Non-vacuity: this is a concrete real-valued function of physical time. -/
  η : ℝ → ℝ
  /-- Open plateau on which `θ` is one;
  `paper/sections/03-torus.tex:172,181`.

  Non-vacuity: the set is retained as data and is constrained below to contain
  the prescribed compact set. -/
  plateau : Set Space
  /-- Fixed support radius for `θ`;
  `paper/sections/03-torus.tex:168-172,212`.

  Non-vacuity: the API requires this actual real radius to be strictly
  positive and to bound `tsupport θ`. -/
  θRadius : ℝ
  /-- Common upper threshold for every sufficiently small `ε`;
  `paper/sections/03-torus.tex:188,212`.

  Non-vacuity: the API requires one strictly positive threshold shared by all
  scale-dependent conclusions. -/
  ε₀ : ℝ
  /-- Radial vector potential `A` from `eq:potential`;
  `paper/sections/03-torus.tex:177-181`.

  Non-vacuity: this is a concrete time-first spacetime vector field whose
  formula and curl are fixed below. -/
  potential : SpaceTimeField
  /-- Scale-indexed correction family `w_ε` from `eq:cutoff`;
  `paper/sections/03-torus.tex:183-193`.

  Non-vacuity: this is one concrete family shared by smoothness, periodicity,
  support, divergence, and cancellation fields. -/
  correction : ℝ → SpaceTimeField


open NSFormalization.Section3.T15 (scaledVelocity scaledSourcePoint scaledStartTime)

/-- The un-periodised packet vanishes on the entire slice before activation,
including the endpoint. No smoothness or packet hypotheses are needed. -/
theorem packet_slice_zero (U : VelocityField) (x₀ : Space) (T ε t : ℝ)
    (ht : t ≤ T - ε ^ 2) :
    (fun y : Space => scaledVelocity U x₀ T ε (t, y)) = fun _ => 0 := by
  funext y
  have hnonpos : (ε⁻¹) ^ 2 * (t - scaledStartTime T ε) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
    exact sub_nonpos.mpr ht
  simp only [scaledVelocity, NSFormalization.Source.PacketScaling.zeroPastField,
    scaledSourcePoint]
  simp only [not_lt.mpr hnonpos, ite_false, smul_zero]

open Metric MeasureTheory
open NSFormalization.Section3.T16 (plateau_subset_ball spatialCurl_timePotential_on_ball)
open NSFormalization.Paper1.RadialPotential (timePotential)
open NSFormalization.Paper1.CorrectionProfile (physicalCorrection temporalCutoff spatialCutoff)
open NSFormalization.Source.PhysicalRemoval (spaceMap)
open NSFormalization.Source (parabolicVelocity)
open NSFormalization.Source.PacketScaling (scaledSupport parabolic_support
  zeroPast_dilate_early zeroPastField_of_pos zeroPastField)

/-- Open-neighbourhood cancellation for the actual un-periodised packet,
using only local smoothness and local divergence of the reference. -/
theorem physicalCorrection_cancels_packet {v U : SpaceTimeField} {x₀ : Space}
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
      tsupport (fun x => scaledVelocity U x₀ T ε (t, x)) ⊆ O' ∧
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
      exact ite_eq_right h
    have hspacket : parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀
        (zeroPastField U) (s, y) ≠ 0 := by
      have hy' := hy
      simp only [hw'def] at hy'
      rwa [ite_eq_left hsT] at hy'
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
  have hpacket : tsupport (fun x => scaledVelocity U x₀ T ε (t, x))
      ⊆ spaceMap ε x₀ '' O := by
    apply (closure_minimal ?_ hKε_compact.isClosed).trans hKε_O
    intro y hy
    apply hslice_w' t y
    change scaledVelocity U x₀ T ε (t, y) ≠ 0 at hy
    simpa only [hw'def, ite_eq_left ht.2, scaledVelocity, scaledSourcePoint,
      scaledStartTime, parabolicVelocity, NSFormalization.Source.dilateField] using hy
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

/-- Both cross transports vanish globally on `[0,T)`, including the inactive initial slice. -/
theorem crossTransport_pair {v U : SpaceTimeField} {x₀ : Space}
    {θ : Space → ℝ} {η : ℝ → ℝ} {K O : Set Space} {T r δ ε θRadius : ℝ}
    (hK : IsCompact K)
    (hcont : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ ball x₀ r, spatialDivergence v t x = 0)
    (hUsupp : ∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => U (t, x)) ⊆ K)
    (hOopen : IsOpen O) (hKO : K ⊆ O)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θRadius) (hθone : EqOn θ (fun _ => 1) O)
    (hηone : EqOn η (fun _ => 1) (Icc (-1 : ℝ) 1))
    (hεtime : 2 * ε ^ 2 < min T δ) (hεspace : ε * θRadius < r) (hε : 0 < ε)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (x : Space) :
    spatialDerivative (scaledVelocity U x₀ T ε) t x
        (v (t, x) + physicalCorrection v x₀ T θ η ε (t, x)) = 0 ∧
      spatialDerivative (fun z => v z + physicalCorrection v x₀ T θ η ε z) t x
        (scaledVelocity U x₀ T ε (t, x)) = 0 := by
  by_cases hstart : t ≤ T - ε ^ 2
  · have hz := packet_slice_zero U x₀ T ε t hstart
    have hd : spatialDerivative (scaledVelocity U x₀ T ε) t x = 0 := by
      simp only [spatialDerivative, hz]
      simp
    have hval := congrFun hz x
    exact ⟨by rw [hd]; simp, by rw [hval]; exact map_zero _⟩
  · obtain ⟨O', hO', _, hsupp, hzero⟩ := physicalCorrection_cancels_packet hK
      hcont hdiv hUsupp hOopen hKO hθsupp hθone hηone hεtime hεspace hε
      ⟨(lt_of_not_ge hstart).le, ht.2⟩
    have hremove : ∀ y ∈ tsupport (fun z => scaledVelocity U x₀ T ε (t, z)),
        ∀ᶠ z in 𝓝 y, v (t, z) + physicalCorrection v x₀ T θ η ε (t, z) = 0 := by
      intro y hy
      filter_upwards [hO'.mem_nhds (hsupp hy)] with z hz using hzero z hz
    exact (NSFormalization.Source.cross_advection_eq_zero
      (fun z => v z + physicalCorrection v x₀ T θ η ε z)
      (scaledVelocity U x₀ T ε) t hremove x).symm

end NSFormalization.Section3.T23
