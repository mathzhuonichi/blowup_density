import NSFormalization.Section3.T16.Assembly
import NSFormalization.Section3.T15.Bridges
import NSFormalization.Source.Insertion
import NSFormalization.Source.LocalizedInsertion

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

/-- Actual raw data: one radial potential and the un-periodised curl correction. -/
def localCorrectionData (v : SpaceTimeField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ) : CutoffData :=
  ⟨θ, η, O, θR, ε₀, timePotential v x₀,
    fun ε => physicalCorrection v x₀ T θ η ε⟩

/-- The proved local construction core. Force estimates and the I02/I03 matching
record are separate remaining obligations, not fields assumed by this record. -/
structure LocalCorrectionCore (v U : SpaceTimeField) (K : Set Space)
    (x₀ : Space) (r T δ : ℝ) (D : CutoffData) : Prop where
  theta_smooth : ContDiff ℝ ∞ D.θ
  theta_compactSupport : HasCompactSupport D.θ
  theta_range : ∀ x, D.θ x ∈ Icc (0 : ℝ) 1
  plateau_open : IsOpen D.plateau
  prescribed_subset_plateau : K ⊆ D.plateau
  theta_one : EqOn D.θ (fun _ => 1) D.plateau
  theta_radius_pos : 0 < D.θRadius
  theta_support : tsupport D.θ ⊆ ball (0 : Space) D.θRadius
  eta_smooth : ContDiff ℝ ∞ D.η
  eta_compactSupport : HasCompactSupport D.η
  eta_range : ∀ t, D.η t ∈ Icc (0 : ℝ) 1
  eta_one : EqOn D.η (fun _ => 1) (Icc (-1 : ℝ) 1)
  eta_support : tsupport D.η ⊆ Ioo (-2 : ℝ) 2
  eps_pos : 0 < D.ε₀
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, 2 * ε ^ 2 < min T δ
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ε * D.θRadius < r
  potential_smooth : ContDiffOn ℝ ∞ D.potential
    (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r)
  potential_formula : ∀ t x, D.potential (t, x) =
    ∫ ρ in (0 : ℝ)..1,
      ρ • NSFormalization.Paper1.RadialPotential.cross
        (v (t, x₀ + ρ • (x - x₀))) (x - x₀)
  potential_curl : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ ball x₀ r,
    SpatialCurl.curl (fun y => D.potential (t, y)) x = v (t, x)
  correction_formula : ∀ ε t x, D.correction ε (t, x) =
    -SpatialCurl.curl (fun y =>
      (temporalCutoff D.η T ε t * spatialCutoff D.θ x₀ ε y) • D.potential (t, y)) x
  correction_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ContDiff ℝ ∞ (D.correction ε)
  correction_divergence_free : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t x,
    spatialDivergence (D.correction ε) t x = 0
  correction_compactSupport : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    HasCompactSupport (D.correction ε)
  correction_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (D.correction ε) ⊆
      Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ ball x₀ (ε * D.θRadius)
  correction_cancels : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t ∈ Ico (T - ε ^ 2) T,
    ∃ O : Set Space, IsOpen O ∧ O ⊆ ball x₀ r ∧
      tsupport (fun x => scaledVelocity U x₀ T ε (t, x)) ⊆ O ∧
      ∀ x ∈ O, v (t, x) + D.correction ε (t, x) = 0
  crossTransport_background_advects_packet : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDerivative (scaledVelocity U x₀ T ε) t x
        (NSFormalization.Section3.T16.correctedBackground v D.correction ε (t, x)) = 0
  crossTransport_packet_advects_background : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDerivative (NSFormalization.Section3.T16.correctedBackground v D.correction ε) t x
        (scaledVelocity U x₀ T ε (t, x)) = 0

/-- Choose both cutoffs and a single positive threshold from the actual local
reference and compact packet carrier. No periodicity, global regularity,
placement record, correction record, or conclusion-shaped input is required. -/
theorem exists_localCorrectionCore (v U : SpaceTimeField) (K : Set Space)
    (x₀ : Space) (r T δ : ℝ) (hr : 0 < r) (hT : 0 < T) (hδ : 0 < δ)
    (hK : IsCompact K)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ ball x₀ r,
      spatialDivergence v t x = 0)
    (hU : ∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => U (t, x)) ⊆ K) :
    ∃ D : CutoffData, LocalCorrectionCore v U K x₀ r T δ D := by
  obtain ⟨R, θ, O, hR, hθ, hθc, hθs, hO, hKO, hθone, hθrange⟩ :=
    NSFormalization.Section3.T16.exists_originCutoff hK
  obtain ⟨η, hη, hηc, hηrange, hηone, hηs⟩ :=
    NSFormalization.Section3.T16.exists_timeCutoff
  obtain ⟨ε₀, hε₀, ht, hs⟩ := NSFormalization.Section3.T16.exists_threshold hR hr hT hδ
  refine ⟨localCorrectionData v x₀ T θ η O R ε₀, ?_⟩
  exact {
    theta_smooth := hθ
    theta_compactSupport := hθc
    theta_range := hθrange
    plateau_open := hO
    prescribed_subset_plateau := hKO
    theta_one := hθone
    theta_radius_pos := hR
    theta_support := hθs
    eta_smooth := hη
    eta_compactSupport := hηc
    eta_range := hηrange
    eta_one := hηone
    eta_support := hηs
    eps_pos := hε₀
    eps_time := ht
    eps_space := hs
    potential_smooth := NSFormalization.Section3.T16.timePotential_contDiffOn_ball isOpen_Ioo hv
    potential_formula := fun t x =>
      NSFormalization.Paper1.RadialPotential.centeredPotential_eq_integral (fun y => v (t, y)) x₀ x
    potential_curl := fun _ ht _ hx => spatialCurl_timePotential_on_ball hv hdiv ht hx
    correction_formula := fun _ _ _ => rfl
    correction_smooth := fun ε hε => NSFormalization.Section3.T16.physicalCorrection_contDiff
      hθ hη hθc hηc hθs hηs hv (ht ε hε) (hs ε hε) hε.1
    correction_divergence_free := fun ε hε =>
      NSFormalization.Section3.T16.physicalCorrection_divergence
        hθ hη hθc hηc hθs hηs hv (ht ε hε) (hs ε hε) hε.1
    correction_compactSupport := fun _ hε =>
      NSFormalization.Source.PhysicalRemoval.physical_compact hε.1.ne' v x₀ T hθc hηc
    correction_support := fun _ hε =>
      NSFormalization.Source.PhysicalRemoval.physical_support hε.1 v x₀ T hθc hηc hθs hηs
    correction_cancels := fun ε hε _ ht' => physicalCorrection_cancels_packet hK hv hdiv hU
      hO hKO hθs hθone hηone (ht ε hε) (hs ε hε) hε.1 ht'
    crossTransport_background_advects_packet := fun ε hε _ ht' x =>
      (crossTransport_pair hK hv hdiv hU hO hKO hθs hθone hηone
        (ht ε hε) (hs ε hε) hε.1 ht' x).1
    crossTransport_packet_advects_background := fun ε hε _ ht' x =>
      (crossTransport_pair hK hv hdiv hU hO hKO hθs hθone hηone
        (ht ε hε) (hs ε hε) hε.1 ht' x).2 }

/-- The force formula, copied in the summand order of the reconciled Spec. -/
def correctionForce (ν : ℝ) (v : SpaceTimeField) (D : CutoffData) (ε : ℝ) :
    SpaceTimeField :=
  fun z =>
    temporalDerivative (D.correction ε) z.1 z.2 -
      ν • spatialLaplacian (D.correction ε) z.1 z.2 +
      spatialDerivative (D.correction ε) z.1 z.2 (v z) +
      spatialDerivative v z.1 z.2 (D.correction ε z) +
      advection (D.correction ε) z.1 z.2


/-- The Spec and supplier differ only in the order of the two cross summands. -/
theorem correctionForce_eq_source (ν : ℝ) (v : SpaceTimeField) (D : CutoffData) (ε : ℝ) :
    correctionForce ν v D ε = NSFormalization.Source.correctionForce ν v (D.correction ε) := by
  funext z
  simp only [correctionForce, NSFormalization.Source.correctionForce]
  abel

/-- The force never sees arbitrary exterior values of the reference: outside
correction support, all correction jets and reference-dependent terms vanish. -/
theorem force_support (ν : ℝ) (v : SpaceTimeField) (D : CutoffData) (ε : ℝ) :
    tsupport (correctionForce ν v D ε) ⊆ tsupport (D.correction ε) := by
  rw [correctionForce_eq_source]
  exact NSFormalization.Source.LocalizedInsertion.correctionForce_support ν v (D.correction ε)

/-- A change of reference outside an open neighbourhood of the actual
correction support leaves the force unchanged, without exterior regularity. -/
theorem correctionForce_eq_of_open_agreement (ν : ℝ) (v V : SpaceTimeField)
    (D : CutoffData) (ε : ℝ) {O : Set SpaceTime} (hO : IsOpen O)
    (hs : tsupport (D.correction ε) ⊆ O) (heq : EqOn v V O) :
    correctionForce ν v D ε = correctionForce ν V D ε := by
  funext z
  by_cases hz : z ∈ O
  · have he : v =ᶠ[𝓝 z] V := by
      filter_upwards [hO.mem_nhds hz] with y hy using heq hy
    have hd := NavierStokes.ResidualRegularity.spatialDerivative_congr he
    simp only [correctionForce, heq hz, hd]
  · have hn : z ∉ tsupport (D.correction ε) := fun h => hz (hs h)
    rw [correctionForce_eq_source, correctionForce_eq_source,
      NSFormalization.Source.LocalizedInsertion.correctionForce_eq_zero_outside ν v (D.correction ε) hn,
      NSFormalization.Source.LocalizedInsertion.correctionForce_eq_zero_outside ν V (D.correction ε) hn]

end NSFormalization.Section3.T23
