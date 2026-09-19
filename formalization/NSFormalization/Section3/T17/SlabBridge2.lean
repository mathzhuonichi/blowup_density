import NSFormalization.Section3.T17.SlabBridge

/-! T17 U13 continuation: global periodicity remains an input, whereas reference
smoothness is needed only on the open classical slab. A time cutoff supplies
an auxiliary globally smooth reference. The actual data retain the radial
potential of the original reference at every time. Global equalities of the
admissible correction and force families transfer all 45 API fields. -/

noncomputable section
namespace NSFormalization.Section3.T17
open Set MeasureTheory Metric Filter
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Paper1.CorrectionProfile (physicalCorrection temporalCutoff spatialCutoff)
open NSFormalization.Paper1.RadialPotential (timePotential)
open scoped ContDiff Topology

def correctionStatementSlab' : Prop :=
  ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (place : PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ),
    0 < ν → 0 < r → r < 1 / 2 → 0 < δ → IsPeriodicOn univ v →
    ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (place.T + δ) ×ˢ (univ : Set Space)) →
    (∀ t ∈ Ioo (0 : ℝ) (place.T + δ), ∀ x ∈ ball place.x₀ r,
      spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t, x)) ⊆ K) →
    ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius →
    ∃ D : CutoffData, LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧
      Nonempty (CorrectionAPI ν place v r δ D)

/-- A time cutoff preserves spatial periodicity and divergence, and makes a
slab-smooth reference globally smooth without changing its middle slices. -/
theorem exists_slab_extension {v : SpaceTimeField} {T δ r : ℝ} {x₀ : Space}
    (hT : 0 < T) (hδ : 0 < δ) (hper : IsPeriodicOn univ v)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Space)))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ ball x₀ r,
      spatialDivergence v t x = 0) :
    ∃ V : SpaceTimeField, ContDiff ℝ ∞ V ∧ IsPeriodicOn univ V ∧
      (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ ball x₀ r,
        spatialDivergence V t x = 0) ∧
      (∀ t, |t - T| ≤ min T δ / 2 → ∀ x, V (t, x) = v (t, x)) := by
  let m := min T δ
  have hm : 0 < m := lt_min hT hδ
  let χ : ContDiffBump T := ⟨m / 2, 3 * m / 4, by positivity, by linarith⟩
  let V : SpaceTimeField := fun z => χ z.1 • v z
  have hc : ContDiff ℝ ∞ (fun z : SpaceTime => χ z.1) := χ.contDiff.comp contDiff_fst
  have hs : tsupport (fun z : SpaceTime => χ z.1) ⊆
      Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Space) := by
    have hs' : tsupport (fun z : SpaceTime => χ z.1) ⊆
        Prod.fst ⁻¹' closedBall T (3 * m / 4) := by
      apply closure_minimal
      · intro z hz
        have hz' : z.1 ∈ tsupport (χ : ℝ → ℝ) := subset_tsupport _ hz
        rwa [χ.tsupport_eq] at hz'
      · exact isClosed_closedBall.preimage continuous_fst
    intro z hz
    have hz' := hs' hz
    change dist z.1 T ≤ 3 * m / 4 at hz'
    rw [Real.dist_eq, abs_le] at hz'
    have hmT : m ≤ T := min_le_left _ _
    have hmδ : m ≤ δ := min_le_right _ _
    exact ⟨⟨by linarith [hz'.1], by linarith [hz'.2]⟩, mem_univ _⟩
  refine ⟨V, contDiff_cutoffSmul_of_ballSmooth isOpen_Ioo isOpen_univ hv hc hs,
    ?_, ?_, ?_⟩
  · intro t ht x i
    change χ t • v (t, x + coordinateVector i) = χ t • v (t, x)
    rw [hper t ht x i]
  · intro t ht x hx
    have hvs : ContDiff ℝ ∞ (fun y : Space => v (t, y)) :=
      hv.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun y => ⟨ht, mem_univ y⟩)
    have hd := (hvs.differentiable (by simp)) x
    have he : spatialDerivative V t x = χ t • spatialDerivative v t x := by
      exact fderiv_const_smul hd (χ t)
    simp only [spatialDivergence, he, smul_apply, PiLp.smul_apply,
      smul_eq_mul, ← Finset.mul_sum]
    change χ t * spatialDivergence v t x = 0
    rw [hdiv t ht x hx, mul_zero]
  · intro t ht x
    change χ t • v (t, x) = v (t, x)
    rw [χ.one_of_mem_closedBall, one_smul]
    exact ht


/-- Physical corrections only read reference slices where the time cutoff is nonzero. -/
theorem physicalCorrection_eq_of_slices {v V : SpaceTimeField} {x₀ : Space}
    {T ε : ℝ} {θ : Space → ℝ} {η : ℝ → ℝ}
    (heq : ∀ t, temporalCutoff η T ε t ≠ 0 → ∀ x, v (t, x) = V (t, x)) :
    physicalCorrection v x₀ T θ η ε = physicalCorrection V x₀ T θ η ε := by
  have hinner : (fun z : SpaceTime =>
      (temporalCutoff η T ε z.1 * spatialCutoff θ x₀ ε z.2) • timePotential v x₀ z) =
      (fun z : SpaceTime =>
      (temporalCutoff η T ε z.1 * spatialCutoff θ x₀ ε z.2) • timePotential V x₀ z) := by
    funext z
    by_cases h : temporalCutoff η T ε z.1 = 0
    · simp [h]
    · have hs : (fun x => v (z.1, x)) = (fun x => V (z.1, x)) := funext (heq z.1 h)
      simp only [timePotential, hs]
  unfold physicalCorrection NSFormalization.Paper1.localCorrection
  rw [hinner]

/-- Global profile equality, including slices outside the cutoff support. -/
theorem correctionProfile_eq_of_slices {v V : SpaceTimeField} {x₀ : Space}
    {T ε : ℝ} {D E : CutoffData} (hθ : D.θ = E.θ) (hη : D.η = E.η)
    (heq : ∀ σ, D.η σ ≠ 0 → ∀ x,
      v (T + ε ^ 2 * σ, x) = V (T + ε ^ 2 * σ, x)) :
    rescaledCorrectionProfile v x₀ T ε D = rescaledCorrectionProfile V x₀ T ε E := by
  funext z
  unfold rescaledCorrectionProfile
  congr 2
  funext y
  by_cases h : D.η z.1 = 0
  · simp [← hη, h]
  · have hp : rescaledPotential v x₀ T ε (z.1, y) =
        rescaledPotential V x₀ T ε (z.1, y) := by
      unfold rescaledPotential
      congr 1
      funext ρ
      rw [heq z.1 h]
    rw [hp, hθ, hη]

/-- Reference changes outside a time-supported correction do not affect the force. -/
theorem correctionForce_eq_of_slices {v V : SpaceTimeField} {D E : CutoffData}
    {ε ν : ℝ} {I : Set ℝ} (hw : D.correction ε = E.correction ε)
    (hs : tsupport (D.correction ε) ⊆ I ×ˢ (univ : Set Space))
    (heq : ∀ t ∈ I, ∀ x, v (t, x) = V (t, x)) :
    correctionForce ν v D ε = correctionForce ν V E ε := by
  funext z
  by_cases ht : z.1 ∈ I
  · have hv : (fun x => v (z.1, x)) = (fun x => V (z.1, x)) := funext (heq z.1 ht)
    simp only [correctionForce, ← hw, spatialDerivative, heq z.1 ht]
  · have hz : ∀ x, D.correction ε (z.1, x) = 0 := by
      intro x
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => ht (hs h).1
    have hd : spatialDerivative (D.correction ε) z.1 z.2 = 0 := by
      simp [spatialDerivative, funext hz]
    simp only [correctionForce, ← hw, hd, hz, zero_apply,
      map_zero]


/-- The force profile also transfers globally; outside the time support the
reference-dependent terms vanish, even for a nonsmooth reference. -/
theorem forceProfile_eq_of_slices {v V : SpaceTimeField} {D E : CutoffData}
    {ν T ε : ℝ} {x₀ : Space}
    (hw : rescaledCorrectionProfile v x₀ T ε D = rescaledCorrectionProfile V x₀ T ε E)
    (hs : tsupport (rescaledCorrectionProfile V x₀ T ε E) ⊆ fixedProfileCylinder E)
    (heq : ∀ σ ∈ Icc (-2 : ℝ) 2, ∀ x,
      v (T + ε ^ 2 * σ, x) = V (T + ε ^ 2 * σ, x)) :
    rescaledForceProfile ν v x₀ T ε D = rescaledForceProfile ν V x₀ T ε E := by
  funext z
  by_cases ht : z.1 ∈ Icc (-2 : ℝ) 2
  · simp only [rescaledForceProfile, hw, rescaledReference, spatialDerivative, heq z.1 ht]
  · have hz : ∀ x, rescaledCorrectionProfile V x₀ T ε E (z.1, x) = 0 := by
      intro x
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => ht (hs h).1
    have hd : spatialDerivative (rescaledCorrectionProfile V x₀ T ε E) z.1 z.2 = 0 := by
      simp [spatialDerivative, funext hz]
    simp only [rescaledForceProfile, hw, hd, hz, zero_apply, map_zero]

/-- Rescaled cylinder times lie in the physical correction window. -/
theorem chart_time_mem_window (T ε σ : ℝ) (hσ : σ ∈ Icc (-2 : ℝ) 2) :
    |(T + ε ^ 2 * σ) - T| ≤ 2 * ε ^ 2 := by
  rw [abs_le]
  have h1 := mul_le_mul_of_nonneg_left hσ.1 (sq_nonneg ε)
  have h2 := mul_le_mul_of_nonneg_left hσ.2 (sq_nonneg ε)
  constructor <;> nlinarith

/-- On the fixed cylinder the rescaled reference reads only window slices. -/
theorem rescaledReference_eqOn_of_slices {v V : SpaceTimeField} {x₀ : Space}
    {T ε : ℝ} (D : CutoffData)
    (heq : ∀ t, |t - T| ≤ 2 * ε ^ 2 → ∀ x, v (t, x) = V (t, x)) :
    EqOn (rescaledReference v x₀ T ε) (rescaledReference V x₀ T ε)
      (fixedProfileCylinder D) := by
  intro z hz
  exact heq _ (chart_time_mem_window _ _ _ hz.1) _

/-- A nonzero scaled cutoff forces its time into the physical window. -/
theorem temporalCutoff_time_mem_window {η : ℝ → ℝ} {T ε t : ℝ}
    (hε : 0 < ε) (hs : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (ht : temporalCutoff η T ε t ≠ 0) : |t - T| ≤ 2 * ε ^ 2 := by
  have h := hs (subset_tsupport η ht)
  change -2 < (ε ^ 2)⁻¹ * (t - T) ∧ (ε ^ 2)⁻¹ * (t - T) < 2 at h
  have hp : 0 < ε ^ 2 := sq_pos_of_pos hε
  rw [← div_eq_inv_mul, lt_div_iff₀ hp, div_lt_iff₀ hp] at h
  rw [abs_le]
  constructor <;> nlinarith [h.1, h.2]


/-- The correction block with global periodicity and only open-slab smoothness. -/
theorem correctionStatementSlab'_holds : correctionStatementSlab' := by
  intro ν u p f K place v r δ hν hr hr2 hδ hper hv hdiv hsupp hball
  obtain ⟨V, hV, hVper, hVdiv, hVeq⟩ :=
    exists_slab_extension place.time_pos hδ hper hv hdiv
  obtain ⟨θR, θ, O, hθR, hθ, hθc, hθsupp, hO, hKO, hθone, hθrange⟩ :=
    exists_originCutoff place.Kstar_compact
  obtain ⟨η, hη, hηc, hηrange, hηone, hηsupp⟩ := exists_timeCutoff
  obtain ⟨ε₁, hε₁, ht, hs⟩ := exists_threshold hθR hr
    (half_pos place.time_pos) (half_pos hδ)
  let ε₀ := min ε₁ place.ε₀
  have hε₀ : 0 < ε₀ := lt_min hε₁ place.eps_pos
  have htimeHalf : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min place.T δ / 2 := by
    intro ε hε
    simpa only [min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)] using
      ht ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have htime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min place.T δ := by
    intro ε hε
    have hm : 0 < min place.T δ := lt_min place.time_pos hδ
    linarith [htimeHalf ε hε]
  have hspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r :=
    fun ε hε => hs ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  let D := correctionData v place.x₀ place.T θ η O θR ε₀
  let E := correctionData V place.x₀ place.T θ η O θR ε₀
  have hpot : LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D :=
    localPotentialAPI v u place.Kstar place.x₀ r place.T δ θ η O θR ε₀
      hr2 place.Kstar_compact hper (hv.mono (prod_mono Subset.rfl (subset_univ _))) hdiv
      (fun t ht => (hsupp t ht).trans place.carrier_subset)
      hθ hθc hθrange hO hKO hθone hθR hθsupp hη hηc hηrange hηone hηsupp
      hε₀ htime hspace
  have hpotV : LocalPotentialAPI V u place.Kstar place.x₀ r place.T δ E :=
    localPotentialAPI V u place.Kstar place.x₀ r place.T δ θ η O θR ε₀
      hr2 place.Kstar_compact hVper hV.contDiffOn hVdiv
      (fun t ht => (hsupp t ht).trans place.carrier_subset)
      hθ hθc hθrange hO hKO hθone hθR hθsupp hη hηc hηrange hηone hηsupp
      hε₀ htime hspace
  let A : CorrectionAPI ν place V r δ E :=
    correctionAPI_of_smooth ν place hV r δ hν hr hr2 hVper hball θ η O θR ε₀ hpotV
      (min_le_right _ _)
  have heq : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t, |t - place.T| ≤ 2 * ε ^ 2 →
      ∀ x, v (t, x) = V (t, x) := by
    intro ε hε t ht x
    exact (hVeq t (ht.trans (htimeHalf ε hε).le) x).symm
  have hW : ∀ ε ∈ Ioc (0 : ℝ) ε₀, D.correction ε = E.correction ε := by
    intro ε hε
    apply congrArg latticeLift
    apply physicalCorrection_eq_of_slices
    intro t ht x
    exact heq ε hε t (temporalCutoff_time_mem_window hε.1 hηsupp ht) x
  have hF : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      correctionForce ν v D ε = correctionForce ν V E ε := by
    intro ε hε
    apply correctionForce_eq_of_slices (hW ε hε) (hpot.correction_support ε hε)
    intro t ht x
    apply heq ε hε t _ x
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hP : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      rescaledCorrectionProfile v place.x₀ place.T ε D =
        rescaledCorrectionProfile V place.x₀ place.T ε E := by
    intro ε hε
    apply correctionProfile_eq_of_slices rfl rfl
    intro σ hσ x
    have hσ' := hηsupp (subset_tsupport η hσ)
    exact heq ε hε _ (chart_time_mem_window _ _ _ ⟨hσ'.1.le, hσ'.2.le⟩) x
  have hQ : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      rescaledForceProfile ν v place.x₀ place.T ε D =
        rescaledForceProfile ν V place.x₀ place.T ε E := by
    intro ε hε
    apply forceProfile_eq_of_slices (hP ε hε) (A.correction_profile_support ε hε)
    intro σ hσ x
    exact heq ε hε _ (chart_time_mem_window _ _ _ hσ) x
  have hC : fixedProfileCylinder D = fixedProfileCylinder E := rfl
  have hR : D.θRadius = E.θRadius := rfl
  refine ⟨D, hpot, ⟨?_⟩⟩
  exact {
    potential := hpot
    localization := A.localization
    viscosity_pos := A.viscosity_pos
    radius_pos := A.radius_pos
    ball_in_chart := A.ball_in_chart
    eps_le_placement := A.eps_le_placement
    reference_periodic := hper
    correction_profile_smooth := by
      intro ε hε
      simpa only [hC, hP ε hε] using A.correction_profile_smooth ε hε
    correction_profile_support := by
      intro ε hε
      simpa only [hC, hP ε hε] using A.correction_profile_support ε hε
    correctionProfileConst := A.correctionProfileConst
    correctionProfileConst_nonneg := A.correctionProfileConst_nonneg
    correction_profile_uniform := by
      intro k ε hε
      simpa only [hC, hP ε hε] using A.correction_profile_uniform k ε hε
    force_profile_smooth := by
      intro ε hε
      simpa only [hC, hQ ε hε] using A.force_profile_smooth ε hε
    force_profile_support := by
      intro ε hε
      simpa only [hC, hQ ε hε] using A.force_profile_support ε hε
    forceProfileConst := A.forceProfileConst
    forceProfileConst_nonneg := A.forceProfileConst_nonneg
    force_profile_uniform := by
      intro k ε hε
      simpa only [hC, hQ ε hε] using A.force_profile_uniform k ε hε
    correction_profile_identity := by
      intro ε hε
      simpa only [hC, hW ε hε, hP ε hε] using A.correction_profile_identity ε hε
    force_profile_identity := by
      intro ε hε
      simpa only [hC, hF ε hε, hQ ε hε] using A.force_profile_identity ε hε
    force_smooth := by
      intro ε hε
      simpa only [hF ε hε] using A.force_smooth ε hε
    force_periodic := by
      intro ε hε
      simpa only [hF ε hε] using A.force_periodic ε hε
    force_support := by
      intro ε hε
      simpa only [hR, hF ε hε] using A.force_support ε hε
    spatialVolumeConst := A.spatialVolumeConst
    spatialVolumeConst_nonneg := A.spatialVolumeConst_nonneg
    force_spatial_volume := by
      intro ε hε
      simpa only [hF ε hε] using A.force_spatial_volume ε hε
    force_time_length := by
      intro ε hε
      simpa only [hF ε hε] using A.force_time_length ε hε
    correctionDerivConst := A.correctionDerivConst
    correctionDerivConst_nonneg := A.correctionDerivConst_nonneg
    correction_derivative_bound := by
      intro j m ε hε
      simpa only [hW ε hε] using A.correction_derivative_bound j m ε hε
    forceDerivConst := A.forceDerivConst
    forceDerivConst_nonneg := A.forceDerivConst_nonneg
    force_derivative_bound := by
      intro m ε hε
      simpa only [hF ε hε] using A.force_derivative_bound m ε hε
    correction_slice_memLp := by
      intro ε hε
      simpa only [hW ε hε] using A.correction_slice_memLp ε hε
    correction_gradient_memLp := by
      intro ε hε
      simpa only [hW ε hε] using A.correction_gradient_memLp ε hε
    energyConst := A.energyConst
    energyConst_nonneg := A.energyConst_nonneg
    correction_energy_bound := by
      intro ε hε
      simpa only [hW ε hε] using A.correction_energy_bound ε hε
    force_spatial_memLp := by
      intro p inst ε hε
      simpa only [hF ε hε] using A.force_spatial_memLp p ε hε
    mixedConst := A.mixedConst
    mixedConst_nonneg := A.mixedConst_nonneg
    force_mixed_bound := by
      intro p q inst hq ε hε
      simpa only [hF ε hε] using A.force_mixed_bound p q hq ε hε
    sobolevConst := A.sobolevConst
    sobolevConst_pos := A.sobolevConst_pos
    forceSobolev_memLp := by
      intro s hs0 hs1 ε hε
      simpa only [hF ε hε] using A.forceSobolev_memLp s hs0 hs1 ε hε
    force_sobolev_bound := by
      intro s hs0 hs1 ε hε
      simpa only [hF ε hε] using A.force_sobolev_bound s hs0 hs1 ε hε
  }

end NSFormalization.Section3.T17
