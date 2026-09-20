import NSFormalization.Section3.T17.ForceSupport
import NSFormalization.Section3.T11.Transport
import NSFormalization.Section3.T15.Scaling
import NSFormalization.Section3.T10.ForcePaths
import NSFormalization.Paper1.PeriodicCorrectionEndpointRates
import NSFormalization.Paper1.PeriodicForceEndpointScaling
import NSFormalization.Paper1.PeriodicForceConvergence
import NSFormalization.Paper1.PeriodicForceMeasurability
import NSFormalization.Paper1.PeriodicForceTimeInterpolation

/-! # T17 (`lem:correction`), unit U11: `eq:HHs`, the `L¹_t H^s_x` bound

The four canonical `CorrectionAPI` fields `sobolevConst`, `sobolevConst_pos`,
`forceSobolev_memLp` and `force_sobolev_bound`
(`research/T17/Spec.lean:944-960`, `Section3/T17/Correction.lean:262-282`) at
the concrete `correctionData` of unit U2, for `0 ≤ s ≤ 1`.
-/

noncomputable section

namespace NSFormalization.Section3.T17

open Set MeasureTheory Filter Metric
open NavierStokes NavierStokes.ProblemStatement
open NavierStokes.PeriodicLocalization (SupportedInCube periodize)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11.Transport (translatePeriodicDatum
  isPeriodicDatum_translate translatePeriodicDatum_norm)
open NSFormalization.Section3.T15 (MemForceSobolevT)
open NSFormalization.Section3.T16
open NSFormalization.Paper1.PeriodicForceConvergence (periodicVectorSobolevNorm)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField forceTimeMeasure)
open NSFormalization.Source (coordinateForce fourierSobolevNorm fourierSobolevNorm_translate)
open NSFormalization.Paper1.CorrectionProfile (physicalCorrection)
open NSFormalization.Paper1.CorrectionForceNorms (scalarPhysicalForce)
open NSFormalization.Paper1.PeriodicBridge (periodize_comp supported_comp)
open NSFormalization.Paper1.PeriodicCorrectionEndpointRates
  (correction_scalar_whole_endpoint_rates)
open NSFormalization.Paper1.PeriodicForceEndpointScaling
  (periodized_scalar_L1Hs_le_endpoint_product)
open scoped ContDiff ENNReal Topology BigOperators

/-! ## 0. The T10-datum / Paper1-Fourier-energy bridge at real order -/

/-- Real-order analogue of `T10.norm_scalar_datum_nat`: a component of the
order-`s` datum has Paper1's scalar periodic Sobolev norm. -/
theorem norm_scalar_datum_real (s : ℝ) {z : SpatialField} {A : PeriodicSobolev s}
    (hz : ContDiff ℝ ∞ z) (hA : IsPeriodicDatum s z A) (i : Fin 3) :
    ‖A.1 i‖ = NSFormalization.Paper1.periodicSobolevNorm s (fun x ↦ (z x i : ℂ)) := by
  have hc : ContDiff ℝ ∞ (fun x ↦ (z x i : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hz)
  have hp : NavierStokes.PeriodicIntegration.UnitPeriods (fun x ↦ (z x i : ℂ)) :=
    fun x j ↦ congrArg (fun y : Space ↦ (y i : ℂ)) (hA.1 x j)
  have he : A.1 i = NSFormalization.Paper1.smoothPeriodicWeightedFourierLp s
      (fun x ↦ (z x i : ℂ)) hc hp := by
    ext k
    simpa only [NSFormalization.Paper1.smoothPeriodicWeightedFourierLp,
      periodicFrequencyWeight_eq_paper1] using hA.2.2 i k
  rw [he, NSFormalization.Paper1.norm_smoothPeriodicWeightedFourierLp]

/-- Paper1's scalar Fourier energy is nonnegative at every real order. -/
theorem periodicSobolevSq_nonneg (s : ℝ) (f : Space → ℂ) :
    0 ≤ NSFormalization.Paper1.periodicSobolevSq s f := by
  unfold NSFormalization.Paper1.periodicSobolevSq
  exact tsum_nonneg (fun k ↦ mul_nonneg
    (Real.rpow_nonneg ((NSFormalization.Paper1.one_le_periodicFrequencyWeight k).trans'
      zero_le_one) s) (sq_nonneg _))

/-- The norm of the order-`s` datum of a smooth periodic field is the Euclidean
combination of the three Paper1 component energies. -/
theorem norm_datum_eq_sqrt (s : ℝ) {z : SpatialField} {A : PeriodicSobolev s}
    (hz : ContDiff ℝ ∞ z) (hA : IsPeriodicDatum s z A) :
    ‖A.1‖ = Real.sqrt (∑ i : Fin 3,
      NSFormalization.Paper1.periodicSobolevSq s (fun x ↦ (z x i : ℂ))) := by
  have hsum : (∑ i : Fin 3, NSFormalization.Paper1.periodicSobolevSq s
      (fun x ↦ (z x i : ℂ))) = ‖A.1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [norm_scalar_datum_real s hz hA i, NSFormalization.Paper1.periodicSobolevNorm,
      Real.sq_sqrt (periodicSobolevSq_nonneg s _)]
  rw [hsum, Real.sqrt_sq (norm_nonneg _)]

/-- The datum norm of a smooth periodic slice is Paper1's vector periodic
Sobolev norm of the space-time field. -/
theorem norm_datum_eq_vector (s : ℝ) {W : SpaceTimeField} {t : ℝ}
    {A : PeriodicSobolev s} (hz : ContDiff ℝ ∞ (fun x : Space ↦ W (t, x)))
    (hA : IsPeriodicDatum s (fun x : Space ↦ W (t, x)) A) :
    ‖A.1‖ = periodicVectorSobolevNorm s W t :=
  norm_datum_eq_sqrt s hz hA

/-- The T10 periodic Sobolev extended norm of a smooth periodic slice is the
`ENNReal` coercion of Paper1's vector periodic Sobolev norm. -/
theorem periodicSobolevENorm_slice_eq (s : ℝ) {W : SpaceTimeField}
    (hW : ContDiff ℝ ∞ W) (hp : IsPeriodicOn univ W) (t : ℝ) :
    periodicSobolevENorm s (fun x : Space ↦ W (t, x))
      = ENNReal.ofReal (periodicVectorSobolevNorm s W t) := by
  have hs : ContDiff ℝ ∞ (fun x : Space ↦ W (t, x)) :=
    hW.comp (contDiff_const.prodMk contDiff_id)
  have hper : IsPeriodicSpatial (fun x : Space ↦ W (t, x)) := fun x i ↦ hp t (mem_univ _) x i
  obtain ⟨A, hA⟩ := smooth_periodic_datum s hs hper
  rw [periodicSobolevENorm_eq hA, ← ofReal_norm]
  exact congrArg _ (norm_datum_eq_vector s hs hA)

/-- Spatial translation invariance of the T10 periodic Sobolev extended norm,
through T11's translated datum. -/
theorem periodicSobolevENorm_translate (s : ℝ) {z : SpatialField}
    (hz : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) (y : Space) :
    periodicSobolevENorm s (fun x ↦ z (x + y)) = periodicSobolevENorm s z := by
  obtain ⟨A, hA⟩ := smooth_periodic_datum s hz hp
  rw [periodicSobolevENorm_eq (isPeriodicDatum_translate hA y),
    periodicSobolevENorm_eq hA, ← ofReal_norm, ← ofReal_norm]
  exact congrArg _ (translatePeriodicDatum_norm s y A)

/-! ## 1. The order-`s` coefficient path of a torus test force (`s ≤ 1`) -/

/-- Monotonicity of the T10 datum norm in the order, for `s ≤ r`, through
Paper1's `periodicSobolevSq_mono_smooth`. -/
theorem norm_datum_mono {s r : ℝ} (hsr : s ≤ r) {z : SpatialField}
    {A : PeriodicSobolev s} {B : PeriodicSobolev r} (hz : ContDiff ℝ ∞ z)
    (hA : IsPeriodicDatum s z A) (hB : IsPeriodicDatum r z B) : ‖A.1‖ ≤ ‖B.1‖ := by
  rw [norm_datum_eq_sqrt s hz hA, norm_datum_eq_sqrt r hz hB]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ ↦ ?_)
  exact NSFormalization.Paper1.periodicSobolevSq_mono_smooth
    (Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hz))
    (fun x j ↦ congrArg (fun y : Space ↦ (y i : ℂ)) (hA.1 x j)) hsr

/-- Order-`s` analogue of `T10.force_coefficient_path` for `s ≤ 1`: the datum
path of a torus test force is continuous, compactly supported, strongly
measurable and Bochner-integrable.  Continuity comes from the order-`1` path
of `T10.continuous_datum_path` through `norm_datum_mono`. -/
theorem force_coefficient_path_real {f : SpaceTimeField} (hf : MemForceT f)
    {s : ℝ} (hs1 : s ≤ 1) :
    ∃ G : ℝ → PeriodicSobolev s,
      (∀ t, IsPeriodicDatum s (fun x ↦ f (t, x)) (G t)) ∧
      Continuous G ∧ HasCompactSupport G ∧ StronglyMeasurable G ∧
      IsPeriodicSobolevPath s f G ∧ MemLp G 1 forceTimeMeasure := by
  have hslice (t : ℝ) : ContDiff ℝ ∞ (fun x : Space ↦ f (t, x)) :=
    hf.1.comp (contDiff_const.prodMk contDiff_id)
  have hex (t : ℝ) := smooth_periodic_datum s (hslice t) (hf.2.1 t (mem_univ _))
  choose G hG using hex
  obtain ⟨G₁, hG₁, hc₁, _, _, _, _⟩ := force_coefficient_path hf 1
  have hc : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro t
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hone : Filter.Tendsto (fun u ↦ ‖G₁ u - G₁ t‖) (nhds t) (nhds 0) := by
      have := hc₁.continuousAt (x := t)
      rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero] at this
      exact this
    refine squeeze_zero (fun u ↦ norm_nonneg _) (fun u ↦ ?_) hone
    have hdiff : ContDiff ℝ ∞ (fun x : Space ↦ f (u, x) - f (t, x)) :=
      (hslice u).sub (hslice t)
    have hsub := datum_sub (hG u) (hG t)
    have hsub₁ := datum_sub (hG₁ u) (hG₁ t)
    have hle := norm_datum_mono (s := s) (r := ((1 : ℕ) : ℝ))
      (by exact_mod_cast hs1) hdiff hsub hsub₁
    change ‖(G u - G t).1‖ ≤ ‖(G₁ u - G₁ t).1‖
    exact hle
  obtain ⟨K, hK, _, hsupport⟩ := hf.2.2
  have hcompact : HasCompactSupport G := by
    apply HasCompactSupport.intro hK
    intro t ht
    have hz : (fun x ↦ f (t, x)) = 0 := by
      funext x
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      exact ht (hsupport hx).1
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    funext i
    apply lp.ext
    funext k
    have hd : IsPeriodicDatum s (fun x ↦ f (t, x)) (G t) := hG t
    rw [hz] at hd
    have hk := hd.2.2 i k
    simpa [periodicFourierCoeff, NSFormalization.Paper1.periodicFourierCoeff,
      UnitAddTorus.mFourierCoeff, NSFormalization.Paper1.torusLift] using hk
  have hm : StronglyMeasurable G := hc.stronglyMeasurable_of_hasCompactSupport hcompact
  exact ⟨G, hG, hc, hcompact, hm, fun t _ ↦ hG t,
    (hc.memLp_of_hasCompactSupport (μ := volume) (p := 1) hcompact).mono_measure
      Measure.restrict_le_self⟩

/-! ## 2. The single Euclidean copy recentred at the origin -/

/-- The Section 4 single-copy correction force, translated so that its chart
ball is centred at the spatial origin.  Recentring is needed because Paper1's
periodization machinery measures support in the **origin-centred** cube
`[-r,r]³` (`NavierStokes.PeriodicLocalization.SupportedInCube`), while the
chart ball of `place` sits inside `(0,1)³`. -/
def shiftedForce (ν : ℝ) (v : SpaceTimeField) (x₀ : Space) (T : ℝ) (θ : Space → ℝ)
    (η : ℝ → ℝ) (ε : ℝ) : SpaceTimeField :=
  fun z ↦ NSFormalization.Source.correctionForce ν v
    (NSFormalization.Paper1.CorrectionProfile.physicalCorrection v x₀ T θ η ε)
    (z.1, z.2 + x₀)

theorem shiftedForce_smooth (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (shiftedForce ν v x₀ T θ η ε) :=
  (NSFormalization.Paper1.CorrectionForceNorms.physicalForce_smooth ν hv x₀ T ε hθ hη).comp
    (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))

theorem shiftedForce_compact (ν : ℝ) (v : SpaceTimeField) (x₀ : Space) (T ε : ℝ)
    (hε : ε ≠ 0) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    HasCompactSupport (shiftedForce ν v x₀ T θ η ε) :=
  (NSFormalization.Paper1.CorrectionForceNorms.physicalForce_compact
      ν v x₀ T ε hε hθc hηc).comp_homeomorph
    ((Homeomorph.refl ℝ).prodCongr (Homeomorph.addRight x₀))

/-- The recentred copy is supported in the origin-centred cube of half-width
`ε·θR`, the exact hypothesis of Paper1's periodization estimates. -/
theorem shiftedForce_supportedInCube (ν : ℝ) (v : SpaceTimeField) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} {θR ε : ℝ} (hε : 0 < ε)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2) :
    SupportedInCube (ε * θR) (shiftedForce ν v x₀ T θ η ε) := by
  intro z hz i
  have hb := (source_force_tsupport ν v x₀ T hε hθc hηc hθsupp hηsupp
    (subset_tsupport _ hz)).2
  rw [mem_ball, dist_eq_norm, add_sub_cancel_right] at hb
  have hcoord : |z.2 i| ≤ ‖z.2‖ := by
    have := PiLp.norm_apply_le z.2 i
    rwa [Real.norm_eq_abs] at this
  linarith

/-- Periodizing the recentred copy is the spatial translate of the periodized
copy: the lattice sum commutes with a spatial translation. -/
theorem periodize_shiftedForce (ν : ℝ) (v : SpaceTimeField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (ε : ℝ) (z : SpaceTime) :
    periodize (shiftedForce ν v x₀ T θ η ε) z =
      periodize (NSFormalization.Source.correctionForce ν v
        (NSFormalization.Paper1.CorrectionProfile.physicalCorrection v x₀ T θ η ε))
        (z.1, z.2 + x₀) := by
  refine tsum_congr fun n ↦ ?_
  exact congrArg (fun y : Space ↦ NSFormalization.Source.correctionForce ν v
    (NSFormalization.Paper1.CorrectionProfile.physicalCorrection v x₀ T θ η ε) (z.1, y))
    (sub_add_eq_add_sub z.2 (NavierStokes.PeriodicLocalization.lattice n) x₀)

/-! ## 3. The Paper1 whole-space endpoint constants, fixed before the scale -/

/-- The `H⁰` endpoint constant of Paper1's
`correction_scalar_whole_endpoint_rates`, chosen before every scale. -/
def sobolevC0 (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3) : ℝ≥0∞ :=
  Classical.choose (correction_scalar_whole_endpoint_rates ν hv x₀ T hθ hη hθc hηc i)

/-- The `H¹` endpoint constant of the same Paper1 statement. -/
def sobolevC1 (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3) : ℝ≥0∞ :=
  Classical.choose (Classical.choose_spec
    (correction_scalar_whole_endpoint_rates ν hv x₀ T hθ hη hθc hηc i))

theorem sobolev_endpoint_spec (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3) :
    sobolevC0 ν hv x₀ T hθ hη hθc hηc i < (⊤ : ℝ≥0∞) ∧
      sobolevC1 ν hv x₀ T hθ hη hθc hηc i < (⊤ : ℝ≥0∞) ∧
      ∀ ε ∈ Ioc (0 : ℝ) 1,
        eLpNorm (fun t ↦ fourierSobolevNorm 0
            (fun x ↦ scalarPhysicalForce ν v x₀ T θ η i ε (t, x))) 1 volume ≤
          ENNReal.ofReal (ε ^ ((3 : ℝ) / 2)) * sobolevC0 ν hv x₀ T hθ hη hθc hηc i ∧
        eLpNorm (fun t ↦ fourierSobolevNorm 1
            (fun x ↦ scalarPhysicalForce ν v x₀ T θ η i ε (t, x))) 1 volume ≤
          ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * sobolevC1 ν hv x₀ T hθ hη hθc hηc i :=
  Classical.choose_spec (Classical.choose_spec
    (correction_scalar_whole_endpoint_rates ν hv x₀ T hθ hη hθc hηc i))

/-- `03-torus.tex:239-242`: the real Sobolev constants of `eq:HHs`, explicit in
Paper1's two endpoint profile constants. -/
def sobolevConst (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) : ℝ → ℝ :=
  fun s ↦ 1 + ∑ i : Fin 3,
    (sobolevC0 ν hv x₀ T hθ hη hθc hηc i).toReal ^ (1 - s) *
      (2 * Real.pi * (sobolevC1 ν hv x₀ T hθ hη hθc hηc i).toReal) ^ s

theorem sobolevConst_summand_nonneg (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (s : ℝ) (i : Fin 3) :
    0 ≤ (sobolevC0 ν hv x₀ T hθ hη hθc hηc i).toReal ^ (1 - s) *
      (2 * Real.pi * (sobolevC1 ν hv x₀ T hθ hη hθc hηc i).toReal) ^ s := by
  have h1 : (0 : ℝ) ≤ 2 * Real.pi * (sobolevC1 ν hv x₀ T hθ hη hθc hηc i).toReal :=
    mul_nonneg (by positivity) ENNReal.toReal_nonneg
  exact mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) (Real.rpow_nonneg h1 _)

/-- `03-torus.tex:239-242`: `C_s > 0` on the whole range `0 ≤ s ≤ 1`. -/
theorem sobolevConst_pos (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < sobolevConst ν hv x₀ T hθ hη hθc hηc s := by
  intro s _ _
  have hsum : (0 : ℝ) ≤ ∑ i : Fin 3,
      (sobolevC0 ν hv x₀ T hθ hη hθc hηc i).toReal ^ (1 - s) *
        (2 * Real.pi * (sobolevC1 ν hv x₀ T hθ hη hθc hηc i).toReal) ^ s :=
    Finset.sum_nonneg fun i _ ↦ sobolevConst_summand_nonneg ν hv x₀ T hθ hη hθc hηc s i
  unfold sobolevConst
  linarith

/-! ## 4. The scalar component estimate -/

/-- Paper1's whole-space endpoint norms are unchanged by the recentring. -/
theorem fourierSobolevNorm_shifted (ν : ℝ) (v : SpaceTimeField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (ε : ℝ) (σ : ℝ) (i : Fin 3) (t : ℝ) :
    fourierSobolevNorm σ
        (fun x ↦ coordinateForce (shiftedForce ν v x₀ T θ η ε) i (t, x)) =
      fourierSobolevNorm σ (fun x ↦ scalarPhysicalForce ν v x₀ T θ η i ε (t, x)) := by
  have h := fourierSobolevNorm_translate σ
    (fun y : Space ↦ scalarPhysicalForce ν v x₀ T θ η i ε (t, y)) (-x₀)
  simp only [sub_neg_eq_add] at h
  exact h

/-- **Per component.**  The periodized recentred copy has the `L¹_tH^s_x` bound
`ε^{3/2-s}·c₀^{1-s}·(2π c₁)^s` on the whole admissible range `0 ≤ s ≤ 1`:
Paper1's `periodized_scalar_L1Hs_le_endpoint_product` (single copy in the
origin cube) fed by `correction_scalar_whole_endpoint_rates`. -/
theorem component_L1Hs_bound (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {θR ε : ℝ} (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hε : ε ∈ Ioc (0 : ℝ) 1) (hcube : ε * θR < 1 / 2)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (i : Fin 3) :
    eLpNorm (fun t ↦ NSFormalization.Paper1.periodicSobolevNorm s
        (fun x ↦ coordinateForce (periodize (shiftedForce ν v x₀ T θ η ε)) i (t, x)))
        1 volume ≤
      ENNReal.ofReal (ε ^ ((3 : ℝ) / 2 - s) *
        ((sobolevC0 ν hv x₀ T hθ hη hθc hηc i).toReal ^ (1 - s) *
          (2 * Real.pi * (sobolevC1 ν hv x₀ T hθ hη hθc hηc i).toReal) ^ s)) := by
  have hε0 : (0 : ℝ) < ε := hε.1
  set c0 : ℝ := (sobolevC0 ν hv x₀ T hθ hη hθc hηc i).toReal with hc0def
  set c1 : ℝ := (sobolevC1 ν hv x₀ T hθ hη hθc hηc i).toReal with hc1def
  have hc0 : (0 : ℝ) ≤ c0 := ENNReal.toReal_nonneg
  have hc1 : (0 : ℝ) ≤ c1 := ENNReal.toReal_nonneg
  obtain ⟨hC0top, hC1top, hrates⟩ := sobolev_endpoint_spec ν hv x₀ T hθ hη hθc hηc i
  obtain ⟨hrate0, hrate1⟩ := hrates ε hε
  -- the recentred single copy and its Paper1 hypotheses
  have hSsf : SupportedInCube (ε * θR) (shiftedForce ν v x₀ T θ η ε) :=
    shiftedForce_supportedInCube ν v x₀ T hε0 hθc hηc hθsupp hηsupp
  have hSi : SupportedInCube (ε * θR)
      (coordinateForce (shiftedForce ν v x₀ T θ η ε) i) :=
    supported_comp hSsf (fun w : Space ↦ ((w i : ℝ) : ℂ)) (by simp)
  have hFi : ContDiff ℝ ∞ (coordinateForce (shiftedForce ν v x₀ T θ η ε) i) :=
    NSFormalization.Source.coordinateForce_smooth
      (shiftedForce_smooth ν hv x₀ T ε hθ hη) i
  have hCi : HasCompactSupport (coordinateForce (shiftedForce ν v x₀ T θ η ε) i) :=
    NSFormalization.Source.coordinateForce_compact
      (shiftedForce_compact ν v x₀ T ε (ne_of_gt hε0) hθc hηc) i
  have hcoord : (fun z ↦ coordinateForce (periodize (shiftedForce ν v x₀ T θ η ε)) i z) =
      periodize (coordinateForce (shiftedForce ν v x₀ T θ η ε) i) :=
    periodize_comp hSsf hcube (fun w : Space ↦ ((w i : ℝ) : ℂ)) (by simp)
  have hslice : (fun t ↦ NSFormalization.Paper1.periodicSobolevNorm s
        (fun x ↦ coordinateForce (periodize (shiftedForce ν v x₀ T θ η ε)) i (t, x))) =
      fun t ↦ NSFormalization.Paper1.periodicSobolevNorm s
        (fun x ↦ periodize (coordinateForce (shiftedForce ν v x₀ T θ η ε) i) (t, x)) := by
    funext t
    exact congrArg (NSFormalization.Paper1.periodicSobolevNorm s)
      (funext fun x ↦ congrFun hcoord (t, x))
  rw [hslice]
  -- Paper1's endpoint interpolation for the periodized single copy
  refine (periodized_scalar_L1Hs_le_endpoint_product hSi hcube hFi hCi hs0 hs1).trans ?_
  simp only [fourierSobolevNorm_shifted ν v x₀ T θ η ε]
  refine le_trans (mul_le_mul'
    (ENNReal.rpow_le_rpow hrate0 (by linarith))
    (ENNReal.rpow_le_rpow (mul_le_mul' (le_refl (ENNReal.ofReal (2 * Real.pi))) hrate1)
      hs0)) (le_of_eq ?_)
  -- pure `ℝ≥0∞` arithmetic: collapse both factors to one `ENNReal.ofReal`
  rw [← ENNReal.ofReal_toReal hC0top.ne, ← ENNReal.ofReal_toReal hC1top.ne,
    ← hc0def, ← hc1def, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith : (0:ℝ) ≤ 1 - s),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hs0,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hstep1 : (ε ^ ((3 : ℝ) / 2) * c0) ^ (1 - s)
      = ε ^ ((3 : ℝ) / 2 * (1 - s)) * c0 ^ (1 - s) := by
    rw [Real.mul_rpow (by positivity) hc0, ← Real.rpow_mul hε0.le]
  have hstep2 : (2 * Real.pi * (ε ^ ((1 : ℝ) / 2) * c1)) ^ s
      = ε ^ ((1 : ℝ) / 2 * s) * (2 * Real.pi * c1) ^ s := by
    rw [show 2 * Real.pi * (ε ^ ((1 : ℝ) / 2) * c1)
        = ε ^ ((1 : ℝ) / 2) * (2 * Real.pi * c1) by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hε0.le]
  rw [hstep1, hstep2, show (3 : ℝ) / 2 - s = (3 : ℝ) / 2 * (1 - s) + (1 : ℝ) / 2 * s by ring,
    Real.rpow_add hε0]
  ring

/-! ## 5. From the datum path to the periodized vector norm -/

/-- The honest `L¹_tH^s_x` path of a torus test force `F`, together with the
comparison of `forceSobolevENormT` with Paper1's vector periodic Sobolev norm
of any spatial translate `W` of `F`. -/
theorem forceSobolevENormT_le_of_translate {s : ℝ} (hs1 : s ≤ 1) {F W : SpaceTimeField}
    (hF : MemForceT F) (hW : ContDiff ℝ ∞ W) (hWper : IsPeriodicOn univ W)
    (y : Space) (hWF : ∀ (t : ℝ) (x : Space), W (t, x) = F (t, x + y)) :
    forceSobolevENormT 1 s F ≤ eLpNorm (periodicVectorSobolevNorm s W) 1 volume ∧
      MemForceSobolevT 1 s F := by
  obtain ⟨G, hG, _, _, hmeas, hpath, hLp⟩ := force_coefficient_path_real hF hs1
  refine ⟨?_, ⟨G, hpath, hLp⟩⟩
  have hkey : ∀ t : ℝ, ‖G t‖ₑ = ENNReal.ofReal (periodicVectorSobolevNorm s W t) := by
    intro t
    have h1 : periodicSobolevENorm s (fun x ↦ F (t, x)) = ‖G t‖ₑ :=
      periodicSobolevENorm_eq (hG t)
    have hslice : (fun x : Space ↦ W (t, x)) =
        fun x : Space ↦ (fun z : Space ↦ F (t, z)) (x + y) := funext (hWF t)
    have h2 : periodicSobolevENorm s (fun x : Space ↦ W (t, x))
        = periodicSobolevENorm s (fun x : Space ↦ F (t, x)) := by
      rw [hslice]
      exact periodicSobolevENorm_translate s
        (hF.1.comp (contDiff_const.prodMk contDiff_id))
        (fun x i ↦ hF.2.1 t (mem_univ _) x i) y
    rw [← h1, ← h2, periodicSobolevENorm_slice_eq s hW hWper t]
  calc forceSobolevENormT 1 s F ≤ eLpNorm G 1 forceTimeMeasure :=
        iInf_le_of_le ⟨G, hpath, hmeas.aestronglyMeasurable⟩ le_rfl
    _ = ∫⁻ t, ‖G t‖ₑ ∂forceTimeMeasure := eLpNorm_one_eq_lintegral_enorm
    _ = ∫⁻ t, ENNReal.ofReal (periodicVectorSobolevNorm s W t) ∂forceTimeMeasure :=
        lintegral_congr hkey
    _ ≤ ∫⁻ t, ENNReal.ofReal (periodicVectorSobolevNorm s W t) ∂volume :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = eLpNorm (periodicVectorSobolevNorm s W) 1 volume :=
        (NSFormalization.Paper1.PeriodicForceTimeInterpolation.eLpNorm_one_eq_lintegral_ofReal_of_nonneg
          (fun _ ↦ Real.sqrt_nonneg _)).symm

/-! ## 6. The two canonical `CorrectionAPI` fields at the concrete data -/

/-- **U11** — `03-torus.tex:239-242,284`, equation `eq:HHs`.  Both canonical
fields at the concrete `correctionData` of unit U2: the honest
`MemForceSobolevT 1 s` datum path of the periodized correction force, and the
`L¹_tH^s_x` estimate with the `ε`-independent constant
`sobolevConst ν hv x₀ T hθ hη hθc hηc s` on the whole range `0 ≤ s ≤ 1`.

`hv` is the documented G1 premise (`research/T17/SPEC_ISSUES.md`), exactly as in
units U3–U7: Paper1's `correction_scalar_whole_endpoint_rates` and
`physicalForce_smooth` need global smoothness of the reference, and `force_eq`
needs it on the chart cylinder.  `hε₀ : ε₀ ≤ 1` is the same normalization lane
385's `force_derivative_bound` already carries; at assembly it comes from
`eps_le_placement` together with `PlacementData.eps_le_one`. -/
theorem forceSobolev_memLp_and_bound (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hε₀ : ε₀ ≤ 1)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
        MemForceSobolevT 1 s
            (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) ∧
          forceSobolevENormT 1 s
              (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) ≤
            ENNReal.ofReal (sobolevConst ν hv x₀ T hθ hη hθc hηc s *
              (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s))) := by
  intro s hs0 hs1 ε hε
  have hε0 : (0 : ℝ) < ε := hε.1
  have hεIoc : ε ∈ Ioc (0 : ℝ) 1 := ⟨hε.1, hε.2.trans hε₀⟩
  have hρ : ε * θR < r := hεspace ε hε
  have hcube : ε * θR < 1 / 2 := lt_trans hρ hr2
  -- the periodized force, its `MemForceT` data
  have hFsm := force_smooth ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp
    hr2 hεtime hεspace ε hε
  have hFper := force_periodic ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp
    hr2 hεtime hεspace ε hε
  have hFsupp := force_support ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp
    hr2 hεtime hεspace ε hε
  have hTpos : (0 : ℝ) < T - 2 * ε ^ 2 := by
    have h1 := hεtime ε hε
    have h2 : min T δ ≤ T := min_le_left T δ
    linarith
  have hFmem : MemForceT (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) :=
    ⟨hFsm, hFper, Icc (T - 2 * ε ^ 2) (T + 2 * ε ^ 2), isCompact_Icc,
      fun t ht ↦ lt_of_lt_of_le hTpos ht.1,
      fun z hz ↦ ⟨Ioo_subset_Icc_self (hFsupp hz).1, mem_univ _⟩⟩
  -- the recentred single copy and its periodization
  have hforce := force_eq (ν := ν) (v := v) (x₀ := x₀) (T := T)
    (δ := δ) (r := r) (θ := θ) (η := η) (O := O) (θR := θR)
    (ε₀ := ε₀) (ε := ε) hvper hv.contDiffOn hθ hη hθc hηc hθsupp hηsupp hr2
    hε.1 hρ (hεtime ε hε)
  have hSsf : SupportedInCube (ε * θR) (shiftedForce ν v x₀ T θ η ε) :=
    shiftedForce_supportedInCube ν v x₀ T hε0 hθc hηc hθsupp hηsupp
  have hWsm : ContDiff ℝ ∞ (periodize (shiftedForce ν v x₀ T θ η ε)) :=
    NavierStokes.PeriodicLocalization.contDiff_periodize hSsf
      (shiftedForce_smooth ν hv x₀ T ε hθ hη)
  have hWper : IsPeriodicOn univ (periodize (shiftedForce ν v x₀ T θ η ε)) :=
    latticeLift_periodic (shiftedForce ν v x₀ T θ η ε)
  have hWF : ∀ (t : ℝ) (x : Space),
      periodize (shiftedForce ν v x₀ T θ η ε) (t, x) =
        correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε (t, x + x₀) := by
    intro t x
    rw [hforce]
    exact periodize_shiftedForce ν v x₀ T θ η ε (t, x)
  obtain ⟨hbound, hmemLp⟩ :=
    forceSobolevENormT_le_of_translate hs1 hFmem hWsm hWper x₀ hWF
  refine ⟨hmemLp, hbound.trans ?_⟩
  -- component-by-component Paper1 estimate
  have hmeas : ∀ i : Fin 3, AEStronglyMeasurable
      (fun t ↦ NSFormalization.Paper1.periodicSobolevNorm s
        (fun x ↦ coordinateForce (periodize (shiftedForce ν v x₀ T θ η ε)) i (t, x)))
      volume := fun i ↦
    (NSFormalization.Paper1.stronglyMeasurable_periodicSobolevNorm_time s
      (NSFormalization.Source.coordinateForce_smooth hWsm i).continuous).aestronglyMeasurable
  have hK : ∀ i : Fin 3, 0 ≤
      (sobolevC0 ν hv x₀ T hθ hη hθc hηc i).toReal ^ (1 - s) *
        (2 * Real.pi * (sobolevC1 ν hv x₀ T hθ hη hθc hηc i).toReal) ^ s :=
    fun i ↦ sobolevConst_summand_nonneg ν hv x₀ T hθ hη hθc hηc s i
  calc eLpNorm (periodicVectorSobolevNorm s
          (periodize (shiftedForce ν v x₀ T θ η ε))) 1 volume
      ≤ ∑ i : Fin 3, eLpNorm (fun t ↦ NSFormalization.Paper1.periodicSobolevNorm s
          (fun x ↦ coordinateForce (periodize (shiftedForce ν v x₀ T θ η ε)) i (t, x)))
          1 volume :=
        NSFormalization.Paper1.PeriodicForceConvergence.eLpNorm_periodicVectorSobolevNorm_le_sum
          hmeas
    _ ≤ ∑ i : Fin 3, ENNReal.ofReal (ε ^ ((3 : ℝ) / 2 - s) *
          ((sobolevC0 ν hv x₀ T hθ hη hθc hηc i).toReal ^ (1 - s) *
            (2 * Real.pi * (sobolevC1 ν hv x₀ T hθ hη hθc hηc i).toReal) ^ s)) :=
        Finset.sum_le_sum fun i _ ↦ component_L1Hs_bound ν hv x₀ T hθ hη hθc hηc
          hθsupp hηsupp hεIoc hcube hs0 hs1 i
    _ = ENNReal.ofReal (∑ i : Fin 3, ε ^ ((3 : ℝ) / 2 - s) *
          ((sobolevC0 ν hv x₀ T hθ hη hθc hηc i).toReal ^ (1 - s) *
            (2 * Real.pi * (sobolevC1 ν hv x₀ T hθ hη hθc hηc i).toReal) ^ s)) :=
        (ENNReal.ofReal_sum_of_nonneg
          (fun i _ ↦ mul_nonneg (Real.rpow_nonneg hε0.le _) (hK i))).symm
    _ ≤ ENNReal.ofReal (sobolevConst ν hv x₀ T hθ hη hθc hηc s *
          (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        have hSnn : (0 : ℝ) ≤ ∑ i : Fin 3,
            (sobolevC0 ν hv x₀ T hθ hη hθc hηc i).toReal ^ (1 - s) *
              (2 * Real.pi * (sobolevC1 ν hv x₀ T hθ hη hθc hηc i).toReal) ^ s :=
          Finset.sum_nonneg fun i _ ↦ hK i
        have hA : (0 : ℝ) < ε ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hε0 _
        have hB : (0 : ℝ) < ε ^ ((3 : ℝ) / 2 - s) := Real.rpow_pos_of_pos hε0 _
        unfold sobolevConst
        nlinarith [hSnn, hA, hB]

/-- **U11 (a)** — `CorrectionAPI.forceSobolev_memLp`
(`Section3/T17/Correction.lean:271-273`), verbatim at the concrete data. -/
theorem forceSobolev_memLp (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hε₀ : ε₀ ≤ 1)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
        MemForceSobolevT 1 s
          (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) :=
  fun s hs0 hs1 ε hε ↦ (forceSobolev_memLp_and_bound ν hv x₀ T δ r hvper O θR ε₀
    hθ hη hθc hηc hθsupp hηsupp hr2 hε₀ hεtime hεspace s hs0 hs1 ε hε).1

/-- **U11 (b)** — `CorrectionAPI.force_sobolev_bound`
(`Section3/T17/Correction.lean:276-282`), equation `eq:HHs`, verbatim at the
concrete data with the constant `sobolevConst ν hv x₀ T hθ hη hθc hηc`. -/
theorem force_sobolev_bound (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hε₀ : ε₀ ≤ 1)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
        forceSobolevENormT 1 s
            (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) ≤
          ENNReal.ofReal
            (sobolevConst ν hv x₀ T hθ hη hθc hηc s *
              (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s))) :=
  fun s hs0 hs1 ε hε ↦ (forceSobolev_memLp_and_bound ν hv x₀ T δ r hvper O θR ε₀
    hθ hη hθc hηc hθsupp hηsupp hr2 hε₀ hεtime hεspace s hs0 hs1 ε hε).2

end NSFormalization.Section3.T17
