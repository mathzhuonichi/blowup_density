import NSFormalization.Paper1.LocalCutoff
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Smooth rescaled correction profiles, including the zero-scale limit. -/
noncomputable section
namespace NSFormalization.Paper1.CorrectionProfile
open NavierStokes NavierStokes.ProblemStatement Set MeasureTheory
open scoped ContDiff

abbrev Parameter := ℝ × SpaceTime

def spatialInclusion : Space →L[ℝ] Parameter :=
  (ContinuousLinearMap.inr ℝ ℝ SpaceTime).comp (ContinuousLinearMap.inr ℝ ℝ Space)

def rescaledReference (v : VelocityField) (x₀ : Space) (T ε : ℝ) : VelocityField :=
  fun z => v (T + ε ^ 2 * z.1, x₀ + ε • z.2)

def jointPotential (v : VelocityField) (x₀ : Space) (T : ℝ) (p : Parameter) : Space :=
  ∫ r in (0 : ℝ)..1,
    r • RadialPotential.cross (v (T + p.1 ^ 2 * p.2.1, x₀ + p.1 • (r • p.2.2))) p.2.2

def cutPotential (v : VelocityField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (p : Parameter) : Space :=
  (η p.2.1 * θ p.2.2) • jointPotential v x₀ T p

def profile (v : VelocityField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (p : Parameter) : Space :=
  -SpatialCurl.curlLinear ((fderiv ℝ (cutPotential v x₀ T θ η) p).comp spatialInclusion)

theorem jointPotential_smooth {v : VelocityField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T : ℝ) :
    ContDiff ℝ ∞ (jointPotential v x₀ T) := by
  let F : Parameter × ℝ → Space := fun p =>
    p.2 • RadialPotential.cross
      (v (T + p.1.1 ^ 2 * p.1.2.1, x₀ + p.1.1 • (p.2 • p.1.2.2))) p.1.2.2
  have harg : ContDiff ℝ ∞ (fun p : Parameter × ℝ =>
      (T + p.1.1 ^ 2 * p.1.2.1, x₀ + p.1.1 • (p.2 • p.1.2.2))) := by fun_prop
  have hF : ContDiff ℝ ∞ F := contDiff_snd.smul
    (RadialPotential.cross_contDiff (hv.comp harg) contDiff_fst.snd.snd)
  exact EulerCompactParameterIntegral.integral_contDiff 0 1 (by norm_num) F hF

theorem cutPotential_smooth {v : VelocityField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (cutPotential v x₀ T θ η) :=
  ((hη.comp contDiff_snd.fst).mul (hθ.comp contDiff_snd.snd)).smul
    (jointPotential_smooth hv x₀ T)

/-- Every fixed-order derivative stays smooth at ε=0: the rescaled formula
contains no inverse powers of ε. -/
theorem profile_smooth {v : VelocityField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (profile v x₀ T θ η) :=
  (SpatialCurl.curlLinear.contDiff.comp
    (((cutPotential_smooth hv x₀ T hθ hη).fderiv_right (m := ∞) (by simp)).clm_comp
      contDiff_const)).neg

theorem jointPotential_slice (v : VelocityField) (x₀ : Space) (T ε σ : ℝ) (z : Space) :
    jointPotential v x₀ T (ε, σ, z) =
      RadialPotential.timePotential (rescaledReference v x₀ T ε) 0 (σ, z) := by
  simp only [jointPotential, RadialPotential.timePotential, RadialPotential.centeredPotential,
    RadialPotential.potential, RadialPotential.integrand, rescaledReference, zero_add, sub_zero]

/-- The profile is the actual cutoff correction of the rescaled reference. -/
theorem profile_eq_localCorrection {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε σ : ℝ) (z : Space)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) :
    profile v x₀ T θ η (ε, σ, z) = localCorrection (rescaledReference v x₀ T ε) 0 θ η (σ, z) := by
  have hF := cutPotential_smooth hv x₀ T hθ hη
  have hin : HasFDerivAt (fun y : Space => (ε, σ, y)) spatialInclusion z := by
    exact (hasFDerivAt_const (𝕜 := ℝ) ε z).prodMk
      ((hasFDerivAt_const (𝕜 := ℝ) σ z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z))
  have hd := ((hF.differentiable (by simp)) (ε, σ, z)).hasFDerivAt.comp z hin
  have heq : (fun y : Space => cutPotential v x₀ T θ η (ε, σ, y)) =
      (fun y => (η σ * θ y) • RadialPotential.timePotential (rescaledReference v x₀ T ε) 0 (σ, y)) := by
    funext y
    rw [cutPotential, jointPotential_slice]
  change -SpatialCurl.curlLinear _ = -SpatialCurl.curlLinear _
  rw [← hd.fderiv]
  congr 2
  exact congrArg (fun f : Space → Space => fderiv ℝ f z) heq

/-- Uniform bounds on all full derivatives over a fixed compact rescaled
cylinder and ε∈[0,1], obtained from actual joint smoothness. -/
theorem profile_uniform_derivative_bound {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) (k : ℕ)
    {K : Set SpaceTime} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Icc (0 : ℝ) 1, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ k (profile v x₀ T θ η) (ε, z)‖ ≤ C := by
  have hc : Continuous (iteratedFDeriv ℝ k (profile v x₀ T θ η)) :=
    (profile_smooth hv x₀ T hθ hη).continuous_iteratedFDeriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro ε hε z hz
  exact (hC (ε, z) ⟨hε, hz⟩).trans (le_max_left _ _)

/-- The cross product is linear in the coordinate displacement. -/
theorem cross_smul_right (a b : Space) (c : ℝ) :
    RadialPotential.cross a (c • b) = c • RadialPotential.cross a b := by
  ext i
  fin_cases i <;> simp [RadialPotential.cross, coordinateVector] <;> ring

/-- The radial potential has exactly one spatial amplitude factor. -/
theorem timePotential_rescale (v : VelocityField) (x₀ : Space) (T ε σ : ℝ) (z : Space) :
    RadialPotential.timePotential v x₀ (T + ε ^ 2 * σ, x₀ + ε • z) =
      ε • jointPotential v x₀ T (ε, σ, z) := by
  have hx : x₀ + ε • z - x₀ = ε • z := by abel
  simp only [RadialPotential.timePotential, RadialPotential.centeredPotential,
    RadialPotential.potential, RadialPotential.integrand, hx, jointPotential]
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro r _
  simp only [smul_comm r ε z, cross_smul_right, smul_comm r ε]

/-- Curl under a forward affine spatial rescaling. -/
theorem curl_affine_scaling {A : Space → Space} (hA : ContDiff ℝ ∞ A)
    (x₀ : Space) (ε : ℝ) (z : Space) :
    SpatialCurl.curl (fun y => A (x₀ + ε • y)) z =
      ε • SpatialCurl.curl A (x₀ + ε • z) := by
  have hin := (hasFDerivAt_const (𝕜 := ℝ) x₀ z).add ((hasFDerivAt_id z).const_smul ε)
  have hd := ((hA.differentiable (by simp)) (x₀ + ε • z)).hasFDerivAt.comp z hin
  change HasFDerivAt (fun y => A (x₀ + ε • y)) _ z at hd
  unfold SpatialCurl.curl
  rw [hd.fderiv]
  have heq : (fderiv ℝ A (x₀ + ε • z)).comp
      (0 + ε • ContinuousLinearMap.id ℝ Space) = ε • fderiv ℝ A (x₀ + ε • z) := by
    ext y
    simp
  rw [heq, map_smul]

theorem curl_const_smul {A : Space → Space} (hA : ContDiff ℝ ∞ A) (ε : ℝ) (z : Space) :
    SpatialCurl.curl (fun y => ε • A y) z = ε • SpatialCurl.curl A z := by
  unfold SpatialCurl.curl
  rw [fderiv_fun_const_smul ((hA.differentiable (by simp)) z), map_smul]

def spatialCutoff (θ : Space → ℝ) (x₀ : Space) (ε : ℝ) : Space → ℝ :=
  fun x => θ (ε⁻¹ • (x - x₀))

def temporalCutoff (η : ℝ → ℝ) (T ε : ℝ) : ℝ → ℝ :=
  fun t => η ((ε ^ 2)⁻¹ * (t - T))

def physicalCorrection (v : VelocityField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (ε : ℝ) : VelocityField :=
  localCorrection v x₀ (spatialCutoff θ x₀ ε) (temporalCutoff η T ε)

/-- The exact correction representation from the paper: the correction has
amplitude one in rescaled coordinates, including all nonlinear background data. -/
theorem physicalCorrection_rescale {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε σ : ℝ) (hε : ε ≠ 0) (z : Space)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) :
    physicalCorrection v x₀ T θ η ε (T + ε ^ 2 * σ, x₀ + ε • z) =
      profile v x₀ T θ η (ε, σ, z) := by
  let t := T + ε ^ 2 * σ
  let A : Space → Space := fun x =>
    (temporalCutoff η T ε t * spatialCutoff θ x₀ ε x) • RadialPotential.timePotential v x₀ (t, x)
  let B : Space → Space := fun y => cutPotential v x₀ T θ η (ε, σ, y)
  have hAsmooth : ContDiff ℝ ∞ A := by
    have hθs : ContDiff ℝ ∞ (spatialCutoff θ x₀ ε) :=
      hθ.comp ((contDiff_id.sub contDiff_const).const_smul ε⁻¹)
    have hP : ContDiff ℝ ∞ (fun y : Space => RadialPotential.timePotential v x₀ (t, y)) :=
      (RadialPotential.timePotential_contDiff hv x₀).comp (contDiff_const.prodMk contDiff_id)
    exact (contDiff_const.mul hθs).smul hP
  have hBsmooth : ContDiff ℝ ∞ B :=
    (cutPotential_smooth hv x₀ T hθ hη).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have heq : (fun y => A (x₀ + ε • y)) = fun y => ε • B y := by
    funext y
    have hx : x₀ + ε • y - x₀ = ε • y := by abel
    have ht : t - T = ε ^ 2 * σ := by dsimp [t]; ring
    simp only [A, B, spatialCutoff, temporalCutoff, hx, ht, smul_smul,
      inv_mul_cancel₀ hε, one_smul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hε), one_mul]
    rw [timePotential_rescale]
    exact smul_comm (η σ * θ y) ε _
  have hc := curl_affine_scaling hAsmooth x₀ ε z
  rw [heq, curl_const_smul hBsmooth] at hc
  have hc' := congrArg (fun a : Space => ε⁻¹ • a) hc
  simp only [smul_smul, inv_mul_cancel₀ hε, one_smul] at hc'
  have hp := profile_eq_localCorrection hv x₀ T ε σ z hθ hη
  change -SpatialCurl.curl A (x₀ + ε • z) = _
  rw [← hc']
  rw [hp]
  change -SpatialCurl.curl B z = -SpatialCurl.curl _ z
  congr 2
  funext y
  exact congrArg (fun a : Space => (η σ * θ y) • a) (jointPotential_slice v x₀ T ε σ y)

/-- Every scale has the same fixed rescaled support cylinder. -/
theorem profile_support {v : VelocityField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) :
    tsupport (profile v x₀ T θ η) ⊆ (univ : Set ℝ) ×ˢ (tsupport η ×ˢ tsupport θ) := by
  apply closure_minimal _ (isClosed_univ.prod ((isClosed_tsupport η).prod (isClosed_tsupport θ)))
  rintro ⟨ε, σ, z⟩ hp
  refine ⟨mem_univ _, ?_⟩
  apply localCorrection_support (rescaledReference v x₀ T ε) 0 θ η
  apply subset_tsupport
  change localCorrection (rescaledReference v x₀ T ε) 0 θ η (σ, z) ≠ 0
  rw [← profile_eq_localCorrection hv x₀ T ε σ z hθ hη]
  exact hp

/-- Compact cutoffs give global-in-profile-coordinate uniform bounds for every
fixed derivative order, uniformly all the way down to ε=0. -/
theorem profile_uniform_global_derivative_bound {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Icc (0 : ℝ) 1, ∀ z : SpaceTime,
      ‖iteratedFDeriv ℝ k (profile v x₀ T θ η) (ε, z)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := profile_uniform_derivative_bound hv x₀ T hθ hη k (hηc.prod hθc)
  refine ⟨C, hC, ?_⟩
  intro ε hε z
  by_cases hz : z ∈ tsupport η ×ˢ tsupport θ
  · exact hb ε hε z hz
  · have hp : (ε, z) ∉ tsupport (profile v x₀ T θ η) :=
      fun h => hz ((profile_support hv x₀ T hθ hη h).2)
    have hd : iteratedFDeriv ℝ k (profile v x₀ T θ η) (ε, z) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp (tsupport_iteratedFDeriv_subset k h))
    simpa only [hd, norm_zero] using hC

def inverseScale (ε : ℝ) : SpaceTime →L[ℝ] SpaceTime :=
  (((ε ^ 2)⁻¹) • ContinuousLinearMap.fst ℝ ℝ Space).prod
    (ε⁻¹ • ContinuousLinearMap.snd ℝ ℝ Space)

/-- The exact physical correction written as a pullback of the smooth profile. -/
theorem physicalCorrection_eq_profile {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε : ℝ) (hε : ε ≠ 0)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (p : SpaceTime) :
    physicalCorrection v x₀ T θ η ε p =
      profile v x₀ T θ η (ε, inverseScale ε (p - (T, x₀))) := by
  have h := physicalCorrection_rescale hv x₀ T ε
    ((ε ^ 2)⁻¹ * (p.1 - T)) hε (ε⁻¹ • (p.2 - x₀)) hθ hη
  have ht : T + ε ^ 2 * ((ε ^ 2)⁻¹ * (p.1 - T)) = p.1 := by
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hε), one_mul]
    ring
  have hx : x₀ + ε • (ε⁻¹ • (p.2 - x₀)) = p.2 := by
    rw [smul_smul, mul_inv_cancel₀ hε, one_smul]
    abel
  change physicalCorrection v x₀ T θ η ε p =
    profile v x₀ T θ η (ε, (ε ^ 2)⁻¹ * (p.1 - T), ε⁻¹ • (p.2 - x₀))
  simpa only [ht, hx] using h

/-- All iterated derivatives transform exactly under an affine pullback. -/
theorem iteratedFDeriv_affine_apply {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} (hf : ContDiff ℝ ∞ f) (L : E →L[ℝ] F)
    (a : F) (c x : E) (k : ℕ) (h : Fin k → E) :
    iteratedFDeriv ℝ k (fun y => f (a + L (y - c))) x h =
      iteratedFDeriv ℝ k f (a + L (x - c)) (fun i => L (h i)) := by
  rw [iteratedFDeriv_comp_sub (𝕜 := ℝ) (f := fun y => f (a + L y)) k c x]
  have hs : ContDiff ℝ ∞ (fun y => f (a + y)) := hf.comp (contDiff_const.add contDiff_id)
  have hc := L.iteratedFDeriv_comp_right hs (x - c) (by simp : (k : WithTop ℕ∞) ≤ ∞)
  change iteratedFDeriv ℝ k (fun y => f (a + L y)) (x - c) = _ at hc
  rw [hc]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_comp_add_left]

@[simp] theorem inverseScale_apply (ε : ℝ) (p : SpaceTime) :
    inverseScale ε p = ((ε ^ 2)⁻¹ * p.1, ε⁻¹ • p.2) := rfl

/-- Exact directional scaling estimate. Each time direction contributes ε⁻²,
and each spatial direction contributes ε⁻¹; no derivative order is hidden in C. -/
theorem physical_directional_derivative_bound {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ p : SpaceTime, ∀ h : Fin k → SpaceTime,
      ‖iteratedFDeriv ℝ k (physicalCorrection v x₀ T θ η ε) p h‖ ≤
        C * ∏ i, ‖inverseScale ε (h i)‖ := by
  obtain ⟨C, hC, hb⟩ := profile_uniform_global_derivative_bound hv x₀ T hθ hη hθc hηc k
  refine ⟨C, hC, ?_⟩
  intro ε hε p h
  let L : SpaceTime →L[ℝ] Parameter :=
    (ContinuousLinearMap.inr ℝ ℝ SpaceTime).comp (inverseScale ε)
  have heq : physicalCorrection v x₀ T θ η ε =
      (fun q => profile v x₀ T θ η ((ε, 0) + L (q - (T, x₀)))) := by
    funext q
    rw [physicalCorrection_eq_profile hv x₀ T ε hε.1.ne' hθ hη]
    simp [L]
  rw [heq, iteratedFDeriv_affine_apply (profile_smooth hv x₀ T hθ hη)]
  have hp : (ε, (0 : SpaceTime)) + L (p - (T, x₀)) =
      (ε, inverseScale ε (p - (T, x₀))) := by simp [L]
  rw [hp]
  have hnorm := hb ε ⟨hε.1.le, hε.2⟩ (inverseScale ε (p - (T, x₀)))
  have hbnd := ContinuousMultilinearMap.le_of_opNorm_le hnorm (fun i => L (h i))
  simpa [L] using hbnd

/-- The mixed time/spatial derivative estimate ε^(-2j-m) of Lemma
`lem:correction`, expressed using j unit time directions followed by m spatial
directions of norm at most one. The derivative is a genuine iterated Fréchet derivative. -/
theorem physical_mixed_derivative_bound {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (j m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ p : SpaceTime,
      ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ (j + m) (physicalCorrection v x₀ T θ η ε) p
        (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space))) (fun i => ((0 : ℝ), u i)))‖ ≤
        C * (ε⁻¹) ^ (2 * j + m) := by
  obtain ⟨C, hC, hb⟩ := physical_directional_derivative_bound hv x₀ T hθ hη hθc hηc (j + m)
  refine ⟨C, hC, ?_⟩
  intro ε hε p u hu
  have hεinv : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.1.le
  have ht : ‖inverseScale ε ((1 : ℝ), (0 : Space))‖ = (ε⁻¹) ^ 2 := by
    simp [inverseScale_apply, Prod.norm_def, inv_pow, Real.norm_eq_abs, sq_nonneg]
  have hx (i : Fin m) : ‖inverseScale ε ((0 : ℝ), u i)‖ ≤ ε⁻¹ := by
    simp only [inverseScale_apply, mul_zero, Prod.norm_def, norm_zero,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hεinv]
    exact max_le hεinv (mul_le_of_le_one_right hεinv (hu i))
  have hprod : (∏ i : Fin m, ‖inverseScale ε ((0 : ℝ), u i)‖) ≤ (ε⁻¹) ^ m := by
    calc
      _ ≤ ∏ _i : Fin m, ε⁻¹ := Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hx i)
      _ = _ := by simp
  refine (hb ε hε p _).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right, ht, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  calc
    ((ε⁻¹) ^ 2) ^ j * (∏ i : Fin m, ‖inverseScale ε (0, u i)‖) ≤
        ((ε⁻¹) ^ 2) ^ j * (ε⁻¹) ^ m :=
      mul_le_mul_of_nonneg_left hprod (pow_nonneg (sq_nonneg _) _)
    _ = (ε⁻¹) ^ (2 * j + m) := by rw [← pow_mul, ← pow_add]

end NSFormalization.Paper1.CorrectionProfile
