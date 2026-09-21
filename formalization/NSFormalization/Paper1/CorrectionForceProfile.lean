import NSFormalization.Paper1.CorrectionProfile
import NSFormalization.Source.ParabolicScaling
import Mathlib.Tactic.Module

/-! The smooth rescaled force correction and its exact ε⁻² amplitude. -/
noncomputable section
namespace NSFormalization.Paper1.CorrectionForceProfile
open NavierStokes NavierStokes.ProblemStatement Set MeasureTheory
open CorrectionProfile
open scoped ContDiff

def slice (F : Parameter → Space) (ε : ℝ) : VelocityField := fun z => F (ε, z)

def directionDerivative (F : Parameter → Space) (h : Parameter) (p : Parameter) : Space :=
  fderiv ℝ F p h

def spaceDerivative (F : Parameter → Space) (p : Parameter) : Space →L[ℝ] Space :=
  (fderiv ℝ F p).comp spatialInclusion

def spaceLaplacian (F : Parameter → Space) (p : Parameter) : Space :=
  ∑ i : Fin 3, directionDerivative
    (directionDerivative F (spatialInclusion (coordinateVector i)))
    (spatialInclusion (coordinateVector i)) p

def timeDirection : Parameter := (0, 1, 0)

def referenceProfile (v : VelocityField) (x₀ : Space) (T : ℝ) (p : Parameter) : Space :=
  v (T + p.1 ^ 2 * p.2.1, x₀ + p.1 • p.2.2)

def forceProfile (ν : ℝ) (v : VelocityField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (p : Parameter) : Space :=
  let W := profile v x₀ T θ η
  let V := referenceProfile v x₀ T
  directionDerivative W timeDirection p - ν • spaceLaplacian W p +
    p.1 • (spaceDerivative V p (W p) + spaceDerivative W p (V p) + spaceDerivative W p (W p))

theorem directionDerivative_smooth {F : Parameter → Space} (hF : ContDiff ℝ ∞ F) (h : Parameter) :
    ContDiff ℝ ∞ (directionDerivative F h) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem spaceDerivative_smooth {F : Parameter → Space} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (spaceDerivative F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

theorem spaceLaplacian_smooth {F : Parameter → Space} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (spaceLaplacian F) :=
  ContDiff.sum (fun i _ => directionDerivative_smooth
    (directionDerivative_smooth hF (spatialInclusion (coordinateVector i)))
    (spatialInclusion (coordinateVector i)))

theorem referenceProfile_smooth {v : VelocityField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T : ℝ) :
    ContDiff ℝ ∞ (referenceProfile v x₀ T) := by
  apply hv.comp
  fun_prop

/-- The rescaled correction force is smooth jointly through zero scale. -/
theorem forceProfile_smooth (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (forceProfile ν v x₀ T θ η) := by
  have hW := profile_smooth hv x₀ T hθ hη
  have hV := referenceProfile_smooth hv x₀ T
  exact ((directionDerivative_smooth hW timeDirection).sub
    ((spaceLaplacian_smooth hW).const_smul ν)).add
    (contDiff_fst.smul ((((spaceDerivative_smooth hV).clm_apply hW).add
      ((spaceDerivative_smooth hW).clm_apply hV)).add ((spaceDerivative_smooth hW).clm_apply hW)))

theorem directionDerivative_support (F : Parameter → Space) (h : Parameter) :
    tsupport (directionDerivative F h) ⊆ tsupport F := by
  apply closure_minimal _ (isClosed_tsupport F)
  intro p hp
  by_contra hn
  exact hp (by simp [directionDerivative, fderiv_of_notMem_tsupport ℝ hn])

theorem forceProfile_support (ν : ℝ) (v : VelocityField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) :
    tsupport (forceProfile ν v x₀ T θ η) ⊆ tsupport (profile v x₀ T θ η) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  have hW : profile v x₀ T θ η p = 0 := image_eq_zero_of_notMem_tsupport hn
  have hD : fderiv ℝ (profile v x₀ T θ η) p = 0 := fderiv_of_notMem_tsupport ℝ hn
  have hDD (i : Fin 3) : directionDerivative
      (directionDerivative (profile v x₀ T θ η) (spatialInclusion (coordinateVector i)))
      (spatialInclusion (coordinateVector i)) p = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hn (directionDerivative_support _ _ (directionDerivative_support _ _ h))
  have hL : spaceLaplacian (profile v x₀ T θ η) p = 0 := by
    simp only [spaceLaplacian, hDD, Finset.sum_const_zero]
  exact hp (by simp [forceProfile, directionDerivative, spaceDerivative, hW, hD, hL])

theorem spatialDerivative_slice {F : Parameter → Space} (hF : ContDiff ℝ ∞ F)
    (ε t : ℝ) (x : Space) :
    spatialDerivative (slice F ε) t x = spaceDerivative F (ε, t, x) := by
  have hin : HasFDerivAt (fun y : Space => (ε, t, y)) spatialInclusion x :=
    (hasFDerivAt_const (𝕜 := ℝ) ε x).prodMk
      ((hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
  exact (((hF.differentiable (by simp)) (ε, t, x)).hasFDerivAt.comp x hin).fderiv

theorem temporalDerivative_slice {F : Parameter → Space} (hF : ContDiff ℝ ∞ F)
    (ε t : ℝ) (x : Space) :
    temporalDerivative (slice F ε) t x = directionDerivative F timeDirection (ε, t, x) := by
  have hin := (hasFDerivAt_const (𝕜 := ℝ) ε t).prodMk
    ((hasFDerivAt_id (𝕜 := ℝ) t).prodMk (hasFDerivAt_const (𝕜 := ℝ) x t))
  have hd := (((hF.differentiable (by simp)) (ε, t, x)).hasFDerivAt.comp t hin).fderiv
  change fderiv ℝ (fun s => F (ε, s, x)) t = _ at hd
  change fderiv ℝ (fun s => F (ε, s, x)) t 1 = _
  rw [hd]
  simp [directionDerivative, timeDirection]

theorem spatialLaplacian_slice {F : Parameter → Space} (hF : ContDiff ℝ ∞ F)
    (ε t : ℝ) (x : Space) :
    spatialLaplacian (slice F ε) t x = spaceLaplacian F (ε, t, x) := by
  unfold spatialLaplacian spaceLaplacian
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun y : Space => spatialDerivative (slice F ε) t y (coordinateVector i)) =
      (fun y => slice (directionDerivative F (spatialInclusion (coordinateVector i))) ε (t, y)) := by
    funext y
    rw [spatialDerivative_slice hF]
    rfl
  rw [heq]
  change spatialDerivative (slice (directionDerivative F (spatialInclusion (coordinateVector i))) ε)
    t x (coordinateVector i) = _
  rw [spatialDerivative_slice (directionDerivative_smooth hF _)]
  rfl

theorem forceProfile_eq_operators (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε t : ℝ) (x : Space) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) :
    forceProfile ν v x₀ T θ η (ε, t, x) =
      temporalDerivative (slice (profile v x₀ T θ η) ε) t x -
      ν • spatialLaplacian (slice (profile v x₀ T θ η) ε) t x +
      ε • (spatialDerivative (slice (referenceProfile v x₀ T) ε) t x (slice (profile v x₀ T θ η) ε (t, x)) +
        spatialDerivative (slice (profile v x₀ T θ η) ε) t x (slice (referenceProfile v x₀ T) ε (t, x)) +
        advection (slice (profile v x₀ T θ η) ε) t x) := by
  have hW := profile_smooth hv x₀ T hθ hη
  have hV := referenceProfile_smooth hv x₀ T
  rw [temporalDerivative_slice hW, spatialLaplacian_slice hW,
    spatialDerivative_slice hV, spatialDerivative_slice hW]
  unfold advection
  rw [spatialDerivative_slice hW]
  rfl

/-- Differential scaling for two amplitude-one fields in the actual
background correction force. -/
theorem correctionForce_dilate (ν c d T : ℝ) (x₀ : Space) (V W : VelocityField)
    (t : ℝ) (x : Space) :
    Source.correctionForce ν (Source.dilateField 1 c d T x₀ V)
      (Source.dilateField 1 c d T x₀ W) (t, x) =
      c • temporalDerivative W (c * (t - T)) (d • (x - x₀)) -
      ν • ((d ^ 2) • spatialLaplacian W (c * (t - T)) (d • (x - x₀))) +
      d • (spatialDerivative V (c * (t - T)) (d • (x - x₀)) (W (c * (t - T), d • (x - x₀))) +
        spatialDerivative W (c * (t - T)) (d • (x - x₀)) (V (c * (t - T), d • (x - x₀))) +
        advection W (c * (t - T)) (d • (x - x₀))) := by
  simp [Source.correctionForce, Source.dilate_temporalDerivative, Source.dilate_laplacian,
    Source.dilate_spatialDerivative, Source.dilate_advection, Source.dilateField, smul_add]
  abel

/-- The original reference is recovered from its amplitude-one rescaled field. -/
theorem reference_eq_dilate (v : VelocityField) (x₀ : Space) (T ε : ℝ) (hε : ε ≠ 0) :
    v = Source.dilateField 1 ((ε ^ 2)⁻¹) ε⁻¹ T x₀ (slice (referenceProfile v x₀ T) ε) := by
  funext p
  have ht : T + ε ^ 2 * ((ε ^ 2)⁻¹ * (p.1 - T)) = p.1 := by
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hε), one_mul]
    ring
  have hx : x₀ + ε • (ε⁻¹ • (p.2 - x₀)) = p.2 := by
    rw [smul_smul, mul_inv_cancel₀ hε, one_smul]
    abel
  simp only [Source.dilateField, slice, referenceProfile, ht, hx, one_smul]

theorem physicalCorrection_eq_dilate {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε : ℝ) (hε : ε ≠ 0)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) :
    physicalCorrection v x₀ T θ η ε = Source.dilateField 1 ((ε ^ 2)⁻¹) ε⁻¹ T x₀
      (slice (profile v x₀ T θ η) ε) := by
  funext p
  simpa only [Source.dilateField, slice, one_smul, inverseScale_apply, Prod.fst_sub, Prod.snd_sub]
    using physicalCorrection_eq_profile hv x₀ T ε hε hθ hη p

/-- The background force correction has exactly amplitude ε⁻² times a
jointly smooth profile, proving that the force has one extra power of ε
relative to the singular packet force. -/
theorem physicalForce_eq_profile (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε : ℝ) (hε : ε ≠ 0)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (p : SpaceTime) :
    Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε) p =
      (ε ^ 2)⁻¹ • forceProfile ν v x₀ T θ η (ε, inverseScale ε (p - (T, x₀))) := by
  have hV := reference_eq_dilate v x₀ T ε hε
  have hW := physicalCorrection_eq_dilate hv x₀ T ε hε hθ hη
  rw [hW]
  conv_lhs => arg 2; rw [hV]
  rw [correctionForce_dilate]
  rw [inverseScale_apply, forceProfile_eq_operators ν hv x₀ T ε _ _ hθ hη]
  have he : (ε ^ 2)⁻¹ * ε = ε⁻¹ := by
    field_simp
  simp only [Prod.fst_sub, Prod.snd_sub, smul_add, smul_sub, smul_smul, he, inv_pow]
  module

/-- Every derivative of the rescaled force profile is uniformly bounded on
all rescaled spacetime coordinates and ε∈[0,1]. -/
theorem forceProfile_uniform_derivative_bound (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Icc (0 : ℝ) 1, ∀ z : SpaceTime,
      ‖iteratedFDeriv ℝ k (forceProfile ν v x₀ T θ η) (ε, z)‖ ≤ C := by
  have hc : Continuous (iteratedFDeriv ℝ k (forceProfile ν v x₀ T θ η)) :=
    (forceProfile_smooth ν hv x₀ T hθ hη).continuous_iteratedFDeriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (hηc.prod hθc)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro ε hε z
  by_cases hz : z ∈ tsupport η ×ˢ tsupport θ
  · exact (hC (ε, z) ⟨hε, hz⟩).trans (le_max_left _ _)
  · have hp : (ε, z) ∉ tsupport (forceProfile ν v x₀ T θ η) := by
      intro h
      exact hz ((profile_support hv x₀ T hθ hη (forceProfile_support ν v x₀ T θ η h)).2)
    have hd : iteratedFDeriv ℝ k (forceProfile ν v x₀ T θ η) (ε, z) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp (tsupport_iteratedFDeriv_subset k h))
    simp only [hd, norm_zero]
    exact le_max_right _ _

/-- Genuine physical correction-force derivatives with the full ε⁻²
amplitude and one inverse-scale factor for every derivative direction. -/
theorem physicalForce_directional_derivative_bound (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ p : SpaceTime, ∀ h : Fin k → SpaceTime,
      ‖iteratedFDeriv ℝ k (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) p h‖ ≤
        C * (ε⁻¹) ^ 2 * ∏ i, ‖inverseScale ε (h i)‖ := by
  obtain ⟨C, hC, hb⟩ := forceProfile_uniform_derivative_bound ν hv x₀ T hθ hη hθc hηc k
  refine ⟨C, hC, ?_⟩
  intro ε hε p h
  let L : SpaceTime →L[ℝ] Parameter :=
    (ContinuousLinearMap.inr ℝ ℝ SpaceTime).comp (inverseScale ε)
  let G : SpaceTime → Space := fun q =>
    forceProfile ν v x₀ T θ η ((ε, 0) + L (q - (T, x₀)))
  have hF := forceProfile_smooth ν hv x₀ T hθ hη
  have hG : ContDiff ℝ ∞ G := hF.comp
    (contDiff_const.add (L.contDiff.comp (contDiff_id.sub contDiff_const)))
  have heq : Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε) =
      fun q => (ε ^ 2)⁻¹ • G q := by
    funext q
    rw [physicalForce_eq_profile ν hv x₀ T ε hε.1.ne' hθ hη]
    simp [G, L]
  have hder : iteratedFDeriv ℝ k G p h =
      iteratedFDeriv ℝ k (forceProfile ν v x₀ T θ η)
        (ε, inverseScale ε (p - (T, x₀))) (fun i => L (h i)) := by
    change iteratedFDeriv ℝ k (fun q => forceProfile ν v x₀ T θ η ((ε, 0) + L (q - (T, x₀)))) p h = _
    rw [iteratedFDeriv_affine_apply hF]
    simp [L]
  have hbound : ‖iteratedFDeriv ℝ k G p h‖ ≤ C * ∏ i, ‖inverseScale ε (h i)‖ := by
    rw [hder]
    have hn := hb ε ⟨hε.1.le, hε.2⟩ (inverseScale ε (p - (T, x₀)))
    simpa [L] using ContinuousMultilinearMap.le_of_opNorm_le hn (fun i => L (h i))
  rw [heq, iteratedFDeriv_const_smul_apply' (hG.contDiffAt.of_le (by simp))]
  simp only [smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ε)), inv_pow]
  calc
    (ε ^ 2)⁻¹ * ‖iteratedFDeriv ℝ k G p h‖ ≤
        (ε ^ 2)⁻¹ * (C * ∏ i, ‖inverseScale ε (h i)‖) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (sq_nonneg ε))
    _ = C * (ε ^ 2)⁻¹ * ∏ i, ‖inverseScale ε (h i)‖ := by ring

/-- The exact spatial derivative estimate for the actual background force:
order m costs ε^(-2-m), uniformly in physical time and space. -/
theorem physicalForce_spatial_derivative_bound (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ p : SpaceTime,
      ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) p
        (fun i => ((0 : ℝ), u i))‖ ≤ C * (ε⁻¹) ^ (2 + m) := by
  obtain ⟨C, hC, hb⟩ := physicalForce_directional_derivative_bound ν hv x₀ T hθ hη hθc hηc m
  refine ⟨C, hC, ?_⟩
  intro ε hε p u hu
  have hεinv : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.1.le
  have hx (i : Fin m) : ‖inverseScale ε ((0 : ℝ), u i)‖ ≤ ε⁻¹ := by
    simp only [inverseScale_apply, mul_zero, Prod.norm_def, norm_zero,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hεinv]
    exact max_le hεinv (mul_le_of_le_one_right hεinv (hu i))
  have hprod : (∏ i : Fin m, ‖inverseScale ε ((0 : ℝ), u i)‖) ≤ (ε⁻¹) ^ m := by
    calc
      _ ≤ ∏ _i : Fin m, ε⁻¹ := Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hx i)
      _ = _ := by simp
  refine (hb ε hε p _).trans ?_
  calc
    C * (ε⁻¹) ^ 2 * (∏ i : Fin m, ‖inverseScale ε (0, u i)‖) ≤
        C * (ε⁻¹) ^ 2 * (ε⁻¹) ^ m :=
      mul_le_mul_of_nonneg_left hprod (mul_nonneg hC (sq_nonneg _))
    _ = C * (ε⁻¹) ^ (2 + m) := by rw [mul_assoc, ← pow_add]

end NSFormalization.Paper1.CorrectionForceProfile
