import NavierStokes.R3LocalizedPressure
import NavierStokes.PeriodicUniqueness

/-!
# Real fields in the complex space-time pressure calculation

These lemmas identify each space-time directional derivative with the
physical spatial or temporal derivative, including the Laplacian.
-/

noncomputable section
namespace NavierStokes.R3SpaceTimeCalculus

open Set Filter MeasureTheory ProblemStatement
open R3SpaceTime R3WeakPressure R3LocalizedPressure
open scoped ContDiff

def unpack : Domain ≃L[ℝ] SpaceTime := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ Space

def liftScalar (f : PressureField) (z : Domain) : ℂ := (f (timeProj z, spaceProj z) : ℝ)

def liftVelocity (u : VelocityField) (i : Fin 3) : Domain → ℂ := liftScalar (fun tx => u tx i)

@[simp] theorem liftScalar_pack (f : PressureField) (t : ℝ) (x : Space) :
    liftScalar f (pack t x) = (f (t, x) : ℂ) := rfl

@[simp] theorem liftVelocity_pack (u : VelocityField) (i : Fin 3) (t : ℝ) (x : Space) :
    liftVelocity u i (pack t x) = (u (t, x) i : ℂ) := rfl

theorem liftScalar_smooth {s : Set ℝ} {f : PressureField}
    (hf : ContDiffOn ℝ ∞ f (s ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (liftScalar f) (timeProj ⁻¹' s) := by
  apply Complex.ofRealCLM.contDiff.comp_contDiffOn
    (hf.comp unpack.contDiff.contDiffOn ?_)
  intro z hz
  exact ⟨hz, mem_univ _⟩

theorem liftVelocity_smooth {s : Set ℝ} {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (s ×ˢ (univ : Set Space))) (i : Fin 3) :
    ContDiffOn ℝ ∞ (liftVelocity u i) (timeProj ⁻¹' s) :=
  liftScalar_smooth ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hu)

theorem slice_smooth {s : Set ℝ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SpaceTime → V} (hf : ContDiffOn ℝ ∞ f (s ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ s) : ContDiff ℝ ∞ (fun x : Space => f (t, x)) := by
  rw [← contDiffOn_univ]
  exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ⟨ht, mem_univ x⟩)

theorem differentiable_at {s : Set ℝ} (hs : IsOpen s) {F : Domain → ℂ}
    (hF : ContDiffOn ℝ ∞ F (timeProj ⁻¹' s)) {t : ℝ} (ht : t ∈ s) (x : Space) :
    DifferentiableAt ℝ F (pack t x) :=
  (hF.contDiffAt ((hs.preimage timeProj.continuous).mem_nhds ht)).differentiableAt (by simp)

theorem spatial_slice_derivative {F : Domain → ℂ} {t : ℝ} {x : Space}
    (hF : DifferentiableAt ℝ F (pack t x)) (i : Fin 3) :
    directional (spaceDirection i) F (pack t x) =
      fderiv ℝ (fun y => F (pack t y)) x (coordinateVector i) := by
  have hpack := unpack.symm.hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  have h := (hF.hasFDerivAt.comp x hpack).fderiv
  have hh := congrArg (fun A : Space →L[ℝ] ℂ => A (coordinateVector i)) h
  exact hh.symm

theorem temporal_slice_derivative {F : Domain → ℂ} {t : ℝ} {x : Space}
    (hF : DifferentiableAt ℝ F (pack t x)) :
    directional timeDirection F (pack t x) = deriv (fun s => F (pack s x)) t := by
  have hpack := unpack.symm.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have h := (hF.hasFDerivAt.comp_hasDerivAt t hpack).deriv
  exact h.symm

theorem fderiv_ofReal {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (x v : Space) :
    fderiv ℝ (fun y => (f y : ℂ)) x v = (fderiv ℝ f x v : ℝ) := by
  change fderiv ℝ (Complex.ofRealCLM ∘ f) x v = _
  rw [(Complex.ofRealCLM.hasFDerivAt.comp x (hf.differentiable (by simp) x).hasFDerivAt).fderiv]
  rfl

theorem lift_space_derivative {s : Set ℝ} (hs : IsOpen s) {f : PressureField}
    (hf : ContDiffOn ℝ ∞ f (s ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ s) (x : Space) (i : Fin 3) :
    directional (spaceDirection i) (liftScalar f) (pack t x) =
      (fderiv ℝ (fun y => f (t, y)) x (coordinateVector i) : ℝ) := by
  rw [spatial_slice_derivative (differentiable_at hs (liftScalar_smooth hf) ht x)]
  exact fderiv_ofReal (slice_smooth hf ht) x (coordinateVector i)

theorem lift_laplacian {s : Set ℝ} (hs : IsOpen s) {f : PressureField}
    (hf : ContDiffOn ℝ ∞ f (s ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ s) (x : Space) :
    functionLaplacian (liftScalar f) (pack t x) =
      (∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun z => f (t, z)) y (coordinateVector i)) x
        (coordinateVector i) : ℝ) := by
  have hfs := liftScalar_smooth hf
  unfold functionLaplacian
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [spatial_slice_derivative (differentiable_at hs
    (directional_contDiffOn (hs.preimage timeProj.continuous) hfs (spaceDirection i)) ht x)]
  have he : (fun y => directional (spaceDirection i) (liftScalar f) (pack t y)) =
      (fun y => (fderiv ℝ (fun z => f (t, z)) y (coordinateVector i) : ℂ)) :=
    funext fun y => lift_space_derivative hs hf ht y i
  rw [he]
  exact fderiv_ofReal (PeriodicUniqueness.spatial_partial_contDiff (slice_smooth hf ht) i) x (coordinateVector i)

theorem liftVelocity_laplacian {s : Set ℝ} (hs : IsOpen s) {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (s ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ s) (x : Space) (i : Fin 3) :
    functionLaplacian (liftVelocity u i) (pack t x) = (spatialLaplacian u t x i : ℂ) := by
  have hui : ContDiffOn ℝ ∞ (fun z => u z i) (s ×ˢ (univ : Set Space)) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hu
  rw [liftVelocity, lift_laplacian hs hui ht]
  congr 1
  have hus := slice_smooth hu ht
  change _ = (EuclideanSpace.proj i : Space →L[ℝ] ℝ) (ProblemStatement.spatialLaplacian u t x)
  rw [ProblemStatement.spatialLaplacian, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [PeriodicUniqueness.fderiv_component hus]
  exact PeriodicUniqueness.fderiv_component (PeriodicUniqueness.spatial_partial_contDiff hus j) i x (coordinateVector j)

theorem liftVelocity_time {s : Set ℝ} (hs : IsOpen s) {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (s ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ s) (x : Space) (i : Fin 3) :
    directional timeDirection (liftVelocity u i) (pack t x) = (temporalDerivative u t x i : ℂ) := by
  rw [temporal_slice_derivative (differentiable_at hs (liftVelocity_smooth hu i) ht x)]
  have hud : DifferentiableAt ℝ (fun r : ℝ => u (r, x)) t :=
    ((hu.contDiffAt ((hs.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)).comp t
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have h := (Complex.ofRealCLM.comp (EuclideanSpace.proj i)).hasFDerivAt.comp_hasDerivAt t hud.hasDerivAt
  exact h.deriv

theorem liftVelocity_divergence {s : Set ℝ} (hs : IsOpen s) {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (s ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ s) (x : Space) :
    functionDivergence (liftVelocity u) (pack t x) = (spatialDivergence u t x : ℂ) := by
  unfold functionDivergence spatialDivergence
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hui : ContDiffOn ℝ ∞ (fun z => u z i) (s ×ˢ (univ : Set Space)) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hu
  rw [liftVelocity, lift_space_derivative hs hui ht]
  rw [PeriodicUniqueness.fderiv_component (slice_smooth hu ht)]
  rfl

end NavierStokes.R3SpaceTimeCalculus
