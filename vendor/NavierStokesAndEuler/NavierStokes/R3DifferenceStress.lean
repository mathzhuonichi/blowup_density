import NavierStokes.R3SpaceTimeCalculus
import NavierStokes.R3CompactEnergy

/-!
# The actual difference stress and pressure equation
-/

noncomputable section
namespace NavierStokes.R3DifferenceStress

open Set Filter MeasureTheory ProblemStatement
open R3SpaceTime R3WeakPressure R3SpaceTimeCalculus
open scoped ContDiff

def stress (u v : VelocityField) (i j : Fin 3) : Domain → ℂ :=
  liftScalar (fun tx => u tx i * u tx j - v tx i * v tx j)

theorem stress_smooth {s : Set ℝ} {u v : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (s ×ˢ (univ : Set Space)))
    (hv : ContDiffOn ℝ ∞ v (s ×ˢ (univ : Set Space))) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (stress u v i j) (timeProj ⁻¹' s) := by
  apply liftScalar_smooth
  have hu' k : ContDiffOn ℝ ∞ (fun tx => u tx k) (s ×ˢ (univ : Set Space)) :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hu
  have hv' k : ContDiffOn ℝ ∞ (fun tx => v tx k) (s ×ˢ (univ : Set Space)) :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hv
  exact ((hu' i).mul (hu' j)).sub ((hv' i).mul (hv' j))

theorem stress_norm (u v : VelocityField) (i j : Fin 3) (t : ℝ) (x : Space) :
    ‖stress u v i j (pack t x)‖ ≤ ‖(u - v) (t, x)‖ ^ 2 +
      2 * (‖u (t, x)‖ * ‖(u - v) (t, x)‖) := by
  let w := (u - v) (t, x)
  have he : u (t, x) i * u (t, x) j - v (t, x) i * v (t, x) j =
      u (t, x) i * w j + w i * u (t, x) j - w i * w j := by
    dsimp [w]
    ring
  change ‖((u (t, x) i * u (t, x) j - v (t, x) i * v (t, x) j : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs, he]
  have hi : |w i| ≤ ‖w‖ := PiLp.norm_apply_le w i
  have hj : |w j| ≤ ‖w‖ := PiLp.norm_apply_le w j
  have hui : |u (t, x) i| ≤ ‖u (t, x)‖ := PiLp.norm_apply_le (u (t, x)) i
  have huj : |u (t, x) j| ≤ ‖u (t, x)‖ := PiLp.norm_apply_le (u (t, x)) j
  have h₁ := mul_le_mul hui hj (abs_nonneg _) (norm_nonneg _)
  have h₂ := mul_le_mul hi huj (abs_nonneg _) (norm_nonneg _)
  have h₃ := mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)
  have hh := (abs_sub (u (t, x) i * w j + w i * u (t, x) j) (w i * w j)).trans
    (add_le_add (abs_add_le (u (t, x) i * w j) (w i * u (t, x) j)) le_rfl)
  simp only [abs_mul] at hh
  change _ ≤ ‖w‖ ^ 2 + 2 * (‖u (t, x)‖ * ‖w‖)
  nlinarith only [h₁, h₂, h₃, hh]

theorem tensor_divergence {u : Space → Space} (hu : ContDiff ℝ ∞ u) (i : Fin 3) (x : Space) :
    (∑ j : Fin 3, fderiv ℝ (fun y => u y i * u y j) x (coordinateVector j)) =
      fderiv ℝ u x (u x) i + u x i * ∑ j : Fin 3, fderiv ℝ u x (coordinateVector j) j := by
  have hp (j : Fin 3) := R3CompactEnergy.partial_mul
    (PeriodicUniqueness.component_contDiff hu i) (PeriodicUniqueness.component_contDiff hu j) j x
  simp only [PeriodicIntegration.spatialPartial, PeriodicUniqueness.fderiv_component hu] at hp
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [← PeriodicUniqueness.fderiv_component hu]
  rw [PeriodicUniqueness.fderiv_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [PeriodicUniqueness.fderiv_component hu]
  ring

theorem stress_divergence {s : Set ℝ} (hs : IsOpen s) {u v : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (s ×ˢ (univ : Set Space)))
    (hv : ContDiffOn ℝ ∞ v (s ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ s)
    (hdu : ∀ x, spatialDivergence u t x = 0) (hdv : ∀ x, spatialDivergence v t x = 0)
    (x : Space) (i : Fin 3) :
    (∑ j : Fin 3, directional (spaceDirection j) (stress u v i j) (pack t x)) =
      ((advection u t x - advection v t x) i : ℝ) := by
  have hu' k : ContDiffOn ℝ ∞ (fun tx => u tx k) (s ×ˢ (univ : Set Space)) :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hu
  have hv' k : ContDiffOn ℝ ∞ (fun tx => v tx k) (s ×ˢ (univ : Set Space)) :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hv
  have he (j : Fin 3) := lift_space_derivative hs (((hu' i).mul (hu' j)).sub ((hv' i).mul (hv' j))) ht x j
  change (∑ j : Fin 3, directional (spaceDirection j)
    (liftScalar (fun tx => u tx i * u tx j - v tx i * v tx j)) (pack t x)) = _
  simp_rw [he]
  rw [← Complex.ofReal_sum]
  congr 1
  have hus := slice_smooth hu ht
  have hvs := slice_smooth hv ht
  have hf (j : Fin 3) : fderiv ℝ (fun y => u (t, y) i * u (t, y) j - v (t, y) i * v (t, y) j) x =
      fderiv ℝ (fun y => u (t, y) i * u (t, y) j) x -
        fderiv ℝ (fun y => v (t, y) i * v (t, y) j) x :=
    fderiv_fun_sub (((PeriodicUniqueness.component_contDiff hus i).mul
      (PeriodicUniqueness.component_contDiff hus j)).differentiable (by simp) x)
      (((PeriodicUniqueness.component_contDiff hvs i).mul
        (PeriodicUniqueness.component_contDiff hvs j)).differentiable (by simp) x)
  simp only [hf, sub_apply, Finset.sum_sub_distrib]
  rw [tensor_divergence hus, tensor_divergence hvs]
  change (spatialDerivative u t x (u (t, x)) i + u (t, x) i * spatialDivergence u t x) -
      (spatialDerivative v t x (v (t, x)) i + v (t, x) i * spatialDivergence v t x) = _
  simp [hdu, hdv, advection]

/-- Subtracting the physical equations gives precisely the momentum
gradient used in the space-time pressure reconstruction. -/
theorem momentum_equation {s : Set ℝ} (hs : IsOpen s) {u v : VelocityField} {p q : PressureField}
    (hu : ContDiffOn ℝ ∞ u (s ×ˢ (univ : Set Space)))
    (hv : ContDiffOn ℝ ∞ v (s ×ˢ (univ : Set Space)))
    (hp : ContDiffOn ℝ ∞ p (s ×ˢ (univ : Set Space)))
    (hq : ContDiffOn ℝ ∞ q (s ×ˢ (univ : Set Space)))
    (hdu : ∀ t ∈ s, ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ s, ∀ x, spatialDivergence v t x = 0)
    (heq : ∀ t ∈ s, ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x)
    (i : Fin 3) (z : Domain) (hz : timeProj z ∈ s) :
    functionMomentum (liftVelocity (u - v)) (fun _ _ => 0) (stress u v) i z =
      directional (spaceDirection i) (liftScalar (p - q)) z := by
  let t := timeProj z
  let x := spaceProj z
  have ht : t ∈ s := hz
  have hw : ContDiffOn ℝ ∞ (u - v) (s ×ˢ (univ : Set Space)) := hu.sub hv
  have hpq : ContDiffOn ℝ ∞ (p - q) (s ×ˢ (univ : Set Space)) := hp.sub hq
  have hz' : z = pack t x := rfl
  rw [hz']
  rw [functionMomentum, liftVelocity_laplacian hs hw ht x i,
    liftVelocity_time hs hw ht x i, stress_divergence hs hu hv ht (hdu t ht) (hdv t ht),
    lift_space_derivative hs hpq ht]
  have htu : DifferentiableAt ℝ (fun r => u (r, x)) t :=
    ((hu.contDiffAt ((hs.prod isOpen_univ).mem_nhds ⟨hz, mem_univ x⟩)).comp t
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have htv : DifferentiableAt ℝ (fun r => v (r, x)) t :=
    ((hv.contDiffAt ((hs.prod isOpen_univ).mem_nhds ⟨hz, mem_univ x⟩)).comp t
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hus := slice_smooth hu hz
  have hvs := slice_smooth hv hz
  have he := heq t hz x
  have hd := PeriodicUniqueness.pressureGradient_sub (slice_smooth hp hz) (slice_smooth hq hz) x
  have hpc : pressureGradient (p - q) t x i =
      fderiv ℝ (fun y => (p - q) (t, y)) x (coordinateVector i) := by
    simp [pressureGradient, coordinateVector, Pi.single_apply]
  rw [PeriodicUniqueness.spatialLaplacian_sub hus hvs, PeriodicUniqueness.temporalDerivative_sub htu htv]
  have hscalar := congrArg (fun y : Space => y i) he
  simp only [navierStokesResidual, PiLp.add_apply, PiLp.sub_apply] at hscalar
  have hpgrad := congrArg (fun y : Space => y i) hd
  rw [hpc] at hpgrad
  simp only [PiLp.sub_apply] at hpgrad ⊢
  push_cast
  norm_cast
  linarith

end NavierStokes.R3DifferenceStress
