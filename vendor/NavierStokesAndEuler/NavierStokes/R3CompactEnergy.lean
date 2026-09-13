import NavierStokes.R3CompactIntegration
import NavierStokes.PeriodicUniqueness

/-!
# Localized energy identities on Euclidean three-space

All integrations by parts use a compact spatial cutoff. The velocity and
pressure themselves need no decay of their derivatives.
-/

noncomputable section
namespace NavierStokes.R3CompactEnergy

open Set MeasureTheory InnerProductSpace ProblemStatement
open scoped ContDiff RealInnerProductSpace

local notation "D" => PeriodicIntegration.spatialPartial

theorem partial_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Space → V} (hf : ContDiff ℝ ∞ f) (i : Fin 3) : ContDiff ℝ ∞ (D i f) :=
  PeriodicUniqueness.spatial_partial_contDiff hf i

theorem partial_mul {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin 3) (x : Space) : D i (fun y => f y * g y) x =
      D i f x * g x + f x * D i g x := by
  unfold PeriodicIntegration.spatialPartial
  change (fderiv ℝ (f * g) x) _ = _
  rw [((hf.differentiable (by simp) x).hasFDerivAt.mul
    (hg.differentiable (by simp) x).hasFDerivAt).fderiv]
  simp
  ring

theorem integral_directional {f : Space → ℝ} {v : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport f) :
    (∫ x : Space, fderiv ℝ f x (v x)) =
      -(∫ x : Space, f x * ∑ i : Fin 3, D i v x i) := by
  have hi (i : Fin 3) : Integrable (fun x : Space => f x * D i v x i) :=
    R3CompactIntegration.integrable_mul hf.continuous
      (PeriodicUniqueness.component_contDiff (partial_smooth hv i) i).continuous hc
  have hj (i : Fin 3) : Integrable (fun x : Space => D i f x * v x i) :=
    R3CompactIntegration.integrable_mul (partial_smooth hf i).continuous
      (PeriodicUniqueness.component_contDiff hv i).continuous (hc.fderiv_apply ℝ _)
  have he (i : Fin 3) : (∫ x : Space, D i f x * v x i) =
      -(∫ x : Space, f x * D i v x i) := by
    have h := R3CompactIntegration.integration_by_parts
      (hf.of_le (by simp)) ((PeriodicUniqueness.component_contDiff hv i).of_le (by simp)) hc i
    simp only [R3CompactIntegration.spatialPartial, PeriodicUniqueness.fderiv_component hv] at h
    change (∫ x : Space, f x * D i v x i) = -(∫ x : Space, D i f x * v x i) at h
    linarith
  have hs : (fun x => fderiv ℝ f x (v x)) = (fun x => ∑ i : Fin 3, D i f x * v x i) := by
    funext x
    rw [PeriodicUniqueness.fderiv_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hs]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hj i), integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [he]
  rw [Finset.sum_neg_distrib]

theorem weighted_directional {χ f : Space → ℝ} {v : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v)
    (hc : HasCompactSupport χ) (hd : ∀ x, (∑ i : Fin 3, D i v x i) = 0) :
    (∫ x : Space, χ x * fderiv ℝ f x (v x)) =
      -(∫ x : Space, fderiv ℝ χ x (v x) * f x) := by
  have h := integral_directional (hχ.mul hf) hv hc.mul_right
  simp only [hd, mul_zero, integral_zero, neg_zero] at h
  have he (x : Space) : fderiv ℝ (fun y => χ y * f y) x (v x) =
      fderiv ℝ χ x (v x) * f x + χ x * fderiv ℝ f x (v x) := by
    change (fderiv ℝ (χ * f) x) _ = _
    rw [((hχ.differentiable (by simp) x).hasFDerivAt.mul
      (hf.differentiable (by simp) x).hasFDerivAt).fderiv]
    simp
    ring
  have hdc : HasCompactSupport (fun x => fderiv ℝ χ x (v x)) := by
    apply HasCompactSupport.intro (hc.fderiv (𝕜 := ℝ))
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx]
    rfl
  have hi : Integrable (fun x => fderiv ℝ χ x (v x) * f x) :=
    R3CompactIntegration.integrable_mul
      ((hχ.continuous_fderiv (by simp)).clm_apply hv.continuous) hf.continuous hdc
  have hj : Integrable (fun x => χ x * fderiv ℝ f x (v x)) :=
    R3CompactIntegration.integrable_mul hχ.continuous
      ((hf.continuous_fderiv (by simp)).clm_apply hv.continuous) hc
  simp_rw [he] at h
  rw [integral_add hi hj] at h
  linarith

theorem weighted_transport {χ : Space → ℝ} {w v : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v)
    (hc : HasCompactSupport χ) (hd : ∀ x, (∑ i : Fin 3, D i v x i) = 0) :
    2 * (∫ x : Space, χ x * ⟪w x, fderiv ℝ w x (v x)⟫_ℝ) =
      -(∫ x : Space, fderiv ℝ χ x (v x) * ‖w x‖ ^ 2) := by
  have h := weighted_directional hχ (hw.norm_sq ℝ) hv hc hd
  simp_rw [PeriodicUniqueness.fderiv_normsq hw] at h
  have he (x : Space) : χ x * (2 * ⟪w x, fderiv ℝ w x (v x)⟫_ℝ) =
      2 * (χ x * ⟪w x, fderiv ℝ w x (v x)⟫_ℝ) := by ring
  simpa only [he, integral_const_mul] using h

theorem inner_partial {f g : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport f) (i : Fin 3) :
    (∫ x : Space, ⟪f x, D i g x⟫_ℝ) = -(∫ x : Space, ⟪D i f x, g x⟫_ℝ) := by
  have compact_inner {a b : Space → Space} (ha : HasCompactSupport a) :
      HasCompactSupport (fun x => ⟪a x, b x⟫_ℝ) := by
    apply HasCompactSupport.intro ha
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, inner_zero_left]
  unfold PeriodicIntegration.spatialPartial
  apply integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (f := f) (g := g) (v := coordinateVector i) (μ := volume) (B := innerSL ℝ (E := Space))
  · exact ((partial_smooth hf i).continuous.inner hg.continuous).integrable_of_hasCompactSupport
      (compact_inner (hc.fderiv_apply ℝ _))
  · exact (hf.continuous.inner (partial_smooth hg i).continuous).integrable_of_hasCompactSupport
      (compact_inner hc)
  · exact (hf.continuous.inner hg.continuous).integrable_of_hasCompactSupport (compact_inner hc)
  · intro x _
    exact hf.differentiable (by simp) x
  · intro x _
    exact hg.differentiable (by simp) x

theorem weighted_second_partial {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport χ) (i : Fin 3) :
    (∫ x : Space, χ x * ⟪w x, D i (D i w) x⟫_ℝ) =
      -(∫ x : Space, χ x * ‖D i w x‖ ^ 2) -
       (∫ x : Space, D i χ x * ⟪w x, D i w x⟫_ℝ) := by
  have h := inner_partial (hχ.smul hw) (partial_smooth hw i) hc.smul_right i
  have he (x : Space) : D i (fun y => χ y • w y) x = D i χ x • w x + χ x • D i w x := by
    unfold PeriodicIntegration.spatialPartial
    change (fderiv ℝ (χ • w) x) _ = _
    rw [((hχ.differentiable (by simp) x).hasFDerivAt.smul
      (hw.differentiable (by simp) x).hasFDerivAt).fderiv]
    simp [add_comm]
  change (∫ x : Space, ⟪χ x • w x, D i (D i w) x⟫_ℝ) =
    -(∫ x : Space, ⟪D i (fun y => χ y • w y) x, D i w x⟫_ℝ) at h
  simp only [he, real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq] at h
  have hi : Integrable (fun x => D i χ x * ⟪w x, D i w x⟫_ℝ) :=
    R3CompactIntegration.integrable_mul (partial_smooth hχ i).continuous
      (hw.continuous.inner (partial_smooth hw i).continuous) (hc.fderiv_apply ℝ _)
  have hj : Integrable (fun x => χ x * ‖D i w x‖ ^ 2) :=
    R3CompactIntegration.integrable_mul hχ.continuous ((partial_smooth hw i).continuous.norm.pow 2) hc
  rw [integral_add hi hj] at h
  linarith

def dissipation (χ : Space → ℝ) (w : Space → Space) : ℝ :=
  ∑ i : Fin 3, ∫ x : Space, χ x * ‖D i w x‖ ^ 2

def diffusionFlux (χ : Space → ℝ) (w : Space → Space) : ℝ :=
  ∑ i : Fin 3, ∫ x : Space, D i χ x * ⟪w x, D i w x⟫_ℝ

def transportFlux (χ : Space → ℝ) (w v : Space → Space) : ℝ :=
  ∫ x : Space, fderiv ℝ χ x (v x) * ‖w x‖ ^ 2

def pressureFlux (χ : Space → ℝ) (w : Space → Space) (p : Space → ℝ) : ℝ :=
  ∫ x : Space, fderiv ℝ χ x (w x) * p x

def coupling (χ : Space → ℝ) (w u : Space → Space) : ℝ :=
  ∫ x : Space, χ x * ⟪w x, fderiv ℝ u x (w x)⟫_ℝ

theorem integrable_weighted_inner {χ : Space → ℝ} {f g : Space → Space}
    (hχ : Continuous χ) (hf : Continuous f) (hg : Continuous g) (hc : HasCompactSupport χ) :
    Integrable (fun x => χ x * ⟪f x, g x⟫_ℝ) :=
  R3CompactIntegration.integrable_mul hχ (hf.inner hg) hc

theorem weighted_laplacian {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport χ) :
    (∫ x : Space, χ x * ⟪w x, ∑ i : Fin 3, D i (D i w) x⟫_ℝ) =
      -dissipation χ w - diffusionFlux χ w := by
  simp only [inner_sum, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_weighted_inner hχ.continuous hw.continuous
    (partial_smooth (partial_smooth hw i) i).continuous hc)]
  simp_rw [weighted_second_partial hχ hw hc]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, dissipation, diffusionFlux]

theorem weighted_pressure {χ p : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w)
    (hc : HasCompactSupport χ) (hd : ∀ x, (∑ i : Fin 3, D i w x i) = 0) :
    (∫ x : Space, χ x * ⟪w x, pressureGradient (fun z => p z.2) 0 x⟫_ℝ) =
      -pressureFlux χ w p := by
  simp only [PeriodicUniqueness.inner_pressureGradient]
  exact weighted_directional hχ hp hw hc hd

/-- The full spatial energy identity for a difference equation. Both the
diffusion and pressure boundary terms are retained as actual integrals. -/
theorem energy_balance {χ p : Space → ℝ} {w u v z : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport χ)
    (hdw : ∀ x, (∑ i : Fin 3, D i w x i) = 0)
    (hdv : ∀ x, (∑ i : Fin 3, D i v x i) = 0)
    (heq : ∀ x, z x = (∑ i : Fin 3, D i (D i w) x) -
      fderiv ℝ w x (v x) - fderiv ℝ u x (w x) - pressureGradient (fun y => p y.2) 0 x) :
    2 * (∫ x : Space, χ x * ⟪w x, z x⟫_ℝ) =
      -2 * dissipation χ w - 2 * diffusionFlux χ w + transportFlux χ w v -
        2 * coupling χ w u + 2 * pressureFlux χ w p := by
  have hL : Continuous (fun x => ∑ i : Fin 3, D i (D i w) x) :=
    continuous_finsetSum _ (fun i _ => (partial_smooth (partial_smooth hw i) i).continuous)
  have hW : Continuous (fun x => fderiv ℝ w x (v x)) :=
    (hw.continuous_fderiv (by simp)).clm_apply hv.continuous
  have hU : Continuous (fun x => fderiv ℝ u x (w x)) :=
    (hu.continuous_fderiv (by simp)).clm_apply hw.continuous
  have hP : Continuous (fun x => pressureGradient (fun y => p y.2) 0 x) :=
    (PeriodicUniqueness.pressureGradient_contDiff (t := 0) (p := fun y => p y.2) hp).continuous
  have hiL := integrable_weighted_inner hχ.continuous hw.continuous hL hc
  have hiW := integrable_weighted_inner hχ.continuous hw.continuous hW hc
  have hiU := integrable_weighted_inner hχ.continuous hw.continuous hU hc
  have hiP := integrable_weighted_inner hχ.continuous hw.continuous hP hc
  have hs1 := integral_sub ((hiL.sub hiW).sub hiU) hiP
  have hs2 := integral_sub (hiL.sub hiW) hiU
  simp only [Pi.sub_apply] at hs1 hs2
  simp_rw [heq, inner_sub_right, mul_sub]
  rw [hs1, hs2,
    integral_sub hiL hiW, weighted_laplacian hχ hw hc, weighted_pressure hχ hp hw hc hdw]
  have hT := weighted_transport hχ hw hv hc hdv
  dsimp only [transportFlux, coupling]
  linarith

end NavierStokes.R3CompactEnergy
