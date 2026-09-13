import NavierStokes.R3CompactEnergy
import NavierStokes.R3CutoffSobolev
import NavierStokes.R3PressureFlux

/-!
# Norms and dissipation in the localized energy estimate
-/

noncomputable section
namespace NavierStokes.R3EnergyNorms

open Set Filter MeasureTheory ProblemStatement InnerProductSpace
open R3CompactEnergy R3CutoffSobolev R3WeightedLp
open scoped ContDiff RealInnerProductSpace ENNReal

theorem lpNorm_two_sq {V : Type*} [NormedAddCommGroup V] {f : Space → V}
    (hf : AEStronglyMeasurable f volume) :
    lpNorm f 2 volume ^ 2 = ∫ x : Space, ‖f x‖ ^ 2 := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf]
  norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg (fun x => sq_nonneg ‖f x‖))]
  norm_num

theorem integral_mul_le {f g : Space → ℝ} (hf : MemLp f 2) (hg : MemLp g 2)
    (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) :
    (∫ x : Space, f x * g x) ≤ lpNorm f 2 volume * lpNorm g 2 volume := by
  have he : (∫ x : Space, f x * g x) = lpNorm (fun x => f x * g x) 1 volume := by
    rw [lpNorm_one_eq_integral_norm (hf.1.fun_mul hg.1)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => (Real.norm_of_nonneg (mul_nonneg (hf₀ x) (hg₀ x))).symm)
  rw [he]
  exact lpNorm_mul_le hf hg

theorem weightedDerivative_sq_le_dissipation {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w) :
    lpNorm (weightedDerivativeNorm φ w) 2 volume ^ 2 ≤
      3 * dissipation (fun x => φ x ^ 8) w := by
  have hm := weightedDerivativeNorm_memLp (hφ.of_le (by simp)) hc (hw.of_le (by simp))
  have hp : HasCompactSupport (fun x => φ x ^ 8) := hc.comp_left (g := fun r : ℝ => r ^ 8) (by norm_num)
  have hi (i : Fin 3) : Integrable (fun x => φ x ^ 8 * ‖PeriodicIntegration.spatialPartial i w x‖ ^ 2) :=
    R3CompactIntegration.integrable_mul (hφ.continuous.pow 8)
      ((partial_smooth hw i).continuous.norm.pow 2) hp
  have hs : Integrable (fun x => ∑ i : Fin 3, φ x ^ 8 * ‖PeriodicIntegration.spatialPartial i w x‖ ^ 2) :=
    integrable_finsetSum _ (fun i _ => hi i)
  have hb (x : Space) : ‖weightedDerivativeNorm φ w x‖ ^ 2 ≤
      3 * ∑ i : Fin 3, φ x ^ 8 * ‖PeriodicIntegration.spatialPartial i w x‖ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left (operator_norm_sq_le (fderiv ℝ w x)) (by positivity : 0 ≤ φ x ^ 8)
    simp only [weightedDerivativeNorm, Real.norm_eq_abs, sq_abs, mul_pow, ← pow_mul,
      PeriodicIntegration.spatialPartial, ← Finset.mul_sum]
    norm_num only [Nat.reduceMul]
    nlinarith only [hh]
  rw [lpNorm_two_sq hm.1]
  have hmsq : Integrable (fun x => ‖weightedDerivativeNorm φ w x‖ ^ 2) := by
    exact (memLp_two_iff_integrable_sq hm.norm.1).mp hm.norm
  have hh := integral_mono hmsq (hs.const_mul 3) hb
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)] at hh
  exact hh

theorem neg_coupling_le {χ : Space → ℝ} {w u : Space → Space} {B : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hχ₀ : ∀ x, 0 ≤ χ x)
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (hB : ∀ x, ‖fderiv ℝ u x‖ ≤ B) :
    -coupling χ w u ≤ B * (∫ x : Space, χ x * ‖w x‖ ^ 2) := by
  have hi : Integrable (fun x => χ x * ⟪w x, fderiv ℝ u x (w x)⟫_ℝ) :=
    integrable_weighted_inner hχ.continuous hw.continuous
      ((hu.continuous_fderiv (by simp)).clm_apply hw.continuous) hc
  have hj := R3CompactIntegration.integrable_mul hχ.continuous (hw.continuous.norm.pow 2) hc
  rw [coupling, ← integral_neg, ← integral_const_mul]
  apply integral_mono hi.neg (hj.const_mul B)
  intro x
  change -(χ x * ⟪w x, fderiv ℝ u x (w x)⟫_ℝ) ≤ B * (χ x * ‖w x‖ ^ 2)
  have hh := mul_le_mul_of_nonneg_left (PeriodicUniqueness.nonlinear_energy_bound (fderiv ℝ u x) (w x) (hB x)) (hχ₀ x)
  nlinarith only [hh]

def pressureFluxFactor (φ : Space → ℝ) (w : Space → Space) (x : Space) : ℂ :=
  (8 * φ x * fderiv ℝ φ x (w x) : ℝ)

theorem pressureFluxFactor_bound {φ : Space → ℝ} {w : Space → Space} {D : ℝ}
    (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1) (hD : ∀ x, ‖fderiv ℝ φ x‖ ≤ D) (x : Space) :
    ‖pressureFluxFactor φ w x‖ ≤ 8 * D * ‖w x‖ := by
  have hh := (fderiv ℝ φ x).le_opNorm (w x)
  have hp : 0 ≤ 8 * φ x := mul_nonneg (by norm_num) (hφ x).1
  rw [pressureFluxFactor, Complex.norm_real, norm_mul, Real.norm_of_nonneg hp]
  have hd : 0 ≤ D := (norm_nonneg _).trans (hD x)
  have hbound := mul_le_mul_of_nonneg_left (hh.trans
    (mul_le_mul_of_nonneg_right (hD x) (norm_nonneg _))) hp
  have hl := mul_le_mul_of_nonneg_right (hφ x).2 (mul_nonneg hd (norm_nonneg (w x)))
  nlinarith only [hbound, hl]

theorem pressureFluxFactor_memLp {φ : Space → ℝ} {w : Space → Space} {D : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) (hr : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hD : 0 ≤ D) (hb : ∀ x, ‖fderiv ℝ φ x‖ ≤ D) (hw₂ : MemLp w 2) :
    MemLp (pressureFluxFactor φ w) 2 ∧
      lpNorm (pressureFluxFactor φ w) 2 volume ≤ 8 * D * lpNorm w 2 volume := by
  have hc : Continuous (pressureFluxFactor φ w) := by
    unfold pressureFluxFactor
    exact Complex.continuous_ofReal.comp
      ((continuous_const.mul hφ.continuous).mul ((hφ.continuous_fderiv (by simp)).clm_apply hw.continuous))
  have hM := hw₂.norm.const_mul (8 * D)
  have hm := hM.mono' hc.aestronglyMeasurable (Eventually.of_forall (pressureFluxFactor_bound hr hb))
  refine ⟨hm, ?_⟩
  have hh := lpNorm_mono_real hM (pressureFluxFactor_bound hr hb)
  change lpNorm (pressureFluxFactor φ w) 2 volume ≤ lpNorm ((8 * D) • (fun x => ‖w x‖)) 2 volume at hh
  rw [lpNorm_const_smul, coe_nnnorm, Real.norm_of_nonneg (by positivity), lpNorm_norm hw₂.1] at hh
  exact hh

theorem pressureFluxFactor_identity {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (w : Space → Space) (x : Space) :
    R3PressureCutoff.powerCutoff φ x * pressureFluxFactor φ w x =
      (fderiv ℝ (fun y => φ y ^ 8) x (w x) : ℝ) := by
  rw [((hφ.differentiable (by simp) x).hasFDerivAt.pow 8).fderiv]
  simp only [R3PressureCutoff.powerCutoff, pressureFluxFactor, smul_apply,
    smul_eq_mul]
  push_cast
  ring

end NavierStokes.R3EnergyNorms
