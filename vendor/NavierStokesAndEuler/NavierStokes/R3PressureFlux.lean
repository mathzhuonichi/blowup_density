import NavierStokes.R3WeightedLp

/-!
# Flux bounds for the physical Gaussian pressure approximations

These bounds apply to the actual spatial stress function. They are uniform
in the Gaussian regularization index and pair the weighted pressure with an
arbitrary square-integrable flux factor.
-/

noncomputable section
namespace NavierStokes.R3PressureFlux

open Set Filter MeasureTheory ProblemStatement
open R3PressureCommutator R3PressureCutoff R3RieszApproximation R3WeightedLp
open scoped ENNReal

theorem norm_integral_mul_le {f g : Space → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    ‖∫ x : Space, f x * g x‖ ≤ lpNorm f 2 volume * lpNorm g 2 volume := by
  calc
    _ ≤ ∫ x : Space, ‖f x‖ * ‖g x‖ := by
      simpa only [norm_mul] using norm_integral_le_integral_norm (fun x => f x * g x)
    _ = lpNorm (fun x => ‖f x‖ * ‖g x‖) 1 volume := by
      rw [lpNorm_one_eq_integral_norm (f := fun x => ‖f x‖ * ‖g x‖) (hf.norm.1.fun_mul hg.norm.1)]
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ lpNorm (fun x => ‖f x‖) 2 volume * lpNorm (fun x => ‖g x‖) 2 volume :=
      lpNorm_mul_le hf.norm hg.norm
    _ = _ := by rw [lpNorm_norm hf.1, lpNorm_norm hg.1]

theorem lpNorm_congr_ae {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {f g : Space → F}
    (h : f =ᵐ[volume] g) : lpNorm f p volume = lpNorm g p volume := by
  unfold lpNorm
  rw [aestronglyMeasurable_congr h, eLpNorm_congr_ae h]

theorem errorBound_congr_ae {R L : ℝ} {φ : Space → ℝ} {f g : Space → ℂ}
    (h : f =ᵐ[volume] g) : errorBound R L φ f = errorBound R L φ g := by
  have hw : weightedNorm φ f =ᵐ[volume] weightedNorm φ g := by
    filter_upwards [h] with x hx
    simp only [weightedNorm, hx]
  simp only [errorBound, lpNorm_congr_ae hw, lpNorm_congr_ae h]

/-- The actual weighted pressure regularization belongs to `L²`, with a
bound independent of the regularization scale. -/
theorem actual_regularized_weighted {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (hφg : φ.HasTemperateGrowth) (n : ℕ) (i j : Fin 3) {g : Space → ℂ}
    (hg : MemLp g 1) (hw : MemLp (weightedNorm φ g) (3 / 2))
    (hg₂ : MemLp (fun x => powerCutoff φ x * g x) 2) :
    MemLp (fun x => powerCutoff φ x * regularized n i j g x) 2 ∧
      lpNorm (fun x => powerCutoff φ x * regularized n i j g x) 2 volume ≤
        lpNorm (fun x => powerCutoff φ x * g x) 2 volume + errorBound R L φ g := by
  let gLp := hg.toLp g
  have hga : (gLp : Space → ℂ) =ᵐ[volume] g := hg.coeFn_toLp
  have hwa : weightedNorm φ gLp =ᵐ[volume] weightedNorm φ g := by
    filter_upwards [hga] with x hx
    simp only [weightedNorm, hx]
  have h2a : (fun x => powerCutoff φ x * gLp x) =ᵐ[volume] (fun x => powerCutoff φ x * g x) := by
    filter_upwards [hga] with x hx
    rw [hx]
  have hw' := (memLp_congr_ae hwa).mpr hw
  have h2' := (memLp_congr_ae h2a).mpr hg₂
  have hreg := regularized_congr_ae n i j hga
  have hrep := regularizedWeightedPressure_ae hφ hφg n i j gLp hw' h2'
  rw [hreg] at hrep
  refine ⟨(memLp_congr_ae hrep).mp (Lp.memLp _), ?_⟩
  have hb := regularized_weighted_lpNorm_le hφ hφg n i j gLp hw' h2'
  rw [hreg, lpNorm_congr_ae h2a, errorBound_congr_ae hga] at hb
  exact hb

/-- Cauchy--Schwarz pairs the weighted Gaussian pressure with the cutoff
flux factor. -/
theorem regularized_flux_le {R L : ℝ} {φ : Space → ℝ} (hφ : Cutoff R L φ)
    (hφg : φ.HasTemperateGrowth) (n : ℕ) (i j : Fin 3) {g h : Space → ℂ}
    (hg : MemLp g 1) (hw : MemLp (weightedNorm φ g) (3 / 2))
    (hg₂ : MemLp (fun x => powerCutoff φ x * g x) 2) (hh : MemLp h 2) :
    ‖∫ x : Space, powerCutoff φ x * regularized n i j g x * h x‖ ≤
      (lpNorm (fun x => powerCutoff φ x * g x) 2 volume + errorBound R L φ g) *
        lpNorm h 2 volume := by
  obtain ⟨hm, hb⟩ := actual_regularized_weighted hφ hφg n i j hg hw hg₂
  exact (norm_integral_mul_le hm hh).trans
    (mul_le_mul_of_nonneg_right hb lpNorm_nonneg)

end NavierStokes.R3PressureFlux
