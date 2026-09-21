import NSFormalization.Source.TimeNormScaling

/-! Spatial translation invariance of the actual Fourier Sobolev norms. -/
noncomputable section
namespace NSFormalization.Source
open NavierStokes.ProblemStatement MeasureTheory
open scoped FourierTransform RealInnerProductSpace

theorem fourier_translate (f : Space → ℂ) (x₀ ξ : Space) :
    𝓕 (fun x => f (x - x₀)) ξ = 𝐞 (-inner ℝ x₀ ξ) • 𝓕 f ξ := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right
    𝐞 volume (innerₗ Space) f (-x₀)) ξ
  simp only [Real.fourier_eq]
  simpa only [VectorFourier.fourierIntegral, Function.comp_apply,
    innerₗ_apply_apply, ← sub_eq_add_neg, LinearMap.map_neg,
    LinearMap.neg_apply, inner_neg_left] using h

theorem norm_fourier_translate (f : Space → ℂ) (x₀ ξ : Space) :
    ‖𝓕 (fun x => f (x - x₀)) ξ‖ = ‖𝓕 f ξ‖ := by
  rw [fourier_translate, Circle.norm_smul]

theorem fourierSobolevNorm_translate (s : ℝ) (f : Space → ℂ) (x₀ : Space) :
    fourierSobolevNorm s (fun x => f (x - x₀)) = fourierSobolevNorm s f := by
  unfold fourierSobolevNorm fourierSobolevSq
  simp_rw [norm_fourier_translate]

theorem homogeneousFourierNorm_translate (s : ℝ) (f : Space → ℂ) (x₀ : Space) :
    homogeneousFourierNorm s (fun x => f (x - x₀)) = homogeneousFourierNorm s f := by
  unfold homogeneousFourierNorm
  simp_rw [norm_fourier_translate]

end NSFormalization.Source
