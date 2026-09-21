import NSFormalization.Paper3.SobolevHilbertModel
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section
namespace NSFormalization.Source.WeakClassicalDerivative
open MeasureTheory NavierStokes.ProblemStatement
open scoped SchwartzMap LineDeriv ENNReal ContDiff

/-- A C1 representative's classical derivative agrees with every L2
representative of its distributional derivative. No support premise is used. -/
theorem ae_eq_classical_derivative {f : Space → ℂ} (hf : ContDiff ℝ 1 f)
    (u v : Lp ℂ 2 (volume : Measure Space)) (a : Space)
    (hu : (u : Space → ℂ) =ᵐ[volume] f)
    (hderiv : ∂_{a} (u : 𝓢'(Space, ℂ)) = (v : 𝓢'(Space, ℂ))) :
    (v : Space → ℂ) =ᵐ[volume] (fun x => fderiv ℝ f x a) := by
  have hDf : Continuous (fun x => fderiv ℝ f x a) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp v).locallyIntegrable (by norm_num)) hDf.locallyIntegrable
  intro g hg hgc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let ψ : SchwartzMap Space ℂ := hg₁.toSchwartzMap hg₂
  have hψc : HasCompactSupport (ψ : Space → ℂ) := hg₁
  have hDψ : Continuous (fun x => fderiv ℝ (ψ : Space → ℂ) x a) :=
    ((ψ.smooth 1).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h₁ : Integrable (fun x => fderiv ℝ (ψ : Space → ℂ) x a • f x) volume :=
    (hDψ.smul hf.continuous).integrable_of_hasCompactSupport (hψc.fderiv_apply ℝ a).smul_right
  have h₂ : Integrable (fun x => ψ x • fderiv ℝ f x a) volume :=
    (ψ.continuous.smul hDf).integrable_of_hasCompactSupport hψc.smul_right
  have h₃ : Integrable (fun x => ψ x • f x) volume :=
    (ψ.continuous.smul hf.continuous).integrable_of_hasCompactSupport hψc.smul_right
  have hibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable h₁ h₂ h₃
    (fun x _ => ψ.differentiableAt) (fun x _ => hf.differentiable (by norm_num) x)
  calc
    (∫ x : Space, g x • v x) = (v : 𝓢'(Space, ℂ)) ψ := by simp [ψ]
    _ = -(u : 𝓢'(Space, ℂ)) (∂_{a} ψ) := by
      rw [← hderiv, TemperedDistribution.lineDerivOp_apply_apply, map_neg]
    _ = -∫ x : Space, fderiv ℝ (ψ : Space → ℂ) x a • f x := by
      rw [Lp.toTemperedDistribution_apply]
      apply congrArg Neg.neg
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [hx, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    _ = ∫ x : Space, ψ x • fderiv ℝ f x a := hibp.symm
    _ = ∫ x : Space, g x • fderiv ℝ f x a := by simp [ψ]

/-- L2 membership of the actual classical derivative follows from the weak
L2 derivative and C1 regularity, rather than being assumed. -/
theorem classical_derivative_memLp {f : Space → ℂ} (hf : ContDiff ℝ 1 f)
    (u v : Lp ℂ 2 (volume : Measure Space)) (a : Space)
    (hu : (u : Space → ℂ) =ᵐ[volume] f)
    (hderiv : ∂_{a} (u : 𝓢'(Space, ℂ)) = (v : 𝓢'(Space, ℂ))) :
    MemLp (fun x => fderiv ℝ f x a) 2 volume :=
  (memLp_congr_ae (ae_eq_classical_derivative hf u v a hu hderiv)).mp (Lp.memLp v)

end NSFormalization.Source.WeakClassicalDerivative
