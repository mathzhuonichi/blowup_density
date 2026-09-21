import Euler.LpSmoothFieldAlgebra
import NSFormalization.Paper3.SobolevHilbertModel
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Physical smooth L² fields as tempered distributions, without a support or L¹
assumption. The order-zero Fourier datum retains the actual physical field. -/
noncomputable section
namespace NSFormalization.Source.PhysicalSobolevDistribution
open MeasureTheory FourierTransform EulerLpTranslation NavierStokes.ProblemStatement
open NSFormalization.Paper3
open scoped SchwartzMap LineDeriv ENNReal ContDiff

/-- The tempered distribution of the actual L² class. -/
def physicalDistribution (A : SmoothL2Field ℂ) : 𝓢'(Space, ℂ) :=
  (A.toLp : 𝓢'(Space, ℂ))

 theorem physicalDistribution_apply (A : SmoothL2Field ℂ) (φ : 𝓢(Space, ℂ)) :
    physicalDistribution A φ = ∫ x, φ x • A.field x := by
  rw [physicalDistribution, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [A.toLp_ae] with x hx
  rw [hx]

 theorem schwartz_smul_field_integrable (A : SmoothL2Field ℂ) (φ : 𝓢(Space, ℂ)) :
    Integrable (fun x => φ x • A.field x) := by
  exact memLp_one_iff_integrable.mp (A.memLp.smul (φ.memLp 2))

/-- Classical directional differentiation agrees with distributional differentiation. -/
theorem physicalDistribution_directionalField (A : SmoothL2Field ℂ) (v : Space) :
    physicalDistribution (A.directionalField v) = ∂_{v} (physicalDistribution A) := by
  ext φ
  rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg]
  rw [physicalDistribution_apply, physicalDistribution_apply]
  exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (schwartz_smul_field_integrable A (∂_{v} φ))
    (schwartz_smul_field_integrable (A.directionalField v) φ)
    (schwartz_smul_field_integrable A φ)
    (fun x _ => φ.differentiableAt)
    (fun x _ => A.smooth.differentiable (by simp) x)

/-- Explicit H⁰ datum, formed using the L² Fourier transform. -/
def physicalH0Datum (A : SmoothL2Field ℂ) : SobolevHilbert 0 := 𝓕 A.toLp

@[simp] theorem physicalH0Datum_realization (A : SmoothL2Field ℂ) :
    sobolevRealization 0 (physicalH0Datum A) = physicalDistribution A := by
  rw [sobolevRealization_zero, physicalH0Datum, fourierInv_fourier_eq]
  rfl

@[simp] theorem norm_physicalH0Datum (A : SmoothL2Field ℂ) :
    ‖physicalH0Datum A‖ = ‖A.toLp‖ := Lp.norm_fourier_eq A.toLp

 theorem continuous_physicalH0Datum {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field ℂ) (hA : Continuous (fun t => (A t).jetLp 0)) :
    Continuous (fun t => physicalH0Datum (A t)) :=
  (fourierCLM ℂ (Lp ℂ 2 (volume : Measure Space))).continuous.comp
    (SmoothL2Field.continuous_toLp A hA)

 theorem continuous_norm_physicalH0Datum {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field ℂ) (hA : Continuous (fun t => (A t).jetLp 0)) :
    Continuous (fun t => ‖physicalH0Datum (A t)‖) :=
  (continuous_physicalH0Datum A hA).norm

end NSFormalization.Source.PhysicalSobolevDistribution
