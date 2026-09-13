import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.MeasureTheory.Function.Holder

/-! Singular multiplication on actual L2 data, using Mathlib's Holder bilinear maps. -/
noncomputable section
namespace NSFormalization.SingularMultiplier
open MeasureTheory
open scoped ENNReal SchwartzMap
abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Data (p : ℝ≥0∞) := Lp ℂ p (volume : Measure Space)

def lowProduct (low : Data 2) : Data 2 →L[ℂ] Data 1 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume 2 2 1 low

def highProduct (high : Data ⊤) : Data 2 →L[ℂ] Data 2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2 high

def distribution (low : Data 2) (high : Data ⊤) : Data 2 →L[ℂ] 𝓢'(Space, ℂ) :=
  (Lp.toTemperedDistributionCLM ℂ volume 1).comp (lowProduct low) +
  (Lp.toTemperedDistributionCLM ℂ volume 2).comp (highProduct high)

theorem lowProduct_ae (low h : Data 2) :
    (lowProduct low h : Space → ℂ) =ᵐ[volume] fun x => low x * h x :=
  (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder low h

theorem highProduct_ae (high : Data ⊤) (h : Data 2) :
    (highProduct high h : Space → ℂ) =ᵐ[volume] fun x => high x * h x :=
  (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder high h

theorem distribution_pairing (low : Data 2) (high : Data ⊤) (h : Data 2)
    (φ : 𝓢(Space, ℂ)) :
    distribution low high h φ =
      (∫ x, φ x * (low x * h x)) + (∫ x, φ x * (high x * h x)) := by
  change Lp.toTemperedDistribution (lowProduct low h) φ +
    Lp.toTemperedDistribution (highProduct high h) φ = _
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
  congr 1
  · apply integral_congr_ae
    filter_upwards [lowProduct_ae low h] with x hx
    simp [hx, smul_eq_mul]
  · apply integral_congr_ae
    filter_upwards [highProduct_ae high h] with x hx
    simp [hx, smul_eq_mul]

end NSFormalization.SingularMultiplier
