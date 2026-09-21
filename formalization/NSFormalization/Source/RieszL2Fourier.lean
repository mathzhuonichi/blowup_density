import NSFormalization.Source.RieszPotentialOperator
import NSFormalization.Source.RieszSingularMultiplier
import NSFormalization.Source.RieszConvolutionFourier
import Mathlib.Analysis.Fourier.LpSpace
import NSFormalization.Source.RieszKernelNormalization

/-! The physical Riesz operator and singular Fourier multiplier agree on every L2 datum. -/
noncomputable section
namespace NSFormalization.RieszL2Fourier
open MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal
open NSFormalization.RieszPotentialOperator NSFormalization.RieszSingularMultiplier
open NSFormalization.RieszPotentialLp
abbrev Space := EuclideanSpace ℝ (Fin 3)

def physicalFourier {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2) :
    Lp ℂ 2 (volume : Measure Space) →L[ℂ] 𝓢'(Space, ℂ) := by
  letI : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) := ⟨targetExponent_one_le ha ha3⟩
  exact (fourierCLM ℂ 𝓢'(Space, ℂ)).comp
    ((Lp.toTemperedDistributionCLM ℂ volume (ENNReal.ofReal (targetExponent a))).comp
      (potentialOperator ha ha3))

def frequencyMultiplier {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2) :
    Lp ℂ 2 (volume : Measure Space) →L[ℂ] 𝓢'(Space, ℂ) :=
  (NSFormalization.Source.RieszFourierProfilePower.constant a : ℂ) •
    (multiplier a ha.le ha3).comp (fourierCLM ℂ (Lp ℂ 2 (volume : Measure Space)))

theorem schwartz_commutes {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    (g : 𝓢(Space, ℂ)) :
    physicalFourier ha ha3 (g.toLp 2 volume) = frequencyMultiplier ha ha3 (g.toLp 2 volume) := by
  letI : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) := ⟨targetExponent_one_le ha ha3⟩
  ext φ
  change Lp.toTemperedDistribution (potentialOperator ha ha3 (g.toLp 2 volume)) (𝓕 φ) =
    (NSFormalization.Source.RieszFourierProfilePower.constant a : ℂ) *
      multiplier a ha.le ha3 (𝓕 (g.toLp 2 volume)) φ
  rw [Lp.toTemperedDistribution_apply, SchwartzMap.toLp_fourier_eq, multiplier_pairing]
  have hp := potentialOperator_coe_ae ha ha3 (g.toLp 2 volume)
  have he := NSFormalization.RieszComplexPotential.complexPotential_congr_ae (g.coeFn_toLp 2 volume) a
  calc
    _ = ∫ x : Space, NSFormalization.RieszComplexPotential.complexPotential a g x * (𝓕 φ) x := by
      apply integral_congr_ae
      filter_upwards [hp] with x hx
      simp only [smul_eq_mul, hx, he]
      ring
    _ = _ := by
      rw [NSFormalization.Source.RieszConvolutionFourier.schwartz_potential_fourier_pairing ha (by linarith), ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [(𝓕 g).coeFn_toLp 2 volume] with x hx
      simp only [hx, NSFormalization.RieszFrequencyCutoffs.symbol, Complex.ofReal_mul]
      ring

theorem commuting_square {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    (g : Lp ℂ 2 (volume : Measure Space)) :
    physicalFourier ha ha3 g = frequencyMultiplier ha ha3 g := by
  refine (SchwartzMap.denseRange_toLpCLM (E := Space) (F := ℂ) (p := 2)
    (μ := volume) ENNReal.ofNat_ne_top).induction_on g
    (isClosed_eq (physicalFourier ha ha3).continuous (frequencyMultiplier ha ha3).continuous) ?_
  exact schwartz_commutes ha ha3
/-- Conventional physical normalization gives the exact angular fractional symbol,
expressed in the cycles-frequency convention, for arbitrary L2 data. -/
theorem normalized_commuting_square {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    (g : Lp ℂ 2 (volume : Measure Space)) :
    (NSFormalization.Source.RieszKernelNormalization.coefficient a : ℂ) •
      physicalFourier ha ha3 g = normalizedMultiplier a ha.le ha3 (𝓕 g) := by
  rw [commuting_square]
  change (NSFormalization.Source.RieszKernelNormalization.coefficient a : ℂ) •
    ((NSFormalization.Source.RieszFourierProfilePower.constant a : ℂ) •
      multiplier a ha.le ha3 (𝓕 g)) = _
  rw [smul_smul, ← Complex.ofReal_mul,
    NSFormalization.Source.RieszKernelNormalization.coefficient_mul_constant ha (by linarith)]
  rfl
end NSFormalization.RieszL2Fourier
