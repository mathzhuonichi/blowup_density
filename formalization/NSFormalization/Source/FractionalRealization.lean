import NSFormalization.Source.BesselFractionalData
import NSFormalization.Source.RieszL2Fourier

/-!
# Physical fractional realization of complete Sobolev data

The Bessel fractional datum is a frequency-space datum. Its inverse Fourier
transform is the physical L2 input to the Riesz potential. Dividing by the
proved Fourier kernel constant then realizes exactly the original tempered
distribution. This identifies the field controlled by the potential estimate.
The convention here is cycles frequency; angular normalization is separate.
-/
noncomputable section
namespace NSFormalization.Source.FractionalRealization

open MeasureTheory FourierTransform
open NSFormalization.Paper3
open NSFormalization.Source.BesselFractionalData
open NSFormalization.RieszPotentialLp NSFormalization.RieszPotentialOperator
open NSFormalization.RieszL2Fourier
open scoped ENNReal SchwartzMap

abbrev Space := EuclideanSpace ℝ (Fin 3)

def physicalInput (a : ℝ) (ha : 0 ≤ a) :
    SobolevHilbert a →L[ℂ] Lp ℂ 2 (volume : Measure Space) :=
  (fourierInvCLM ℂ (Lp ℂ 2 (volume : Measure Space))).comp (datum a ha)

theorem fourier_physicalInput (a : ℝ) (ha : 0 ≤ a) (h : SobolevHilbert a) :
    𝓕 (physicalInput a ha h) = datum a ha h :=
  fourier_fourierInv_eq _

theorem norm_physicalInput (a : ℝ) (ha : 0 ≤ a) (h : SobolevHilbert a) :
    ‖physicalInput a ha h‖ = ‖datum a ha h‖ := by
  rw [← Lp.norm_fourier_eq, fourier_physicalInput]

theorem kernelConstant_pos {a : ℝ} (ha : 0 < a) (ha3 : a < 3 / 2) :
    0 < RieszFourierProfilePower.constant a := by
  unfold RieszFourierProfilePower.constant
  have h1 := Real.Gamma_pos_of_pos (show 0 < a / 2 by linarith)
  have h2 := Real.Gamma_pos_of_pos (show 0 < (3 - a) / 2 by linarith)
  positivity

def realization {a : ℝ} (ha : 0 < a) (ha3 : a < 3 / 2) :
    letI : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) :=
      ⟨targetExponent_one_le ha ha3⟩
    SobolevHilbert a →L[ℂ]
      Lp ℂ (ENNReal.ofReal (targetExponent a)) (volume : Measure Space) := by
  letI : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) :=
    ⟨targetExponent_one_le ha ha3⟩
  exact (RieszFourierProfilePower.constant a : ℂ)⁻¹ •
    (potentialOperator ha ha3).comp (physicalInput a ha.le)

theorem potential_toDistribution {a : ℝ} (ha : 0 < a) (ha3 : a < 3 / 2)
    (h : SobolevHilbert a) :
    letI : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) :=
      ⟨targetExponent_one_le ha ha3⟩
    (potentialOperator ha ha3 (physicalInput a ha.le h) : 𝓢'(Space, ℂ)) =
      (RieszFourierProfilePower.constant a : ℂ) • sobolevRealization a h := by
  letI : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) :=
    ⟨targetExponent_one_le ha ha3⟩
  apply (fourierEquiv ℂ 𝓢'(Space, ℂ)).injective
  change 𝓕 (Lp.toTemperedDistribution
    (potentialOperator ha ha3 (physicalInput a ha.le h))) =
      𝓕 ((RieszFourierProfilePower.constant a : ℂ) • sobolevRealization a h)
  rw [fourier_smul]
  have hc := commuting_square ha ha3 (physicalInput a ha.le h)
  change 𝓕 (Lp.toTemperedDistribution
    (potentialOperator ha ha3 (physicalInput a ha.le h))) =
      (RieszFourierProfilePower.constant a : ℂ) •
        NSFormalization.RieszSingularMultiplier.multiplier a ha.le ha3
          (𝓕 (physicalInput a ha.le h)) at hc
  rw [fourier_physicalInput, multiplier_datum] at hc
  exact hc

/-- The bounded Lp realization is the original Sobolev distribution, with no
assumed physical/Fourier identification. -/
theorem realization_toDistribution {a : ℝ} (ha : 0 < a) (ha3 : a < 3 / 2)
    (h : SobolevHilbert a) :
    letI : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) :=
      ⟨targetExponent_one_le ha ha3⟩
    (realization ha ha3 h : 𝓢'(Space, ℂ)) = sobolevRealization a h := by
  letI : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) :=
    ⟨targetExponent_one_le ha ha3⟩
  have hc : (RieszFourierProfilePower.constant a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (kernelConstant_pos ha ha3).ne'
  change (Lp.toTemperedDistributionCLM ℂ volume (ENNReal.ofReal (targetExponent a)))
    ((RieszFourierProfilePower.constant a : ℂ)⁻¹ •
      potentialOperator ha ha3 (physicalInput a ha.le h)) = _
  rw [map_smul]
  change (RieszFourierProfilePower.constant a : ℂ)⁻¹ •
    (potentialOperator ha ha3 (physicalInput a ha.le h) : 𝓢'(Space, ℂ)) = _
  rw [potential_toDistribution ha ha3, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- The bound retains the actual homogeneous derivative datum. -/
theorem realization_norm_le_datum {a : ℝ} (ha : 0 < a) (ha3 : a < 3 / 2)
    (h : SobolevHilbert a) :
    letI : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) :=
      ⟨targetExponent_one_le ha ha3⟩
    ‖realization ha ha3 h‖ ≤
      ‖(RieszFourierProfilePower.constant a : ℂ)⁻¹‖ *
        (potentialConstant a * (512 : ℝ) ^ (1 / targetExponent a)) *
          ‖datum a ha.le h‖ := by
  letI : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) :=
    ⟨targetExponent_one_le ha ha3⟩
  change ‖(RieszFourierProfilePower.constant a : ℂ)⁻¹ •
    potentialOperator ha ha3 (physicalInput a ha.le h)‖ ≤ _
  rw [norm_smul]
  calc
    _ ≤ ‖(RieszFourierProfilePower.constant a : ℂ)⁻¹‖ *
      ((potentialConstant a * (512 : ℝ) ^ (1 / targetExponent a)) *
        ‖physicalInput a ha.le h‖) :=
      mul_le_mul_of_nonneg_left (potentialOperator_norm_le ha ha3 _) (norm_nonneg _)
    _ = _ := by rw [norm_physicalInput]; ring

end NSFormalization.Source.FractionalRealization
