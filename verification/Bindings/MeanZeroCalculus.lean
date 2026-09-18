import Contracts.V1.MeanZeroCalculus
import NSFormalization.Section3.T12.TameProduct
import NSFormalization.Section3.T12.FourierEmbeddings
import NSFormalization.Section3.T12.CriticalL3Density
import NSFormalization.Section3.T12.GradientLSix
import NSFormalization.Section3.T12.GradientLambdaL3
import NSFormalization.Section3.T12.SpectralGap

noncomputable section
namespace BlowupDensity.Bindings.MeanZeroCalculus
open BlowupDensity.Contracts.V1.MeanZeroCalculus
open NSFormalization.Section3.T12

theorem periodicScalarSobolevENorm_eq (s : ℝ) (z : Space → ℝ) : periodicScalarSobolevENorm s z = NSFormalization.Section3.T12.periodicScalarSobolevENorm s z := rfl

theorem memPeriodicHmScalar_eq (m : ℕ) (z : Space → ℝ) : MemPeriodicHmScalar m z = NSFormalization.Section3.T12.MemPeriodicHmScalar m z := rfl

theorem memPeriodicHmVector_eq (m : ℕ) (z : SpatialField) : MemPeriodicHmVector m z = NSFormalization.Section3.T12.MemPeriodicHmVector m z := rfl

theorem memPeriodicHomogeneous_eq (s : ℝ) (z : SpatialField) : MemPeriodicHomogeneous s z = NSFormalization.Section3.T12.MemPeriodicHomogeneous s z := rfl

theorem smoothPeriodicT_eq (z : SpatialField) : SmoothPeriodicT z = NSFormalization.Section3.T12.SmoothPeriodicT z := rfl

theorem periodicLpENorm_eq {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞) (z : Space → E) : periodicLpENorm p z = NSFormalization.Section3.T12.periodicLpENorm p z := rfl

theorem lift_eq (v : SpatialField) : lift v = NSFormalization.Section3.T12.lift v := rfl
theorem gradientTensor_eq (v : SpatialField) : gradientTensor v = NSFormalization.Section3.T12.gradientTensor v := rfl
theorem laplacian_eq (v : SpatialField) : laplacian v = NSFormalization.Section3.T12.laplacian v := rfl
theorem isPeriodicLambda_eq (v Lv : SpatialField) : IsPeriodicLambda v Lv = NSFormalization.Section3.T12.IsPeriodicLambda v Lv := rfl

def meanZeroCalculus : MeanZeroSobolevCalculusAPI where
  Cproduct := tameProductConst
  Cproduct_pos := tameProductConst_pos
  Cinfty := linftyConst
  Cinfty_pos := linftyConst_pos
  CcriticalHalf := CcriticalHalf
  CcriticalHalf_pos := CcriticalHalf_pos
  CcriticalThreeHalves := CcriticalThreeHalves
  CcriticalThreeHalves_pos := CcriticalThreeHalves_pos
  Csix := Csix
  Csix_pos := Csix_pos
  CHtwo := hTwoConst
  CHtwo_pos := hTwoConst_pos
  Cgap := gapConst
  Cgap_pos := gapConst_pos
  tameProduct := tameProduct
  boundedRepresentative := boundedRepresentative
  velocityCriticalL3 := velocityCriticalL3
  lambda_exists := lambda_exists
  gradientLambdaCriticalL3 := gradientLambdaCriticalL3
  gradientLSix := gradientLSix
  hTwo_le_laplacian := hTwo_le_laplacian
  spectralGap := spectralGap
  homogeneous_le_sobolev := homogeneous_le_sobolev

theorem meanZeroCalculusStatement_holds : meanZeroCalculusStatement := ⟨meanZeroCalculus⟩
end BlowupDensity.Bindings.MeanZeroCalculus
