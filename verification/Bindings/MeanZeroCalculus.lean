import Contracts.V1.MeanZeroCalculus
import NSFormalization.Section3.T12.TameProduct
import NSFormalization.Section3.T12.FourierEmbeddings
import NSFormalization.Section3.T12.CriticalL3Density
import NSFormalization.Section3.T12.GradientLSix
import NSFormalization.Section3.T12.GradientLambdaL3
import NSFormalization.Section3.T12.SpectralGap

/-!
# Binding for the T12 mean-zero periodic Sobolev calculus contract

The only layer that knows the current implementation's names and paths.  Each
of the eleven definitions the contract writes out is guarded by a `rfl` bridge
against its canonical `NSFormalization.Section3.T12` source, and the nine API
fields plus the seven constants are assembled from the named theorems of the
six canonical proof modules.

The periodic data vocabulary the contract inherits from `Contracts.V1.TorusData`
is already bridged in `Bindings/TorusData.lean`; the three derivative spellings
are also bridged in `Bindings/GradientL6.lean`, and the contract itself records
by `rfl` that its copies are the registered ones.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.MeanZeroCalculus
open scoped ContDiff ENNReal BigOperators

/-! ## 1. Definitional drift guards

One bridge per definition restated in `Contracts/V1/MeanZeroCalculus.lean`. -/

theorem meanZero_isPeriodicScalarDatum_eq :
    IsPeriodicScalarDatum =
      NSFormalization.Section3.T12.IsPeriodicScalarDatum := rfl

theorem meanZero_periodicScalarSobolevENorm_eq :
    periodicScalarSobolevENorm =
      NSFormalization.Section3.T12.periodicScalarSobolevENorm := rfl

theorem meanZero_memPeriodicHmScalar_eq :
    MemPeriodicHmScalar =
      NSFormalization.Section3.T12.MemPeriodicHmScalar := rfl

theorem meanZero_memPeriodicHmVector_eq :
    MemPeriodicHmVector =
      NSFormalization.Section3.T12.MemPeriodicHmVector := rfl

theorem meanZero_memPeriodicHomogeneous_eq :
    MemPeriodicHomogeneous =
      NSFormalization.Section3.T12.MemPeriodicHomogeneous := rfl

theorem meanZero_smoothPeriodicT_eq :
    SmoothPeriodicT = NSFormalization.Section3.T12.SmoothPeriodicT := rfl

/-- Pointwise because a bare equality leaves the implicit normed codomain `E`
and its instance unconstrained. -/
theorem meanZero_periodicLpENorm_eq {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (z : Space → E) :
    periodicLpENorm p z = NSFormalization.Section3.T12.periodicLpENorm p z := rfl

theorem meanZero_lift_eq :
    Contracts.V1.MeanZeroCalculus.lift = NSFormalization.Section3.T12.lift := rfl

theorem meanZero_gradientTensor_eq :
    Contracts.V1.MeanZeroCalculus.gradientTensor =
      NSFormalization.Section3.T12.gradientTensor := rfl

theorem meanZero_laplacian_eq :
    Contracts.V1.MeanZeroCalculus.laplacian = NSFormalization.Section3.T12.laplacian := rfl

theorem meanZero_isPeriodicLambda_eq :
    IsPeriodicLambda = NSFormalization.Section3.T12.IsPeriodicLambda := rfl

/-! ## 2. The transported nine-field record

The constants are the closed terms of the canonical modules, not numerals:
`tameProductConst m = 4^(m/2) · sqrt(∑ₖ W(k)⁻²)`,
`linftyConst = sqrt(∑ₖ W(k)⁻²)`,
`CcriticalHalf = criticalL3Const · cutoffGagliardoConst · (gapConst (1/2) + 1)`,
`CcriticalThreeHalves = 4 · CcriticalHalf`,
`Csix = 343 · gradientL6Const · leibnizConst · (1 + 2 · hTwoConst)`,
`hTwoConst = 1 + 1/(4π²)` and `gapConst s = (1 + 1/(4π²))^(s/2)`. -/

/-- The declaration registered for T12: the proved canonical record,
transported field by field into the stable version-one specification. -/
def meanZeroCalculus : MeanZeroSobolevCalculusAPI where
  Cproduct := NSFormalization.Section3.T12.tameProductConst
  Cproduct_pos := NSFormalization.Section3.T12.tameProductConst_pos
  Cinfty := NSFormalization.Section3.T12.linftyConst
  Cinfty_pos := NSFormalization.Section3.T12.linftyConst_pos
  CcriticalHalf := NSFormalization.Section3.T12.CcriticalHalf
  CcriticalHalf_pos := NSFormalization.Section3.T12.CcriticalHalf_pos
  CcriticalThreeHalves := NSFormalization.Section3.T12.CcriticalThreeHalves
  CcriticalThreeHalves_pos := NSFormalization.Section3.T12.CcriticalThreeHalves_pos
  Csix := NSFormalization.Section3.T12.Csix
  Csix_pos := NSFormalization.Section3.T12.Csix_pos
  CHtwo := NSFormalization.Section3.T12.hTwoConst
  CHtwo_pos := NSFormalization.Section3.T12.hTwoConst_pos
  Cgap := NSFormalization.Section3.T12.gapConst
  Cgap_pos := NSFormalization.Section3.T12.gapConst_pos
  tameProduct := NSFormalization.Section3.T12.tameProduct
  boundedRepresentative := NSFormalization.Section3.T12.boundedRepresentative
  velocityCriticalL3 := NSFormalization.Section3.T12.velocityCriticalL3
  lambda_exists := NSFormalization.Section3.T12.lambda_exists
  gradientLambdaCriticalL3 := NSFormalization.Section3.T12.gradientLambdaCriticalL3
  gradientLSix := NSFormalization.Section3.T12.gradientLSix
  hTwo_le_laplacian := NSFormalization.Section3.T12.hTwo_le_laplacian
  spectralGap := NSFormalization.Section3.T12.spectralGap
  homogeneous_le_sobolev := NSFormalization.Section3.T12.homogeneous_le_sobolev

/-- The registered statement form of the contract. -/
theorem meanZeroCalculusStatement_holds : meanZeroCalculusStatement :=
  ⟨meanZeroCalculus⟩

end BlowupDensity.Bindings
