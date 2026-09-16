import NSFormalization.Section4.A01.ForcingFamilyBound
import Euler.RegularizedForcingRepresentative

/-! Full finite-word forcing: exact cancellation and a single spatial analytic residual.
The constants below are explicit candidate constants; their general-data validity is
conditional on `CylinderCommutatorBound`, not asserted unconditionally. -/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution EulerTimeLp
  EulerRegularizedTopBlocks EulerSobolevMaximalRegularity EulerSobolevWordConstraints
  EulerTimeSobolevTransport EulerAsymmetricTransport EulerSobolevTransport
  EulerRegularizedEnergyFamily EulerTransportL2Time EulerRegularizedMetricPaths
  EulerWeightedCylinderEnergy EulerFiniteMetricEnergy EulerMildTopWord
  EulerSobolevWordValueIdentity EulerSobolevEnergyPaths
open NSFormalization.Source.ForcedCylinderLocal
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Full dependent word-family elaboration needs extra reduction fuel.
set_option maxHeartbeats 400000 in
/-- The original Z is exactly the physical force-word family plus the commutator.
This identity holds without a mild equation or a choice of maximal limit. -/
theorem rev200_forcing_sign {q : ℕ} (hq : 6 ≤ q) {S T : ℝ}
    (hT : 0 ≤ T) (hTS : T ≤ S)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (U : TimeLp T (SobolevSpace 1 (2+q))) :
    (cylinderEnergyForcing hq hT hTS F hF u U : ℝ → ℝ) =ᵐ[timeMeasure T]
      fun r => familyNorm ((extendPath T hT
        ((sobolevPath F hF (q+1)).comp (timeInclusion hTS)) r).val -
        cylinderCommutator hq (extendPath T hT u r) (U r)) := by
  let f := sobolevPath F hF (q+1)
  let V := reindexMaximalTime 1 q T U
  have hz := energyForcingNorm_ae hq hT u U
    (ForcedSourceUpgrade.sourceTime hq hT hTS f u V)
    (energyPressureTime hq hT hTS f u V)
  filter_upwards [hz, sourceTime_add_pressureTime_ae hq hT hTS f u V,
    (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q)).coeFn_compLpL U]
    with r hz hc hv
  rw [show cylinderEnergyForcing hq hT hTS F hF u U r = _ from hz]
  apply congrArg familyNorm
  change V r = _ at hv
  have hb := congrArg (fun z : SobolevSpace 1 ((q+1)+1) =>
    extendPath T hT (f.comp (timeInclusion hTS)) r -
      asymmetricTransport 1 (by omega : 6 ≤ q+1) (velocityComponents 1 0)
        (velocityComponents_norm 1 0 (by norm_num) (by simp)) (extendPath T hT u r) z) hv
  exact forcing_array_rearrange _ _ _ _ _ (hc.trans hb)

end NSFormalization.Section4.A01
