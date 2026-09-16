import NSFormalization.Section4.A01.CommutatorBound
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

open EulerSobolevL2Product EulerFamilyNormTime
-- Mutation: reduce four-coordinate constant to three; retain the complete original proof.
theorem rev202_coordinate_constant {q : ℕ} (hq : 6 ≤ q) {C : ℝ}
    (htame : CylinderCoordinateTame q hq C)
    (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q))
    (hV : restrictOperator 1 (by omega : q+1 ≤ 2+q) V = v) :
    familyNorm (cylinderCommutator hq v V) ≤
      (3*C) * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖ * cylinderWordGradient V := by
  rw [cylinderCommutator_eq_sum, familyNorm_eq_piLp, map_sum]
  apply (norm_sum_le _ _).trans
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    htame v V hV i)
  simp only [familyNorm_eq_piLp] at h
  exact h.trans_eq (by simp; ring)
end NSFormalization.Section4.A01
