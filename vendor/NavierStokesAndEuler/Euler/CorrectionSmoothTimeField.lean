import Euler.FieldTowerSmoothTimeField
import Euler.AllOrderDriftPressureBounds
import Euler.SmoothTimeFieldAlgebra
import Euler.LiftedSmoothTimeField

/-! The constructed all-order correction and its true time derivative
are actual smooth bounded cover coefficients. Their quantitative bounds
come from the checked weighted Sobolev estimates. -/

noncomputable section


namespace EulerAllOrderDriftCorrection

open Set EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerCylinderSobolevSpace
  EulerCylinderCoordinates EulerLiftedSmoothTimeField
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : Data P T}

private local instance (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ] Vector3) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Vector3) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Vector3)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Vector3)) := inferInstance

def Budget.correctionCoefficient (B : Budget P hT A) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Vector3 :=
  (B.fieldTower P).toSmoothTimeField

def Budget.correctionDerivativeCoefficient (B : Budget P hT A) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Vector3 :=
  (B.timeDerivativeTower P).toSmoothTimeField

theorem Budget.correctionCoefficient_timeDerivative (B : Budget P hT A) :
    SmoothTimeField.TimeDerivative T hT.le (B.correctionCoefficient P)
      (B.correctionDerivativeCoefficient P) :=
  (B.fieldTower P).toSmoothTimeField_timeDerivative_of_interior (B.timeDerivativeTower P)
    hT.le 6 (by norm_num) (B.fieldTower_hasDerivAt_timeDerivativeTower P 6 le_rfl)

theorem Budget.correctionCoefficient_jet_bound (B : Budget P hT A) (n : ℕ) :
    ‖(B.correctionCoefficient P).jet n‖ ≤
      (sobolevEmbeddingConstant P 3 * B.correctionSize P) *
        (‖coordinateEquiv.symm.toContinuousLinearMap‖ * (B.reducedRadius P)⁻¹)^n *
          (n.factorial : ℝ)^2 :=
  (B.fieldTower P).toSmoothTimeField_jet_weighted n (B.reducedRadius P)
    (B.correctionSize P) (B.reducedRadius_pos P) (B.correctionSize_nonneg P)
    (B.fieldTower_reducedNorm P (n+6) n le_rfl)

theorem Budget.correctionDerivativeCoefficient_jet_bound (B : Budget P hT A)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ (n : ℕ) (t : Icc (0 : ℝ) T),
      EulerSobolevGevreyOperators.weightedNorm P 6 n (B.reducedRadius P)
        ((B.timeDerivativeTower P).realization (n+6) t) ≤ C) (n : ℕ) :
    ‖(B.correctionDerivativeCoefficient P).jet n‖ ≤
      (sobolevEmbeddingConstant P 3 * C) *
        (‖coordinateEquiv.symm.toContinuousLinearMap‖ * (B.reducedRadius P)⁻¹)^n *
          (n.factorial : ℝ)^2 :=
  (B.timeDerivativeTower P).toSmoothTimeField_jet_weighted n (B.reducedRadius P)
    C (B.reducedRadius_pos P) hC (hb n)

end EulerAllOrderDriftCorrection
