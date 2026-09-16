import NSFormalization.Section4.A01.CommutatorBound

noncomputable section
namespace NSFormalization.Section4.A01

open EulerCylinderSobolevSpace

-- Deliberate substantive mutation: flip the sign of the coordinate sum.
-- The proof of the actual decomposition must not typecheck against this target.
example {q : ℕ} (hq : 6 ≤ q)
    (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)) :
    cylinderCommutator hq v V =
      -(∑ i : Fin 4, cylinderCoordinateCommutator hq v V i) := by
  exact cylinderCommutator_eq_sum hq v V

end NSFormalization.Section4.A01
