import NSFormalization.Source.OrdinaryForcedTime

noncomputable section
namespace NSFormalization.Source.OrdinaryForcedEvolution
open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
open NSFormalization.Source.OrdinaryForcedTime
open scoped Topology

/-- Closed-interval ordinary derivative as a continuous path, including both endpoints. -/
def derivativePath {q : ℕ} (hq : 6 ≤ q) (ν : ℝ) {S T : ℝ}
    (hTS : T ≤ S) (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))) :
    C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2) :=
  ⟨ordinaryDerivative hq ν hTS f u, ordinaryDerivative_continuous hq ν hTS f u⟩

/-- Clamping the derived derivative path gives a continuous ambient time path. This is
an extension of the derivative values, not a derivative claim outside the lifespan. -/
theorem extended_derivative_continuous {q : ℕ} (hq : 6 ≤ q) (ν : ℝ) {S T : ℝ}
    (hT : 0 ≤ T) (hTS : T ≤ S) (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))) :
    Continuous (fun t : ℝ => derivativePath hq ν hTS f u (projIcc 0 T hT t)) :=
  (derivativePath hq ν hTS f u).continuous.comp continuous_projIcc

end NSFormalization.Source.OrdinaryForcedEvolution

