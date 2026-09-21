import NSFormalization.Source.OrdinaryForcedLocal
import Euler.MildEquationBridge

/-! The actual ordinary L2 interior time law, derived from the forced mild witness. -/
noncomputable section
namespace NSFormalization.Source.OrdinaryForcedTime
open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
open EulerQuadraticSource EulerSobolevHeatGenerator EulerVolterraConvolution
open EulerMeanOrdinaryLift NSFormalization.Source.ForcedCylinderLocal
open NSFormalization.Source.OrdinaryCylinderDescent
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The actual projected cylinder evolution, observed in ordinary L2 by the source lift adjoint. -/
def ordinaryDerivative {q : ℕ} (hq : 6 ≤ q) (ν : ℝ) {S T : ℝ} (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (t : Icc (0 : ℝ) T) : EulerMeanSolenoidal.L2 :=
  ordinaryLift.toContinuousLinearMap.adjoint
    (ν • laplacianEvaluation 1 (q + 1) (by omega) (u t) +
      value 1 ((coefficients 1 hq f).apply (timeInclusion hTS t) (u t)))

/-- The derivative path is continuous as a consequence of the actual finite-order mild data. -/
theorem ordinaryDerivative_continuous {q : ℕ} (hq : 6 ≤ q) (ν : ℝ) {S T : ℝ} (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))) :
    Continuous (ordinaryDerivative hq ν hTS f u) := by
  apply ordinaryLift.toContinuousLinearMap.adjoint.continuous.comp
  apply Continuous.add
  · exact ((laplacianEvaluation 1 (q + 1) (by omega)).continuous.comp u.continuous).const_smul ν
  · exact (valueOperator 1 q).continuous.comp
      (((coefficients 1 hq f).comp (timeInclusion hTS)).continuous.comp
        (continuous_id.prodMk u.continuous))

/-- An actual forced Duhamel witness supplies its ordinary L2 time derivative; no time law is assumed. -/
theorem ordinary_hasDerivAt {q : ℕ} (hq : 6 ≤ q) {ν S T : ℝ} (hν : 0 < ν)
    (hT : 0 ≤ T) (hTS : T ≤ S) (u₀ : SobolevSpace 1 (q + 1))
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (hsol : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS (coefficients 1 hq f) u₀ u t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => ordinaryValue (q + 1) (extendPath T hT u r))
      (ordinaryDerivative hq ν hTS f u ⟨t, ht.1.le, ht.2.le⟩) t := by
  let C := (coefficients 1 hq f).comp (timeInclusion hTS)
  have hd := EulerMildEquationBridge.viscous_mild_hasDerivAt 1 (by omega : 2 ≤ q)
    ν hν T hT u₀ C.apply C.continuous u hsol t ht
  exact ordinaryLift.toContinuousLinearMap.adjoint.hasFDerivAt.comp_hasDerivAt t hd

/-- The continuous ordinary realization returned by local existence has the same derived time law. -/
theorem realization_hasDerivAt {q : ℕ} (hq : 6 ≤ q) {ν S T : ℝ} (hν : 0 < ν)
    (hT : 0 ≤ T) (hTS : T ≤ S) (u₀ : SobolevSpace 1 (q + 1))
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hsol : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS (coefficients 1 hq f) u₀ u t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT U)
      (ordinaryDerivative hq ν hTS f u ⟨t, ht.1.le, ht.2.le⟩) t := by
  have he (s : Icc (0 : ℝ) T) : ordinaryValue (q + 1) (u s) = U s := by
    change ordinaryLift.toContinuousLinearMap.adjoint (value 1 (u s)) = U s
    rw [← hU s]
    exact congrArg (fun M : EulerMeanSolenoidal.L2 →L[ℝ] EulerMeanSolenoidal.L2 => M (U s))
      ordinaryLift.adjoint_comp_self
  have hd := ordinary_hasDerivAt hq hν hT hTS u₀ f u hsol t ht
  change HasDerivAt (fun r => U (projIcc 0 T hT r)) _ t
  simpa only [extendPath, he] using hd

end NSFormalization.Source.OrdinaryForcedTime
