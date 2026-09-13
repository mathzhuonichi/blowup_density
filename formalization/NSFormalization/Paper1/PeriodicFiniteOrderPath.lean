import NSFormalization.Paper1.PeriodicFiniteOrderMild
import NSFormalization.Source.OrdinaryCylinderDescent

/-! # Ordinary path extracted from a finite-order cylinder witness

This module only transports the already proved continuous `L²` component of
`CylinderMildWitness`.  It does not identify a periodic field with an
ordinary `L²` field; that identification is recorded by the witness' lift
equality and therefore remains an explicit hypothesis.
-/

noncomputable section
namespace NSFormalization.Paper1.PeriodicFiniteOrderPath

open Set MeasureTheory
open NSFormalization.Paper1.PeriodicFiniteOrderMild
open EulerMeanSolenoidal EulerMeanOrdinaryLift EulerCylinderSobolevSpace
open scoped Topology

variable {q : ℕ} {hq : 6 ≤ q} {ν S : ℝ}
variable {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
variable {A : NSFormalization.Paper1.PeriodicOrdinaryLocal.OrdinaryRepresentative a}
variable {F : Icc (0 : ℝ) S → EulerLpTranslation.SmoothL2Field EulerSmoothLimit.Space}
variable {hF : ∀ n, Continuous (fun t => (F t).jetLp n)}

/-- The ordinary `L²` path carried by a finite-order mild witness. -/
def ordinaryPath (W : CylinderMildWitness hq ν S a A F hF) :
    C(Icc (0 : ℝ) W.T, EulerMeanSolenoidal.L2) := W.U

theorem ordinaryPath_continuous (W : CylinderMildWitness hq ν S a A F hF) :
    Continuous (ordinaryPath W) := by
  exact (ordinaryPath W).continuous

theorem ordinaryPath_initial (W : CylinderMildWitness hq ν S a A F hF) :
    ordinaryPath W ⟨0, le_rfl, W.hT.le⟩ = A.field.toLp := by
  exact W.initial_L2

theorem ordinaryLift_value (W : CylinderMildWitness hq ν S a A F hF)
    (t : Icc (0 : ℝ) W.T) :
    EulerMeanOrdinaryLift.ordinaryLift (ordinaryPath W t) =
      EulerCylinderSobolevSpace.value 1 (W.u t) := by
  exact W.realization t

/-! The following lemmas are deliberately transport lemmas: they expose the
finite-order information carried by the witness without claiming any
classical Navier--Stokes regularity. -/

theorem ordinaryPath_initial_lift (W : CylinderMildWitness hq ν S a A F hF) :
    EulerMeanOrdinaryLift.ordinaryLift
        (ordinaryPath W ⟨0, le_rfl, W.hT.le⟩) =
      EulerCylinderSobolevSpace.value 1
        (W.u ⟨0, le_rfl, W.hT.le⟩) := by
  exact W.realization ⟨0, le_rfl, W.hT.le⟩

theorem ordinaryPath_divergence_free (W : CylinderMildWitness hq ν S a A F hF)
    (t : Icc (0 : ℝ) W.T) :
    EulerCylinderSobolevSpace.value 1 (W.u t) ∈
      EulerLiftedGradientSpace.divergenceFreeSpace 1 1 0 := by
  exact W.divergence t

theorem ordinaryPath_mild (W : CylinderMildWitness hq ν S a A F hF)
    (t : Icc (0 : ℝ) W.T) :
    W.u t = EulerQuadraticSource.quadraticDuhamel 1 ν W.viscosity_pos W.hT.le W.hTS
      (NSFormalization.Source.ForcedCylinderLocal.coefficients 1 hq
        (EulerSmoothFieldSobolevTime.sobolevPath F hF q))
      (EulerMeanSmoothRepresentative.ordinarySobolev (q + 1)
        A.field.toLp A.field.translation_contDiff) W.u t := by
  exact W.mild t

end NSFormalization.Paper1.PeriodicFiniteOrderPath
