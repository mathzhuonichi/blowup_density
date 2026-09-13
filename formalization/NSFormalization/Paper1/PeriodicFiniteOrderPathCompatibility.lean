import NSFormalization.Paper1.PeriodicFiniteOrderPath

/-! # Explicit compatibility layer for finite-order ordinary paths

This file records the only safe bridge currently available: a candidate ordinary
path is identified with the path carried by a `CylinderMildWitness` by an
explicit equality hypothesis. No smooth field, pressure, or classical Flow is
reconstructed here.
-/

noncomputable section
namespace NSFormalization.Paper1.PeriodicFiniteOrderPathCompatibility

open Set MeasureTheory
open NSFormalization.Paper1.PeriodicFiniteOrderMild
open NSFormalization.Paper1.PeriodicFiniteOrderPath
open EulerMeanSolenoidal EulerMeanOrdinaryLift EulerCylinderSobolevSpace
open scoped Topology

variable {q : ℕ} {hq : 6 ≤ q} {ν S : ℝ}
variable {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
variable {A : NSFormalization.Paper1.PeriodicOrdinaryLocal.OrdinaryRepresentative a}
variable {F : Icc (0 : ℝ) S → EulerLpTranslation.SmoothL2Field EulerSmoothLimit.Space}
variable {hF : ∀ n, Continuous (fun t => (F t).jetLp n)}

/-- A candidate ordinary path is compatible only when equality with the witness
path is supplied explicitly. -/
structure CompatiblePath (W : CylinderMildWitness hq ν S a A F hF) where
  candidate : C(Icc (0 : ℝ) W.T, EulerMeanSolenoidal.L2)
  agrees : candidate = ordinaryPath W

@[simp] theorem candidate_eq (W : CylinderMildWitness hq ν S a A F hF)
    (C : CompatiblePath W) : C.candidate = ordinaryPath W := C.agrees

theorem candidate_continuous (W : CylinderMildWitness hq ν S a A F hF)
    (C : CompatiblePath W) : Continuous C.candidate := by
  rw [C.agrees]
  exact ordinaryPath_continuous W

theorem candidate_initial (W : CylinderMildWitness hq ν S a A F hF)
    (C : CompatiblePath W) :
    C.candidate ⟨0, le_rfl, W.hT.le⟩ = A.field.toLp := by
  rw [C.agrees]
  exact ordinaryPath_initial W

theorem candidate_lift_value (W : CylinderMildWitness hq ν S a A F hF)
    (C : CompatiblePath W) (t : Icc (0 : ℝ) W.T) :
    EulerMeanOrdinaryLift.ordinaryLift (C.candidate t) =
      EulerCylinderSobolevSpace.value 1 (W.u t) := by
  rw [C.agrees]
  exact ordinaryLift_value W t

end NSFormalization.Paper1.PeriodicFiniteOrderPathCompatibility
