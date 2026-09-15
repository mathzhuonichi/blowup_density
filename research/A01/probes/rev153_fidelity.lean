import NSFormalization.Section4.A01.L2Descent

/-! Reviewer probe (lane 153) — statement fidelity of `exists_ordinaryLift_of_invariant` against the
target `DescentL2` of `research/A01/probes/probe151_descent_L2.lean:28-30`.

The restatement below is byte-for-byte the probe-151 `DescentL2`, elaborated in probe-151's *own*
`open` environment, which deliberately does **not** `open EulerLpTranslation` (the lane-153 module
does).  If `translation` / `ordinaryLift` / `LiftL2` / `EulerMeanSolenoidal.L2` resolved to different
constants in the two environments, the `exact` below would fail. -/

noncomputable section
namespace Rev153Fidelity

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerCylinderSobolev
open scoped ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Verbatim copy of probe-151 `DescentL2`. -/
def DescentL2 : Prop :=
  ∀ g : LiftL2 1, (∀ θ : AddCircle (1 : ℝ), translation 1 ((0 : Vector3), θ) g = g) →
    ∃ G : EulerMeanSolenoidal.L2, ordinaryLift G = g

/-- Lane 153 proves exactly `DescentL2`, no weakening. -/
theorem descentL2_holds : DescentL2 :=
  NSFormalization.Section4.A01.exists_ordinaryLift_of_invariant

#print axioms descentL2_holds

-- which `translation` is meant (the vendor cylinder translation, EulerProof.lean:1223)
#check @EulerLiftedGradientSpace.translation
#check @NSFormalization.Section4.A01.exists_ordinaryLift_of_invariant

end Rev153Fidelity
