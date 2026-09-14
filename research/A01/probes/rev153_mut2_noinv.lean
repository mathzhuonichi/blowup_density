import NSFormalization.Section4.A01.L2Descent

/-! Reviewer probe (lane 153), **mutation 2** — is the invariance hypothesis `hginv` load-bearing?

Two checks, neither of them the forbidden "drop the argument and re-`apply` the original theorem":

* `invariance_necessary` — the CONVERSE: membership in the image of `ordinaryLift` *forces* angular
  invariance.  So `hginv` is not a convenience of the averaging route; it exactly characterises the
  set on which the conclusion can hold.
* `drop_hginv_collapses` — consequently, the `hginv`-free statement is equivalent to
  "`translation 1 (0,θ)` is the identity on the whole of `LiftL2 1`", i.e. the cylinder `L²` space
  would not see the `AddCircle 1` factor of `liftMeasure 1 = volume.prod volume` at all.

Separately, `research/A01/REVIEW_L2_DESCENT.md` records the first error obtained by deleting `hginv`
from the theorem and re-running the module's proof body verbatim. -/

noncomputable section
namespace Rev153Mut2

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerCylinderSobolev
open scoped ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Necessity of `hginv`: every element of the image of `ordinaryLift` is angle-invariant. -/
theorem invariance_necessary (g : LiftL2 1)
    (h : ∃ G : EulerMeanSolenoidal.L2, ordinaryLift G = g) :
    ∀ θ : AddCircle (1 : ℝ), translation 1 ((0 : Vector3), θ) g = g := by
  obtain ⟨G, rfl⟩ := h
  intro θ
  rw [ordinaryLift_translation]
  congr 1
  simp

/-- Hence the `hginv`-free mutant collapses the angular translation to the identity on all of
`LiftL2 1`. -/
theorem drop_hginv_collapses
    (H : ∀ g : LiftL2 1, ∃ G : EulerMeanSolenoidal.L2, ordinaryLift G = g) :
    ∀ (g : LiftL2 1) (θ : AddCircle (1 : ℝ)), translation 1 ((0 : Vector3), θ) g = g :=
  fun g θ => invariance_necessary g (H g) θ

#print axioms invariance_necessary
#print axioms drop_hginv_collapses

end Rev153Mut2
