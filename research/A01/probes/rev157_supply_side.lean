import NSFormalization.Section4.A01.Horizon

/-!
Reviewer probe (lane 157), the **supply side** of `HasAprioriBound` (review note N3).

`rev157_constructor_loop.lean` shows the *consumer* side closes: for the pair that
`localTheory_on_prescribed_horizon` **outputs**, angle invariance `hu` is free and
`apriori_rows_of_hslice` + the carrier constructor give both rows.

This file records the other side.  `HasAprioriBound` unfolds (`Iff.rfl`) to a `∀` over a cylinder
path `u` that is constrained **only** by the forced Duhamel equation: no angle invariance, no
ordinary carrier `U`, no `ClassicalSolutionR`, and the index is `Icc 0 T'` for an arbitrary
`T' ≤ S`, **not** `Icc 0 S`.  So a lane that wants to *prove* `HasAprioriBound` from the a-priori
rows must still produce `hu`, `U` (with the descent) and `hslice` for that `u` — the original
unit-(iv) obligation of `research/A01/REVIEW_L2_DESCENT.md` §3 row 4, which is about this `u`.
-/

noncomputable section

namespace Rev157Supply

open Set MeasureTheory EulerLpTranslation EulerMeanOrdinaryLift EulerCylinderSobolevSpace
open NSFormalization.Section4.A01
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerMeanSmoothRepresentative
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The predicate, unfolded.  Note what is *absent* from the antecedent. -/
theorem hasAprioriBound_unfold {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field EulerSmoothLimit.Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field EulerSmoothLimit.Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (R : ℝ) :
    HasAprioriBound hq hν a F hF R ↔
      ∀ (T' : ℝ) (hT : 0 ≤ T') (hTS : T' ≤ S)
        (u : C(Icc (0 : ℝ) T', SobolevSpace 1 (q + 1))),
        (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
          (coefficients 1 hq (sobolevPath F hF q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) → ‖u‖ ≤ R :=
  Iff.rfl

#print axioms hasAprioriBound_unfold

end Rev157Supply
