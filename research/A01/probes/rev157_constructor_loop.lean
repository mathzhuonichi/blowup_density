import NSFormalization.Section4.A01.SliceWiring
import NSFormalization.Section4.A01.Horizon

/-!
Reviewer probe (lane 157), **claim #4**: does the named constructor really close the loop?

This file assumes the lane's claimed remaining obligation as an ordinary **hypothesis** (`hctor`,
not an axiom — `#print axioms` below stays standard) and derives, from `HasAprioriBound` alone,
a cylinder pair on `Icc 0 S` **together with** a genuine `ClassicalSolutionR` for which **both**
a-priori rows hold.  If it typechecks, `apriori_rows_of_hslice` + the constructor really are all
that is needed on the consumer side of `HasAprioriBound`.

It also records that `hinv` (unit (iv)) is *output* by `localTheory_on_prescribed_horizon`:
`hu` below is taken from the theorem's own last conjunct, not assumed.
-/

noncomputable section

namespace Rev157Ctor

open Set MeasureTheory EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01 (jetSobolevConst)
open NSFormalization.Section4.A04 (sobolevNormAt)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR)
open NavierStokes.ProblemStatement (Space)
open scoped Topology ENNReal ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- **The exact statement the next lane must prove** (the mild ⇒ classical carrier constructor,
units B1/B2 of `research/A01/A01_SPLIT.md`), as a hypothesis. -/
def CarrierConstructor (q : ℕ) (ν S : ℝ) : Prop :=
  ∀ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)),
      (∀ t, ordinaryLift (U t) = value 1 (u t)) →
      ∃ (a' : SpatialField) (f' : SpaceTimeField) (T : ℝ) (_hST : S < T)
        (w : ClassicalSolutionR ν a' f' T),
        ∀ t : Icc (0 : ℝ) S, (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)

/-- Given `HasAprioriBound` and the carrier constructor, both a-priori rows hold for a genuine
classical solution on a strictly longer horizon, with the cylinder sup-bound `‖u‖ ≤ R`. -/
theorem rows_from_constructor {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hb : HasAprioriBound hq hν a F hF R)
    (hctor : CarrierConstructor q ν S) :
    ∃ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
      (a' : SpatialField) (f' : SpaceTimeField) (T : ℝ) (w : ClassicalSolutionR ν a' f' T),
      ‖u‖ ≤ R ∧
      (∀ t : Icc (0 : ℝ) S, sobolevNormAt (2 : ℝ) w.velocity ↑t ≤ 16 * ‖u t‖) ∧
      (∀ t : Icc (0 : ℝ) S,
        ‖u t‖ ≤ jetSobolevConst (q + 1) * sobolevNormAt ((q + 1 : ℕ) : ℝ) w.velocity ↑t) := by
  obtain ⟨u, U, hR', -, -, hU, -, -, hu⟩ :=
    localTheory_on_prescribed_horizon hq hν hS hR a ha F hF hu₀ hb
  obtain ⟨a', f', T, hST, w, hslice⟩ := hctor u U hU
  obtain ⟨hfwd, hconv⟩ := apriori_rows_of_hslice hST (by omega) w u U hu hU hslice
  exact ⟨u, a', f', T, w, hR', hfwd, hconv⟩

#print axioms rows_from_constructor

end Rev157Ctor
