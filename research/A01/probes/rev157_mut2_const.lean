import NSFormalization.Section4.A01.SliceWiring

/-!
Reviewer probe (lane 157), **mutation 2**: is the constant `jetSobolevConst (q+1)` load-bearing,
or would the statement hold with `1` (i.e. is the lane's inequality accidentally the trivial one)?
Statement-level mutation (not an omitted argument): the conclusion's constant is replaced by `1`,
the proof body kept.  Expected to FAIL.
-/

noncomputable section

namespace Rev157Mut2

open Set MeasureTheory
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01
open NSFormalization.Section4.A04 (sobolevNormAt)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR)
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity EulerLpTranslation
open scoped ENNReal ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- MUTANT — `jetSobolevConst (q+1)` replaced by `1`.  Expected to FAIL. -/
theorem mutant_const_one {q : ℕ} {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} {S T : ℝ} (hST : S < T) (w : ClassicalSolutionR ν a f T)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) :
    ∀ t : Icc (0 : ℝ) S,
      ‖u t‖ ≤ (1 : ℝ) * sobolevNormAt ((q + 1 : ℕ) : ℝ) w.velocity ↑t := by
  refine sobolevSpace_norm_le_sobolevNormAt u w.velocity
    (fun t => contDiff_slice w.velocity_smooth ⟨t.2.1, lt_of_le_of_lt t.2.2 hST⟩)
    (fun t => sobolevENorm_slice_ne_top w ⟨t.2.1, lt_of_le_of_lt t.2.2 hST⟩)
    (fun t n hn wrd => ?_)
  exact hword_jet_full (u t) (fun θ => hu θ t) (U t) (hU t)
    (velocitySliceSmoothL2 w t hST) (hslice t).symm n hn wrd

/-- MUTANT (forward row) — `16` replaced by `1` in the order-2 cap.  Expected to FAIL. -/
theorem mutant_sixteen {q : ℕ} {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} {S T : ℝ} (hST : S < T) (hq : 4 ≤ q) (w : ClassicalSolutionR ν a f T)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) :
    ∀ t : Icc (0 : ℝ) S, sobolevNormAt (2 : ℝ) w.velocity ↑t ≤ 1 * ‖u t‖ :=
  sobolevNormAt_two_le_of_cylinder u U hu hU hq w.velocity hslice

end Rev157Mut2
