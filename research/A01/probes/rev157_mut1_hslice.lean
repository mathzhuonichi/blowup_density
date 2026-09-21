import NSFormalization.Section4.A01.SliceWiring

/-!
Reviewer probe (lane 157), **mutation 1**: `hslice`'s orientation.

`OrderTwoCap.sobolevNormAt_two_le_of_cylinder` consumes `hslice` as written
(`(fun x => v (↑t,x)) =ᵐ ⇑(U t)`); `L2Descent.hword_jet_full` consumes the *opposite* orientation
(`⇑U =ᵐ Z.field`), which is why the module writes `(hslice t).symm` there.  This file re-runs the
module's own proof body with the `.symm` deleted.  Positive control first (the module's body,
verbatim, compiles); then the mutant.
-/

noncomputable section

namespace Rev157Mut1

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

/-- POSITIVE CONTROL — the module's proof body, verbatim, with `.symm`.  Compiles. -/
theorem control {q : ℕ} {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} {S T : ℝ} (hST : S < T) (w : ClassicalSolutionR ν a f T)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) :
    ∀ t : Icc (0 : ℝ) S,
      ‖u t‖ ≤ jetSobolevConst (q + 1) * sobolevNormAt ((q + 1 : ℕ) : ℝ) w.velocity ↑t := by
  refine sobolevSpace_norm_le_sobolevNormAt u w.velocity
    (fun t => contDiff_slice w.velocity_smooth ⟨t.2.1, lt_of_le_of_lt t.2.2 hST⟩)
    (fun t => sobolevENorm_slice_ne_top w ⟨t.2.1, lt_of_le_of_lt t.2.2 hST⟩)
    (fun t n hn wrd => ?_)
  exact hword_jet_full (u t) (fun θ => hu θ t) (U t) (hU t)
    (C01.velocityField w hST t) (hslice t).symm n hn wrd

/-- MUTANT — same body, `.symm` deleted.  Expected to FAIL. -/
theorem mutant {q : ℕ} {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} {S T : ℝ} (hST : S < T) (w : ClassicalSolutionR ν a f T)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) :
    ∀ t : Icc (0 : ℝ) S,
      ‖u t‖ ≤ jetSobolevConst (q + 1) * sobolevNormAt ((q + 1 : ℕ) : ℝ) w.velocity ↑t := by
  refine sobolevSpace_norm_le_sobolevNormAt u w.velocity
    (fun t => contDiff_slice w.velocity_smooth ⟨t.2.1, lt_of_le_of_lt t.2.2 hST⟩)
    (fun t => sobolevENorm_slice_ne_top w ⟨t.2.1, lt_of_le_of_lt t.2.2 hST⟩)
    (fun t n hn wrd => ?_)
  exact hword_jet_full (u t) (fun θ => hu θ t) (U t) (hU t)
    (C01.velocityField w hST t) (hslice t) n hn wrd

end Rev157Mut1
