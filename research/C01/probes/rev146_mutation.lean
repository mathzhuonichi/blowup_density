import NSFormalization.Section4.C01.JetPaths

/-!
Reviewer negative check for lane 146-C01-jet-paths (read-only probe; NOT part of the build).

Two substantive mutations of the lane's statements, each retried with the lane's own
proof script and then with normalisation tactics:

M1  `residualPath_field` with the **advection sign flipped** (`f + adv + νΔu`).
M2  `viscousPath_field` with `ν •` **replaced by the identity** (`Δu` instead of `νΔu`).

Both must fail; if either elaborated, the corresponding sign/scaling in the module would be
unpinned.
-/

noncomputable section

open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerSmoothLimit
open NSFormalization.Source.OrdinaryViscousStability
open NavierStokes.ProblemStatement (advection spatialLaplacian)

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {S T : ℝ}

-- M1: advection sign flipped.
theorem residualPath_field_MUT_sign (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    (hST : S < T) (t : Icc (0 : ℝ) S) (x : Space) :
    (residualPath w hf hST t).field x
      = f (t.1, x) + advection w.velocity t.1 x + ν • spatialLaplacian w.velocity t.1 x := by
  rw [residualPath, addField_field, fieldSub_field, forcePath_field,
    advectionPath_field, viscousPath_field]

-- M2: `ν •` replaced by the identity.
theorem viscousPath_field_MUT_nu (w : ClassicalSolutionR ν a f T) (hST : S < T)
    (t : Icc (0 : ℝ) S) (x : Space) :
    (viscousPath w hST t).field x = spatialLaplacian w.velocity t.1 x := by
  rw [viscousPath, mapField_field, smul_apply, ContinuousLinearMap.id_apply,
    laplacianPath_field]

end NSFormalization.Section4.C01
