import NSFormalization.Section4.A05.SmoothJets

/-!
# T12 shared coordinate-derivative helper

Lanes 400 (`GradientLSix.lean`) and 405 (`GradientLambdaL3.lean`) were written in
parallel inside the single namespace `NSFormalization.Section3.T12` and each
declared its own `contDiff_dirDeriv` with the same one-line proof, so the two
modules could not be imported together (`environment already contains
'NSFormalization.Section3.T12.contDiff_dirDeriv'`).  The lane-400 statement is
the general one (arbitrary normed target `F`; lane 405's copy is its
`F := Space` instance, because `SpatialField` is the reducible abbreviation
`Space → Space`), so it is kept verbatim here and both modules import it.

No statement changes: `contDiff_dirDeriv` below is character-for-character the
declaration that used to sit at `GradientLSix.lean:184-186`.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A05 (dirDeriv)
open scoped ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_dirDeriv {w : Space → F} (hw : ContDiff ℝ ∞ w) (i : Fin 3) :
    ContDiff ℝ ∞ (dirDeriv i w) :=
  (hw.fderiv_right (by simp)).clm_apply contDiff_const

end NSFormalization.Section3.T12
