import NSFormalization.Section4.A01.ForceBridge

/-! Reviewer mutation probe. This deliberately flips the sign in the main on-horizon identity. -/

open Set NavierStokes.ProblemStatement
open EulerLpTranslation

namespace NSFormalization.Section4.A01

theorem mutated_forceOfPath_forcePath_eq_on_horizon_sign
    {S : ℝ} {f : A02.SpaceTimeField} (hf : D01.MemForceR f)
    (t : Icc (0 : ℝ) S) (x : Space) :
    forceOfPath (C01.forcePath (S := S) hf) (t.1, x) = -f (t.1, x) := by
  simpa only using forceOfPath_forcePath_eq_on_horizon hf t x

end NSFormalization.Section4.A01
