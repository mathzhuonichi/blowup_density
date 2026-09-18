import NSFormalization.Section3.T11.Transport

/-! Reviewer negative probe: the main residual statement is load-bearing.

The target below changes the transported force correction from `- d t` to `+ d t`.
`fail_if_success` records that the existing theorem cannot solve this mutated
statement; the contradictory hypothesis is used only to make this audit probe
itself typecheck.  The same target without that hypothesis is compiled
separately by the reviewer to capture Lean's concrete failure.
-/

noncomputable section

namespace NSFormalization.Section3.T11.TransportReviewProbe

open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T11.Transport
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField SpaceTimeScalar)

example {v u : SpaceTimeField} {q p : SpaceTimeScalar}
    {ν α t : ℝ} {X c d : ℝ → Space} {x : Space}
    (_hvline : ∀ s : ℝ, v (s, x) = α • u (α * s, x + X s) - c s)
    (_hv : ∀ y : Space, v (t, y) = α • u (α * t, y + X t) - c t)
    (_hq : ∀ y : Space, q (t, y) = α ^ 2 * p (α * t, y + X t))
    (_hX : HasDerivAt X (c t) t) (_hc : HasDerivAt c (d t) t)
    (_hu : DifferentiableAt ℝ u (α * t, x + X t))
    (_hu2 : ContDiff ℝ 2 (fun y : Space ↦ u (α * t, y)))
    (_hp : DifferentiableAt ℝ (fun y : Space ↦ p (α * t, y)) (x + X t))
    (hfalse : False) :
    NavierStokesR3.ProblemStatement.navierStokesResidual (α * ν) v q t x =
      α ^ 2 •
          NavierStokesR3.ProblemStatement.navierStokesResidual ν u p (α * t) (x + X t) +
        d t := by
  fail_if_success
    exact navierStokesResidual_transport _hvline _hv _hq _hX _hc _hu _hu2 _hp
  exact hfalse.elim

end NSFormalization.Section3.T11.TransportReviewProbe
