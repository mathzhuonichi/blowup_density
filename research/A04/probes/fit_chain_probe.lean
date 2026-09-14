/-
# Consumer-fit probe (`fit_Rhigh`, `fit_chain`) — reconstructed by the lane-121 reviewer

Preserved verbatim from `research/A04/REVIEW_HPR.md` appendix A (`/tmp/rev121/fit.lean`).
`fit_Rhigh` fills `inner_energy_Rhigh`'s `hpr` slot with `pressure_drop`; `fit_chain` is the
real consumer shape — `momentum_datum` supplies `hmom` and `pressure_drop` supplies `hpr` at the
SAME `P`, from the SAME `hP`, with an `A02.MemForceR f` handed to both.  Both `#print axioms` →
`[propext, Classical.choice, Quot.sound]`.
-/

import NSFormalization.Section4.A04.PressureDrop

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A04
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR)
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped RealInnerProductSpace ContDiff

namespace Rev121Fit

-- Instance check: the real inner product the assembly uses on the carrier.
#synth InnerProductSpace ℝ (RealVectorSobolev (3 : ℝ))
#synth NormedAddCommGroup (RealVectorSobolev (3 : ℝ))

/-- Reviewer-written fit against `inner_energy_Rhigh` (NOT the module's example). -/
theorem fit_Rhigh
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {m : ℕ} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {G Gt N P L Fd : RealVectorSobolev (m : ℝ)}
    {grad C u2 uNorm fNorm d : ℝ}
    (hν : 0 ≤ ν) (hd : d = 2 * ⟪G, Gt⟫) (hmom : Gt = ν • L - N - P + Fd)
    (hlap : ⟪G, L⟫ ≤ -grad ^ 2) (hnl : -⟪G, N⟫ ≤ C * u2 * uNorm * grad)
    (hGn : ‖G‖ = uNorm) (hFn : ‖Fd‖ = fNorm)
    (hGd : IsSobolevDatum (m : ℝ) (fun x : Space => u.velocity (t, x)) G)
    (hPd : IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x) P) :
    (1 / 2) * d + ν * grad ^ 2 ≤ C * u2 * uNorm * grad + fNorm * uNorm :=
  inner_energy_Rhigh hν hd hmom hlap (pressure_drop u hf ht hGd hPd) hnl hGn hFn

/-- The full chain: `momentum_datum` supplies `hmom`, `pressure_drop` supplies `hpr`,
    at the SAME `P` and the SAME `hP`.  This is the real consumer shape. -/
theorem fit_chain
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) (hf : NSFormalization.Section4.A02.MemForceR f)
    {m : ℕ} (hm : 2 ≤ m)
    {Gfun : ℝ → RealVectorSobolev (m : ℝ)}
    (hGd : ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum (m : ℝ) (fun x => u.velocity (t, x)) (Gfun t))
    (hGc : ContDiffOn ℝ ∞ Gfun (Ico (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {L N P Fd : RealVectorSobolev (m : ℝ)}
    (hL : IsSobolevDatum (m : ℝ) (fun x => spatialLaplacian u.velocity t x) L)
    (hN : IsSobolevDatum (m : ℝ) (fun x => advection u.velocity t x) N)
    (hP : IsSobolevDatum (m : ℝ) (fun x => pressureGradient u.pressure t x) P)
    (hF : IsSobolevDatum (m : ℝ) (fun x => f (t, x)) Fd)
    {grad C u2 uNorm fNorm d : ℝ}
    (hν : 0 ≤ ν) (hd : d = 2 * ⟪Gfun t, deriv Gfun t⟫)
    (hlap : ⟪Gfun t, L⟫ ≤ -grad ^ 2) (hnl : -⟪Gfun t, N⟫ ≤ C * u2 * uNorm * grad)
    (hGn : ‖Gfun t‖ = uNorm) (hFn : ‖Fd‖ = fNorm) :
    (1 / 2) * d + ν * grad ^ 2 ≤ C * u2 * uNorm * grad + fNorm * uNorm :=
  inner_energy_Rhigh hν hd (momentum_datum u hf hm hGd hGc ht hL hN hP hF) hlap
    (pressure_drop u hf ht (hGd t ⟨le_of_lt ht.1, ht.2⟩) hP) hnl hGn hFn

#print axioms fit_Rhigh
#print axioms fit_chain

end Rev121Fit
