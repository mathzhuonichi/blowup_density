import NSFormalization.Section3.T17.LatticeDeriv

/-! Lane 369 (r1) negative check — the general bridge's strict separation
hypothesis `hlt : ρ < r` is load-bearing.  Feeding the weakened `ρ ≤ r` is a
type mismatch (`lake env lean` on this file exits 1 with the error below), so the
no-copy/zero case genuinely needs the closed support ball strictly inside the
open copy ball. -/

namespace NSFormalization.Section3.T17.Rev369r1Negative
open Set Metric NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open NavierStokes.ProblemStatement

example {w : SpaceTimeField} {x₀ : Space} {ρ r : ℝ}
    (hs : ∀ (t : ℝ) (y : Space), w (t, y) ≠ 0 → y ∈ ball x₀ ρ)
    (hr : r + ρ ≤ 1) (hle : ρ ≤ r)
    (z : SpaceTime) (n : ℕ) (u : Fin n → SpaceTime) :
    ∃ k : NSFormalization.Section3.T10.PeriodicFrequency,
      ‖iteratedFDeriv ℝ n (latticeLift w) z u‖ =
        ‖iteratedFDeriv ℝ n w (z - (0, latticeVector k)) u‖ :=
  latticeLift_iteratedFDeriv_eq hs hr hle z n u

end NSFormalization.Section3.T17.Rev369r1Negative
