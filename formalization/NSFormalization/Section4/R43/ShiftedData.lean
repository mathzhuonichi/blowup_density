import NSFormalization.Section4.A05.RieszShift
import NSFormalization.Section4.C01.VelocityJets

/-!
# The shifted critical data carried by a classical velocity slice

This module keeps the R43-facing wrapper separate from the A05 construction.
It supplies precisely the `shifted` field of `CriticalAdvectionLpBridge`; the
independent fractional Parseval field `pairing_identity` remains open.
-/

noncomputable section

open Set NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev

namespace NSFormalization.Section4.R43

open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField ClassicalSolutionR MemForceR)

/-- Every interior velocity slice in a critical datum path has the shifted
physical `Λ` field and the three half-order derivative data required by R43.

This is a `def`, rather than a `theorem`, because its codomain is the structure
`ShiftedCriticalData` in `Type`. -/
def criticalAdvectionLpBridge_shifted
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      ShiftedCriticalData (fun x => w.velocity (t, x))
        (hcrit.velocityThreeHalf t) := by
  intro t ht
  exact NSFormalization.Section4.A05.shiftedCriticalData_of_memHInfty
    (fun x => w.velocity (t, x))
    (NSFormalization.Section4.C01.velocity_slice_memHInfty w
      (Ioo_subset_Ico_self ht))
    (hcrit.velocityThreeHalf t)
    (hcrit.velocityThreeHalf_isDatum t (Ioo_subset_Ico_self ht))

end NSFormalization.Section4.R43
