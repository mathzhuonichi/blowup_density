import NSFormalization.Section4.R44.EnergyIdentity

/-!
Reviewer mutation probe: the main identity's dissipative coefficient is changed
from `-2 * ν` to `+2 * ν`.  Reusing the proved theorem must fail.
-/
noncomputable section

open Set NavierStokes.ProblemStatement
open NSFormalization.Section4
open NSFormalization.Section4.R44

example {ν T : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (hν : 0 < ν) (hf : A02.MemForceR f) (w : A02.ClassicalSolutionR ν a f T)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => Y (fun x => w.velocity (r, x)) ^ 2)
      (2 * ν * Z (fun x => w.velocity (t, x)) ^ 2 -
        2 * energyAdvectionJPairing (jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩)
          (energyDatum (-1 / 2) (fun x => advection w.velocity t x)) +
        2 * forceJPairing (jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩)) t := by
  exact energy_identity hν hf w ht
