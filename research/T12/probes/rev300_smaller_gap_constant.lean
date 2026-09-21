import NSFormalization.Section3.T12.SpectralGap

/-!
# Reviewer mutation probe for lane 300

This intentionally shrinks the spectral-gap factor by replacing `4π²` with
`8π²`.  At positive order the mutation is false already on a first nonzero
Fourier mode, so the lane theorem must not discharge it.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open NSFormalization.Section3.T10
open NSFormalization.Section4.A02 (SpatialField)
open scoped ENNReal

def rev300SmallerGapConst (s : ℝ) : ℝ :=
  (1 + 1 / (8 * Real.pi ^ 2)) ^ (s / 2)

example :
    ∀ s : ℝ, 0 ≤ s → ∀ v : SpatialField,
      MemPeriodicHomogeneous s v →
        periodicSobolevENorm s v ≤
          ENNReal.ofReal (rev300SmallerGapConst s) * periodicHomogeneousENorm s v :=
  spectralGap

end NSFormalization.Section3.T12
