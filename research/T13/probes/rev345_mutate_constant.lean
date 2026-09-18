import NSFormalization.Section3.T13.TorusIdentity

noncomputable section

namespace NSFormalization.Section3.T13.ReviewMutation

open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal

/- The coefficient is deliberately changed from `cFrac s` to `cFrac s + 1`.
   This probe is expected to fail: the published theorem cannot prove the
   substantively mutated identity. -/
example (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (f : SpatialField)
    (hfs : ContDiff ℝ ∞ f) (hfp : IsPeriodicSpatial f) :
    ITorus s f < ⊤ ∧
      ITorus s f = (cFrac s + 1) * periodicHomogeneousENorm s (meanZeroPartT f) ^ (2 : ℕ) := by
  exact torus_identity hs0 hs1 hfs hfp

end NSFormalization.Section3.T13.ReviewMutation
