import NSFormalization.Section4.I03.HomogeneousScaling
import Bindings.Packet

open NSFormalization.Section4.I03
open scoped ENNReal

-- Import separately: the existing Packet and Scaling bindings share a name.
example : componentTimeNorm 2 (-1) (BlowupDensity.Bindings.packet 1 (by norm_num)).force ≠ ⊤ := by
  let P := BlowupDensity.Bindings.packet 1 (by norm_num)
  exact componentTimeNorm_finite 2 (by norm_num) (by norm_num) P.force_smooth P.force_support.1
