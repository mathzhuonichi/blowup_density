import NSFormalization.Section3.T23.Boundary
import NSFormalization.Section3.T15.Placement

/-!
# T23 U4: localized differences and boundary retention

The U3 insertion formulas are accepted only as explicit hypotheses.  This
module proves the eight U4 fields from those formulas and the already proved
placement, local-correction, packet-support, and domain-geometry facts.
-/

noncomputable section

namespace NSFormalization.Section3.T23

open Set Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T15
open NSFormalization.Section3.T22 (zeroExtension)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open scoped Topology

end NSFormalization.Section3.T23
