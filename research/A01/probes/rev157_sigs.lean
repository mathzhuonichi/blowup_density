-- Reviewer probe (lane 157): printed signatures, to read which constants the module's `open`s
-- actually resolved to (LESSONS 2026-09-14/111: read `#check`, not the `open` list; /152: a
-- selective `open` can resolve a bare type name to a vendor homonym).
import NSFormalization.Section4.A01.SliceWiring

set_option pp.fullNames true

#check @NSFormalization.Section4.A01.velocitySliceSmoothL2_field
#check @NSFormalization.Section4.A01.sobolevENorm_slice_ne_top_order
#check @NSFormalization.Section4.A01.sobolevENorm_slice_ne_top
#check @NSFormalization.Section4.A01.sobolevSpace_norm_le_sobolevNormAt_of_solution
#check @NSFormalization.Section4.A01.isSobolevDatum_ordinary_of_hslice
#check @NSFormalization.Section4.A01.apriori_rows_of_hslice
