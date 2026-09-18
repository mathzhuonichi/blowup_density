import NSFormalization.Section3.T12.HaarCube
namespace NSFormalization.Section3.T12
open MeasureTheory
open NSFormalization.Section3.T10
open NSFormalization.Section4.A02
example (v : SpatialField) : periodicLpENorm 3 v = eLpNorm (torusLift v) 3 periodicTorusMeasure :=
  periodicLpENorm_eq_eLpNorm_torusLift 3 v
example (v : SpatialField) : periodicLpENorm 6 v = eLpNorm (torusLift v) 6 periodicTorusMeasure :=
  periodicLpENorm_eq_eLpNorm_torusLift 6 v
end NSFormalization.Section3.T12
