import NSFormalization.Section4.D01.OrderZeroDatum
import NSFormalization.Section4.D01.DerivativeDatum
import Euler.MeanOrbitSobolev
import Euler.MeanOrdinaryLift
import NSFormalization.Source.OrdinaryCylinderDescent
import NSFormalization.Source.FourierConvention

open MeasureTheory
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement (Space)

-- D01 smooth-field all-order datum (SmoothDatum.lean:279 / :291)
#check @smoothAngularDatum_isSobolevDatum
#check @exists_isSobolevDatum_of_contDiff_memLp
-- D01 derivative-datum multiplier (DerivativeDatum.lean:246)
#check @isSobolevDatum_partialDeriv
-- D01 order-0 seed + uniqueness
#check @orderZeroDatum
#check @isSobolevDatum_unique
#check @memLp_of_isSobolevDatum
-- Euler coordinates
#check @EulerMeanSmoothRepresentative.ordinarySobolev
#check @EulerMeanSmoothRepresentative.ordinarySobolev_value
#check @EulerMeanSmoothRepresentative.ordinarySobolev_coordinate
#check @EulerMeanOrdinaryLift.ordinaryLift
#check @NSFormalization.Source.OrdinaryCylinderDescent.ordinaryValue
#check @NSFormalization.Source.OrdinaryCylinderDescent.ordinaryValue_lift
-- Fourier convention constants
#check @NSFormalization.Source.angularFourier
#check @NSFormalization.Source.frequencyUnit
#check @NSFormalization.Source.angularSobolevSq_eq_frequency_weight
