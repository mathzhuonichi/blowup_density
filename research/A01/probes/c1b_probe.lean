import NSFormalization.Section4.D01.OrderZeroDatum
import Euler.MeanSolenoidalSpace

open MeasureTheory
open NSFormalization.Section4.D01
open NavierStokes.ProblemStatement (Space)

-- Euler L2 is Lp Space 2 volume with Space = EuclideanSpace ℝ (Fin 3)
#check (EulerMeanSolenoidal.L2 : Type)

-- coercion + MemLp for an Euler L2 field
example (U : EulerMeanSolenoidal.L2) : MeasureTheory.MemLp (⇑U) 2 (volume : Measure Space) :=
  Lp.memLp U

-- the order-0 datum from a bare MemLp field (D01)
#check @orderZeroDatum
#check @isSobolevDatum_orderZeroDatum

-- THE ORDER-0 BRIDGE: an Euler L2 field has the D01 order-0 datum
example (U : EulerMeanSolenoidal.L2) :
    IsSobolevDatum 0 (⇑U) (orderZeroDatum (Lp.memLp U)) :=
  isSobolevDatum_orderZeroDatum (Lp.memLp U)
