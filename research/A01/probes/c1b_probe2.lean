import NSFormalization.Section4.D01.OrderZeroDatum
import Euler.MeanSolenoidalSpace
import Euler.LpSmoothField

open MeasureTheory
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement (Space)

-- ae-congruence of IsSobolevDatum in the physical field (all orders, bookkeeping)
example {s : ℝ} {z z' : Space → Space} {A : RealVectorSobolev s}
    (h : IsSobolevDatum s z A) (hzz' : z =ᵐ[volume] z') : IsSobolevDatum s z' A := by
  intro i ψ
  rw [h i ψ]
  refine integral_congr_ae ?_
  filter_upwards [hzz'] with x hx
  rw [hx]

-- c5 at order 0: transport U 0 = a.toLp to a datum for the physical initial field a.field
example (a : EulerLpTranslation.SmoothL2Field Space) (U : EulerMeanSolenoidal.L2)
    (hU : U = a.toLp) : IsSobolevDatum 0 a.field (orderZeroDatum (Lp.memLp U)) := by
  have h0 := isSobolevDatum_orderZeroDatum (Lp.memLp U)
  have hae : (⇑U : Space → Space) =ᵐ[volume] a.field := by
    rw [hU]; exact a.toLp_ae
  intro i ψ
  rw [h0 i ψ]
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]
