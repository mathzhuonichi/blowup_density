import Euler.BaseEulerParent
import Euler.ParentPacketParity

/-! Oddness of the genuine base velocity propagates through its actual
flow to the base parent, using ODE uniqueness. -/

noncomputable section

namespace EulerBaseEulerParent.Input

open Set EulerSmoothLimit EulerSmoothBanachFlow EulerParentPacketFrames

variable (I : Input)

theorem oddData (hodd : ∀ t, Function.Odd (I.field.field t : Space → Space))
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) : OddData (I.parent ell hell hell1) := by
  have hd (t : Icc (0 : ℝ) I.T) : Function.Odd (I.displacement.field t : Space → Space) := by
    intro x
    rw [I.displacement_apply,I.displacement_apply,forward_odd I.T I.T_pos.le I.field hodd t]
    abel
  exact { displacement := hd }

end EulerBaseEulerParent.Input
