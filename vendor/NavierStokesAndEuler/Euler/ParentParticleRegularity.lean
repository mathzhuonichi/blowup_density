import Euler.ParentParticleInverse
import Euler.ContinuousInverseDerivative
import Euler.GevreyInverseMap

/-! Spatial smoothness of the actual physical particle inverse follows
from its inverse identities and the genuine determinant-one Jacobian. -/

noncomputable section

namespace EulerParentPacketFrames.ParticleInverse

open Set EulerSmoothLimit EulerContinuousInverseDerivative EulerGevreyComposition
open scoped ContDiff

variable {A : Parent} (I : ParticleInverse A)

theorem hasFDerivAt (t : Icc (0 : ℝ) A.T) (x : Space) :
    HasFDerivAt (I.field t)
      (A.inverse.field t (A.ell⁻¹ • I.field t x)) x := by
  apply hasFDerivAt_inverse (A.position t) (I.field t) x
    (A.frame.field t (A.ell⁻¹ • I.field t x))
    (A.inverse.field t (A.ell⁻¹ • I.field t x))
    (I.continuous.uncurry_left t).continuousAt
  · simpa only [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul] using
      A.position_frame t (A.ell⁻¹ • I.field t x)
  · exact Filter.Eventually.of_forall (I.right_inverse t)
  · exact A.inverse_left t (A.ell⁻¹ • I.field t x)

theorem smooth (t : Icc (0 : ℝ) A.T) : ContDiff ℝ ∞ (I.field t) := by
  apply contDiff_of_fderiv_eq_comp (I.field t)
    (fun y => A.inverse.field t (A.ell⁻¹ • y))
    (fun x => (I.hasFDerivAt t x).differentiableAt)
  · exact (A.inverse.smooth t).comp (contDiff_id.const_smul A.ell⁻¹)
  · exact fun x => (I.hasFDerivAt t x).fderiv

end EulerParentPacketFrames.ParticleInverse
