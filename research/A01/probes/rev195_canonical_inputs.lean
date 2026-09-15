import NSFormalization.Section4.A01.InteriorMomentum
import NSFormalization.Section4.A01.ForcePathSmooth

/-!
Positive assembly-interface probe for lane 192's canonical inputs. The main
theorem deliberately keeps `fc` and `u₀` general, while lane 192 instantiates
them with the canonical physical force path and the canonical cylinder datum.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set NavierStokes.ProblemStatement
open NSFormalization.Paper3 NSFormalization.Section4.D01
open NSFormalization.Source.ForcedCylinderLocal
open EulerLpTranslation EulerLpTranslation.SmoothL2Field
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace
  EulerSmoothFieldSobolevTime

variable {q m : ℕ} (hq : 6 ≤ q) (hm : m + 2 ≤ q + 1) (hm2 : 2 ≤ (m : ℝ))
variable {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
variable {f : A02.SpaceTimeField} (hf : D01.MemForceR f)
variable (a : SmoothL2Field Space)
variable (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)

-- These partial applications check the exact first two data arguments consumed
-- by both assembly exports. `ha` is the solenoidal input retained by lane 192's
-- constructor when it produces the displayed canonical `u₀`.
#check interior_momentum_identity hq hm hm2 hν hS
  (ordinarySobolev (q + 1) a.toLp a.translation_contDiff)
  (sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) q)

#check interior_momentum_identity_of_complement_paths hq hm hm2 hν hS
  (ordinarySobolev (q + 1) a.toLp a.translation_contDiff)
  (sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) q)

example : ∀ x, EulerSmoothLimit.divergence a.field x = 0 := ha

end NSFormalization.Section4.A01
