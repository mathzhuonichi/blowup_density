import NSFormalization.Section3.T21.Definitions
import NSFormalization.Section3.T20.CriticalRegularity

/-!
# T21 N0: the canonical T20 bridge

On the canonical side the lifespan vocabulary is shared with T20, so the
field is a direct specialization of `CriticalRegularityTAPI.globalRegularity`.
The non-definitional registered lifespan bridge is exercised in the T21
conformance probe.
-/

noncomputable section

namespace NSFormalization.Section3.T21

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T10
open scoped ENNReal

/-- N0: T20 critical global regularity in the exact canonical T21 field
shape. -/
theorem criticalGlobalRegularity
    (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν →
      ∀ g : SpaceTimeField, g ∈ forceClassT →
        forceSobolevENormT 1 (1 / 2) g < ENNReal.ofReal (K.c * ν) →
          maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤ :=
  K.globalRegularity

end NSFormalization.Section3.T21
