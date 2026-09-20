import NSFormalization.Section4.R43.Endpoint
noncomputable section
namespace NSFormalization.Section4.R43
open A02
open D01 (forceSobolevENormL1)
open scoped ENNReal
-- Mutation: double the allowed force radius, retaining the original proof.
theorem widened_smallness :
    ∀ ν : ℝ, 0 < ν → ∀ f : SpaceTimeField, MemForceR f →
      forceSobolevENormL1 (1 / 2) f < ENNReal.ofReal ((2 * criticalConst) * ν) →
        maximalLifespanR ν (fun _ => 0) f = ⊤ := by
  intro ν hν f hf hsmall
  exact homogeneousAtZero_of_memForceR ν hν f hf
    ((forceHomogeneousENorm_le_forceSobolevENormL1 f hf).trans_lt hsmall)

end NSFormalization.Section4.R43
