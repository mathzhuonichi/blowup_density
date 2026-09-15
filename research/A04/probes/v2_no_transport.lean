import Bindings.EnergyHighPartial
import NSFormalization.Section4.A04.HighContinuation
import Contracts.V2.EnergyHighPartial
-- NEGATIVE PROBE: bind regularizedNormDerivative WITHOUT uniqueness_toA02.
-- Expected: type mismatch, w : Data.ClassicalSolutionR vs A02.ClassicalSolutionR.
noncomputable section
namespace BlowupDensity.Bindings
open BlowupDensity.Contracts.V1.Data
def bad_v2_no_transport :
    Contracts.V2.EnergyHighPartial.EnergyHighPartialV2API :=
  { energyHighPartial with
    Cgron := NSFormalization.Section4.A04.Cgron
    Cgron_pos := NSFormalization.Section4.A04.Cgron_pos
    regularizedNormDerivative := fun ν a f T hν ha hf w hpath m hm t ht ζ hζ =>
      NSFormalization.Section4.A04.regularizedNormDerivative ν a f T hν ha hf
        w hpath m hm t ht ζ hζ
    highContinuationIntegral := fun ν a f T hν ha hf hf1 w hpath m hm t₀ t ht₀ htt htT =>
      NSFormalization.Section4.A04.highContinuationIntegral ν a f T hν ha hf hf1
        (uniqueness_toA02 w) hpath m hm t₀ t ht₀ htt htT }
end BlowupDensity.Bindings
