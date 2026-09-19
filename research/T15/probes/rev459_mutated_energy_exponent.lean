import Bindings.Scaling3

noncomputable section
namespace BlowupDensity.Review459Mutation

open Set MeasureTheory
open Contracts.V1 Contracts.V1.Data Contracts.V1.TorusData
open Contracts.V1.TorusLocalTheory
open scoped ENNReal

/- Deliberate substantive mutation: change the energy scaling exponent in the
main API field from `1/2` to `3/2`.  The assembled canonical field must not
discharge this statement. -/
example {nu : ℝ} (P : PacketImportAPI nu)
    (place : Scaling3.PlacementData P.toPacketAPI) :
    ∀ epsilon ∈ Ioc (0 : ℝ) place.ε₀,
      energyEssSupT place.T
          (Scaling3.periodizedScaledVelocity P place.x₀ place.T epsilon) =
        ENNReal.ofReal (epsilon ^ ((3 : ℝ) / 2) * P.energyBound) := by
  exact (Bindings.Scaling3.scalingAPI P place).packetEnergyIdentity

end BlowupDensity.Review459Mutation
