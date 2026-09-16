import Bindings.InsertionFromData
noncomputable section
namespace BlowupDensity.Bindings
open Set Filter Contracts.V1 Contracts.V1.Data
open scoped ENNReal Topology
theorem rev233_shift_lifespan {ν T : ℝ} {a : SpatialField} {P : PacketAPI ν}
    (L : Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P)
    (ha : L.family.a = a) (hT : L.family.T = T)
    (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) L.family.ε₀) :
    maximalLifespanR ν a (L.family.force ε) = ENNReal.ofReal (T + 1) := by
  simpa only [ha, hT] using L.lifespan ε hε


end BlowupDensity.Bindings
