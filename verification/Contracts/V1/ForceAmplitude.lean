import Contracts.V1.PeriodicInsertion

/-! Remark 3.13: positive finite packet amplitude, the reverse-triangle lower
bound, and divergence for every family of the registered insertion record.
For ENNReal amplitudes infinity is the topological limit `𝓝 ⊤`.
-/
namespace BlowupDensity.Contracts.V1
open Set Filter Topology
open Data TorusData TorusLocalTheory
open scoped ENNReal

/-- The original force is nonzero by packet energy and blowup. The correction
constant is exactly the carried order-zero force-profile constant. -/
def forceAmplitudeStatement : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI)
    (scaling : BlowupDensity.T15.Draft.ScalingAPI P place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction : BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D)
    (A : BlowupDensity.T18.Spec.PeriodicInsertionAPI ν P place scaling a g r δ D reference correction),
    P.force ≠ 0 ∧ (0 < ⨆ z, ‖P.force z‖ₑ) ∧ (⨆ z, ‖P.force z‖ₑ) < ⊤ ∧
    (∀ ε ∈ Ioc (0 : ℝ) A.ε₀,
      ENNReal.ofReal ((ε⁻¹) ^ 3 * (⨆ z, ‖P.force z‖ₑ).toReal -
        correction.forceProfileConst 0 * (ε⁻¹) ^ 2) ≤
          ⨆ z, ‖A.force ε z - g z‖ₑ) ∧
    Tendsto (fun ε : ℝ => ⨆ z, ‖A.force ε z - g z‖ₑ)
      (𝓝[>] (0 : ℝ)) (𝓝 ⊤) ∧
    Tendsto (fun ε : ℝ => (⨆ z, ‖A.force ε z - g z‖ₑ).toReal)
      (𝓝[>] (0 : ℝ)) atTop

end BlowupDensity.Contracts.V1
