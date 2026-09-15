import Bindings.EnergyAbsorptionPartialV2

/-!
Lane 152 review — negative check on the **contract statement**.

Two substantive mutations of `Contracts.V2.EnergyAbsorptionPartial.energyIdentity`
(`Spec.lean:344-350`), each stated as a bare `example` with the *binding's own proof
script* (`Bindings/EnergyAbsorptionPartialV2.lean:energyAbsorptionPartialV2`).  Both must
fail: if either went through, the contract's constants would not be load bearing.

A. the viscous coefficient `-2 * ν` weakened to `-ν`;
B. the forcing factor `2 * pairing …` dropped to `pairing …`.
-/

noncomputable section
open Set MeasureTheory
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.EnergyAbsorptionPartial (slice l2Sq)
open BlowupDensity.Contracts.V2.EnergyAbsorptionPartial (gradientSq pairing)
open BlowupDensity.Bindings

-- MUTATION A: -2 * ν  ↦  -ν
example :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          HasDerivAt (fun s => l2Sq (slice w.velocity s))
            (-ν * gradientSq (slice w.velocity t) +
              2 * pairing (slice w.velocity t) (slice f t)) t :=
  fun _ _ _ _ _ hf _ w _ ht => by
    rw [energyAbsorptionPartialV2_gradientSq_eq]
    exact NSFormalization.Section4.C01.energyIdentity_l2Sq (uniqueness_toA02 w) hf ht

-- MUTATION B: 2 * pairing  ↦  pairing
example :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          HasDerivAt (fun s => l2Sq (slice w.velocity s))
            (-2 * ν * gradientSq (slice w.velocity t) +
              pairing (slice w.velocity t) (slice f t)) t :=
  fun _ _ _ _ _ hf _ w _ ht => by
    rw [energyAbsorptionPartialV2_gradientSq_eq]
    exact NSFormalization.Section4.C01.energyIdentity_l2Sq (uniqueness_toA02 w) hf ht
