import NSFormalization.Section4.C01.EnstrophyIdentity
import Bindings.EnergyAbsorptionPartialV2

open Set
open BlowupDensity.Contracts.V1 (laplacian)
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.EnergyAbsorptionPartial
  (slice laplacianSq advectionWork)

/- Exact `research/C01/Spec.lean:487-494` field shape, using the registered data copy. -/
example :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          HasDerivAt (fun s =>
              BlowupDensity.Contracts.V2.EnergyAbsorptionPartial.gradientSq
                (slice w.velocity s))
            (2 * advectionWork (slice w.velocity t) -
              2 * ν * laplacianSq (slice w.velocity t) -
              2 * BlowupDensity.Contracts.V2.EnergyAbsorptionPartial.pairing
                (slice f t) (laplacian (slice w.velocity t))) t := by
  intro ν _hν a _ha f hf T w t ht
  simp_rw [BlowupDensity.Bindings.energyAbsorptionPartialV2_gradientSq_eq]
  exact NSFormalization.Section4.C01.enstrophyIdentity_gradientSq
    (BlowupDensity.Bindings.uniqueness_toA02 w) hf ht
