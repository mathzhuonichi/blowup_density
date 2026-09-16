import NSFormalization.Section4.R43.Universal
namespace NSFormalization.Section4.R43
open A02
open D01 (dotHomogeneousENorm)
open D01.Homogeneous (forceHomogeneousENorm)
theorem rev225_widened :
    ∀ ν : ℝ, 0 < ν →
      ∀ a : SpatialField, a ∈ initialClassR →
        ∀ f : SpaceTimeField, MemForceR f →
          dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f
              < ENNReal.ofReal (2 * criticalConst * ν) →
            maximalLifespanR ν a f = ⊤ := by
  intro ν hν a ha f hf hsmall
  obtain ⟨u, p, hu⟩ := exists_maximal' ν a f hν ha hf
  exact A04.lifespanInfiniteOfLocallyFinite_of_memForceR' ν a f hν ha hf u p hu
    (fun _ hS hSL => maximal_squaredHTwoIntegral_general hν ha hf hu hsmall hS hSL)

end NSFormalization.Section4.R43
