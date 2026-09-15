import Bindings.EnergyAbsorptionPartialV3
import NSFormalization.Section4.C01.EnstrophyBounds

/-! Exact original-vocabulary consumers of the enstrophy identity and bound.
The Frobenius gradient is transported by the existing non-definitional V2
bridge. No contract or registered API is changed by this probe. -/

noncomputable section

open Set MeasureTheory
open BlowupDensity.Contracts.V1 (laplacian)
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.EnergyAbsorptionPartial
  (slice l2Sq laplacianSq criticalL3 advectionWork)
open BlowupDensity.Contracts.V2.EnergyAbsorptionPartial (gradientSq pairing)
open BlowupDensity.Bindings
open scoped ENNReal

namespace C01Enstrophy162

theorem gradient_bridge : gradientSq = NSFormalization.Section4.C01.gradientSq := by
  funext z
  exact energyAbsorptionPartialV2_gradientSq_eq z

/-- `Spec.lean`'s entire `enstrophyIdentity` field, with its original quantifiers. -/
theorem identity :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          HasDerivAt (fun s => gradientSq (slice w.velocity s))
            (2 * advectionWork (slice w.velocity t) -
              2 * ν * laplacianSq (slice w.velocity t) -
              2 * pairing (slice f t) (laplacian (slice w.velocity t))) t := by
  intro ν _ a _ f hf T w t ht
  rw [gradient_bridge]
  exact NSFormalization.Section4.C01.enstrophyIdentity (uniqueness_toA02 w) hf ht

/-- `Spec.lean`'s entire differential-bound field, with the already registered
`C₁` and explicit universal `CRH1 = 2`. -/
theorem differentialBound :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          ENNReal.ofReal energyAbsorptionPartialV3.C₁ * criticalL3 (slice w.velocity t) ≤
              ENNReal.ofReal (ν / 4) →
            ∀ E' : ℝ, HasDerivAt (fun s => gradientSq (slice w.velocity s)) E' t →
              E' + ν * laplacianSq (slice w.velocity t) ≤
                2 * ν⁻¹ * l2Sq (slice f t) := by
  intro ν hν a _ f hf T w t ht hsmall E' hd
  rw [gradient_bridge] at hd
  exact NSFormalization.Section4.C01.enstrophyDifferentialBound hν
    (uniqueness_toA02 w) hf ht hsmall hd

/-- `Spec.lean`'s complete integrated field, with the original half-open
smallness interval and the same constant `CRH1 = 2`. -/
theorem integralBound :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ico (0 : ℝ) T,
          (∀ s ∈ Ico (0 : ℝ) t,
            ENNReal.ofReal energyAbsorptionPartialV3.C₁ * criticalL3 (slice w.velocity s) ≤
              ENNReal.ofReal (ν / 4)) →
            IntervalIntegrable (fun s => laplacianSq (slice w.velocity s)) volume 0 t ∧
              gradientSq (slice w.velocity t) +
                  ν * ∫ s in (0 : ℝ)..t, laplacianSq (slice w.velocity s) ≤
                gradientSq a + 2 * ν⁻¹ * ∫ s in (0 : ℝ)..t, l2Sq (slice f s) := by
  intro ν hν a _ f hf T w t ht hsmall
  rw [gradient_bridge]
  exact NSFormalization.Section4.C01.enstrophyIntegralBound hν
    (uniqueness_toA02 w) hf ht hsmall

end C01Enstrophy162

#print axioms C01Enstrophy162.identity
#print axioms C01Enstrophy162.differentialBound
#print axioms C01Enstrophy162.integralBound
#print axioms NSFormalization.Section4.C01.pressure_laplacian_pairing_zero
#print axioms NSFormalization.Section4.C01.enstrophyDerivative
#print axioms NSFormalization.Section4.C01.laplacianSq_continuousOn
#print axioms NSFormalization.Section4.C01.gradientSq_continuousOn
#print axioms NSFormalization.Section4.C01.intervalIntegrable_laplacianSq
