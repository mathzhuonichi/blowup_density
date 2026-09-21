import Contracts.V2.EnergyAbsorptionPartial
import Bindings.EnergyAbsorptionPartialV2
import NSFormalization.Section4.C01.EnergyBounds

/-! REVIEW PROBE (lane 154): dry run of the planned V3 binding.  The two prospective V3
fields are stated in the **contract's** vocabulary, token-for-token from
`research/C01/Spec.lean:364-370` and `:383-387`, and discharged from the lane's theorems.
Confirms (a) `forcePrimitive`/`energyBudget` bind by `rfl`, (b) `l2Bound` needs **no** bridge,
(c) `energyDifferentialBound` needs **exactly** V2's `gradientSq` bridge and nothing else. -/

noncomputable section

open Set MeasureTheory
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.EnergyAbsorptionPartial (slice l2Sq l2Norm)
open BlowupDensity.Contracts.V2.EnergyAbsorptionPartial (gradientSq)

namespace BlowupDensity.Bindings

/-- Contract-side restatement of `research/C01/Spec.lean:218-219`. -/
def forcePrimitiveC (f : SpaceTimeField) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, l2Norm (slice f s)

/-- Contract-side restatement of `research/C01/Spec.lean:224-225`. -/
def energyBudgetC (a : SpatialField) (f : SpaceTimeField) (t : ℝ) : ℝ :=
  l2Norm a + forcePrimitiveC f t

theorem v3_forcePrimitive_eq :
    forcePrimitiveC = NSFormalization.Section4.C01.forcePrimitive := rfl

theorem v3_energyBudget_eq :
    energyBudgetC = NSFormalization.Section4.C01.energyBudget := rfl

/-- Prospective V3 field `energyDifferentialBound`. -/
example :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          ∀ E' : ℝ, HasDerivAt (fun s => l2Sq (slice w.velocity s)) E' t →
            E' + 2 * ν * gradientSq (slice w.velocity t) ≤
              2 * l2Norm (slice f t) * l2Norm (slice w.velocity t) :=
  fun _ _ _ _ _ hf _ w _ ht E' hderiv => by
    rw [energyAbsorptionPartialV2_gradientSq_eq]
    exact NSFormalization.Section4.C01.energyDifferentialBound (uniqueness_toA02 w) hf ht E' hderiv

/-- Prospective V3 field `l2Bound` (= eq:RL2): no bridge at all. -/
example :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ico (0 : ℝ) T,
          l2Norm (slice w.velocity t) ≤ energyBudgetC a f t :=
  fun _ hν _ _ _ hf _ w _ ht =>
    NSFormalization.Section4.C01.l2Bound (uniqueness_toA02 w) hf hν ht

end BlowupDensity.Bindings
