import Bindings.Localization

noncomputable section

namespace Rev379ConstantMutation

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm
open BlowupDensity.Contracts.V1.TorusData
open scoped ContDiff ENNReal BigOperators Topology

/- A substantive mutation: doubling the explicit Gagliardo constant in the
   whole-space identity must not be accepted by the registered proof. -/
example :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
      ContDiff ℝ ∞ f → HasCompactSupport f →
        IReal s f = (2 : ℝ≥0∞) * cFrac s * dotHomogeneousENorm s f ^ (2 : ℕ) := by
  intro s hs0 hs1 f hf hcompact
  exact (BlowupDensity.Bindings.localizationAPI.wholeSpace_identity
    s hs0 hs1 f hf hcompact).2

end Rev379ConstantMutation
