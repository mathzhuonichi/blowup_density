import Contracts.V1.Correction3

/-! Lemma 3.5 over the registered vocabulary, with a classical reference.
The zero extension is explicit, and its identification on the slab is part
of the conclusion. All 45 version-one API fields are retained. -/
namespace BlowupDensity.Contracts.V2.Correction3
open Set MeasureTheory Metric
open BlowupDensity.Contracts.V1 BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V1.Correction3

def correctionStatementV2 : Prop :=
  ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (place : PlacementData u p f K)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (reference : ClassicalSolutionT ν a g (place.T + δ)),
    0 < ν → 0 < r → r < 1 / 2 → 0 < δ →
    a ∈ initialClassT → g ∈ forceClassT →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t, x)) ⊆ K) →
    ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius →
    (∃ D : CutoffData,
      LocalPotentialAPI (fun z => if z.1 ∈ Ico (0 : ℝ) (place.T + δ) then reference.velocity z else 0) u place.Kstar place.x₀ r place.T δ D ∧
      Nonempty (CorrectionAPI ν place (fun z => if z.1 ∈ Ico (0 : ℝ) (place.T + δ) then reference.velocity z else 0) r δ D)) ∧
    ∀ t ∈ Ico (0 : ℝ) (place.T + δ), ∀ x,
      (fun z => if z.1 ∈ Ico (0 : ℝ) (place.T + δ) then reference.velocity z else 0) (t, x) = reference.velocity (t, x)

end BlowupDensity.Contracts.V2.Correction3
