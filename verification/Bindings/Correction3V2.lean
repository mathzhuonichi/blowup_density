import Contracts.V2.Correction3
import Bindings.Correction3
import Bindings.TorusLocalTheory
import NSFormalization.Section3.T17.ArticleScope

/-! Fieldwise transport of placement, cutoff, classical solution and all
45 correction fields through the existing checked V1 conversions. -/
namespace BlowupDensity.Bindings.Correction3

theorem correctionStatementV2_holds :
    Contracts.V2.Correction3.correctionStatementV2 := by
  intro ν u p f K place a g r δ reference hν hr hr2 hδ ha hg hsupp hball
  obtain ⟨⟨D, hD, ⟨A⟩⟩, heq⟩ :=
    NSFormalization.Section3.T17.correctionStatementArticle_holds
      ν u p f K (placementOfContract place) a g r δ
      (TorusLocalTheory.ofContract reference) hν hr hr2 hδ ha hg hsupp hball
  exact ⟨⟨CutoffData.toContract D, api_toContract hD, ⟨toContract A⟩⟩, heq⟩

open Set MeasureTheory Metric
open Contracts.V1 Contracts.V1.Data Contracts.V1.TorusData Contracts.V1.TorusLocalTheory

/-- The registered building block supplies the raw support clause; no support
hypothesis is needed from a consumer of the packet-indexed article theorem. -/
theorem correctionArticle_of_packet (ν : ℝ) (P : PacketAPI ν)
    (place : Contracts.V1.Correction3.PlacementData P.velocity P.pressure P.force P.carrier)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (hν : 0 < ν) (hr : 0 < r) (hr2 : r < 1 / 2) (hδ : 0 < δ)
    (ha : a ∈ initialClassT) (hg : g ∈ forceClassT)
    (hball : ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius) :
    let v : SpaceTimeField := fun z =>
      if z.1 ∈ Ico (0 : ℝ) (place.T + δ) then reference.velocity z else 0
    (∃ D : CutoffData, LocalPotentialAPI v P.velocity place.Kstar place.x₀ r place.T δ D ∧
      Nonempty (Contracts.V1.Correction3.CorrectionAPI ν place v r δ D)) ∧
    ∀ t ∈ Ico (0 : ℝ) (place.T + δ), ∀ x, v (t, x) = reference.velocity (t, x) := by
  exact correctionStatementV2_holds ν P.velocity P.pressure P.force P.carrier
    place a g r δ reference hν hr hr2 hδ ha hg
    (fun t ht => P.velocity_support t ⟨ht.1.le, ht.2⟩) hball

end BlowupDensity.Bindings.Correction3
