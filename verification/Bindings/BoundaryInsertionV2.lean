import Bindings.PacketImport
import Bindings.BoundedDomainNorm
import Contracts.V2.BoundaryInsertion
import Bindings.BoundaryInsertion
import NSFormalization.Section3.T23.BoundaryIntegration

/-! Discharge the boundary integration premise from the domain hypotheses. -/
namespace BlowupDensity.Bindings.BoundaryInsertion

/-- Bounded-domain insertion for both boxes and smooth-level domains, with
no unproved boundary identity or unconsumed correction supplier. -/
theorem boundaryInsertionStatementV2_holds :
    Contracts.V2.BoundaryInsertion.boundaryInsertionStatementV2 := by
  intro ν hν P place Ω norms a g r δ reference hΩ hδ hr hg ha hrball hball
  exact Contract.boundaryInsertionStatement'_of_ibp_holds
    ν hν P place Ω norms a g r δ reference hΩ
    (NSFormalization.Section3.T23.ibp_boundedDomain hΩ)
    hδ hr hg ha hrball hball


open Set
open Contracts.V1 Contracts.V1.Data Contracts.V1.BoundaryInsertion

/-- Corollary 3.14 with the packet, placement and norm results supplied by
compiled proofs. Only the article's domain, geometry and reference-solution
hypotheses are arguments. The prescribed ball has radius `2 * r`. -/
theorem boundaryInsertion_from_data
    (ν : ℝ) (hν : 0 < ν) (Ω : Set Space) (hΩ : IsBoundedBoxOrSmoothDomain Ω)
    (x₀ : Space) (r : ℝ) (hr : 0 < r)
    (hball : closure (Metric.ball x₀ (2 * r)) ⊆ Ω)
    (T : ℝ) (hT : 0 < T) (δ : ℝ) (hδ : 0 < δ)
    (a : SpatialField) (g : SpaceTimeField)
    (ha : a ∈ initialClassOmega Ω) (hg : g ∈ forceClassOmega Ω)
    (reference : ClassicalSolutionOmega ν Ω a g (T + δ)) :
    let P := Bindings.packetImportFamily.select ν hν
    let place := Contract.placeFrom (P := P)
      (NSFormalization.Section3.T23.domainPlacementData
        P.carrier_compact P.force_support.1 x₀ (2 * r) (by positivity) hball
        x₀ (Metric.mem_ball_self (by positivity)) T hT)
    ∃ (C : CorrectionAPI ν P.toPacketAPI) (D : CutoffData),
      C.T = T ∧ C.δ = δ ∧ C.x₀ = x₀ ∧ C.r = r ∧
      (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
        C.v (t, x) = reference.velocity (t, x)) ∧
      D.θ = C.θ ∧ D.η = C.η ∧ D.plateau = C.plateau ∧
      D.θRadius = C.θRadius ∧ D.ε₀ = C.ε₀ ∧
      D.potential = C.potential ∧ D.correction = C.correction ∧
      Nonempty (BoundaryInsertionAPI ν P place Ω
        Bindings.BoundedDomainNorm.boundedDomainNorm a g r δ D reference) := by
  let P := Bindings.packetImportFamily.select ν hν
  let place := Contract.placeFrom (P := P)
    (NSFormalization.Section3.T23.domainPlacementData
      P.carrier_compact P.force_support.1 x₀ (2 * r) (by positivity) hball
      x₀ (Metric.mem_ball_self (by positivity)) T hT)
  have hcore : closure (Metric.ball x₀ r) ⊆ Metric.ball x₀ (2 * r) :=
    (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball (by linarith))
  exact boundaryInsertionStatementV2_holds ν hν P place Ω
    Bindings.BoundedDomainNorm.boundedDomainNorm a g r δ reference
    hΩ hδ hr hg ha hcore hball

end BlowupDensity.Bindings.BoundaryInsertion

