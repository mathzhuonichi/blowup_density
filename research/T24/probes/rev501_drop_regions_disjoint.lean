import Bindings.MultipleRegionsV2

/-!
Reviewer mutation: remove `regions_disjoint` from the bounded-domain existence
statement while keeping its conclusion unchanged.  The attempted proof below
must fail because the concrete assembly requires pairwise disjoint balls.
-/
noncomputable section
namespace Rev501DropRegionsDisjoint

open Set
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.BoundaryInsertion

example :
    ∀ (ν : ℝ), 0 < ν → ∀ (P : PacketImportAPI ν),
      ∀ (Ω : Set Space) (hΩ : IsBoundedBoxOrSmoothDomain Ω),
      ∀ (T : ℝ), 0 < T → ∀ (N : ℕ), 0 < N →
        ∀ (regionCenter : Fin N → Space) (regionRadius : Fin N → ℝ),
          (∀ j : Fin N, 0 < regionRadius j) →
          (∀ j : Fin N,
            closure (Metric.ball (regionCenter j) (regionRadius j)) ⊆ Ω) →
          Nonempty
            (BlowupDensity.Contracts.V2.MultipleRegions.MultipleRegionsOmegaAPI
              P T Ω hΩ regionCenter regionRadius) := by
  intro _ν _hν P Ω hΩ T hT N hN regionCenter regionRadius hr hQ
  exact ⟨BlowupDensity.Bindings.MultipleRegionsV2.multipleRegionsOmega
    P Ω hΩ T hT N hN regionCenter regionRadius hr hQ⟩

end Rev501DropRegionsDisjoint
