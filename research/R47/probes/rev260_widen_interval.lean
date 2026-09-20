import Tests.GridObservations

/-!
Reviewer mutation for lane 260: widen the theorem's velocity-observation
interval from `[0,T)` to `[0,T]`.  The registered proof must not establish
this stronger endpoint claim.
-/

noncomputable section

namespace Rev260WidenInterval

open Set
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.GridObservations
open BlowupDensity.Bindings

example (ν : ℝ) (hν : 0 < ν)
    (a : SpatialField) (ha : a ∈ initialClassR)
    (g : SpaceTimeField) (hg : MemForceR g)
    (T : ℝ) (hT : 0 < T) (δ : ℝ) (hδ : 0 < δ)
    (reference : ClassicalSolutionR ν a g (T + δ))
    (n : ℕ) (grids : Fin n → Grid) :
    ∃ F : GridFamilyAPI ν a g T δ reference n grids,
      ∀ ε ∈ Ioc (0 : ℝ) F.ε₀, ∀ i : Fin n, ∀ t ∈ Icc (0 : ℝ) T,
        gridObservation (grids i) (fun x => (F.solution ε).velocity (t, x)) =
          gridObservation (grids i) (fun x => reference.velocity (t, x)) := by
  obtain ⟨F⟩ := gridObservations_choose
    ν hν a ha g hg T hT δ hδ reference n grids
  refine ⟨F, ?_⟩
  intro ε hε i t ht
  exact F.velocity_observations ε hε i t ht

end Rev260WidenInterval
