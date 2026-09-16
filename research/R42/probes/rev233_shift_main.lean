import Bindings.InsertionFromData
noncomputable section
namespace BlowupDensity.Bindings
open Set Filter Contracts.V1 Contracts.V1.Data
open scoped ENNReal Topology
theorem rev233_shift_main :
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T →
      ∀ (a : SpatialField), a ∈ initialClassR →
        ∀ (g : SpaceTimeField), MemForceR g →
          ENNReal.ofReal T < maximalLifespanR ν a g →
            ∃ (P : PacketAPI ν)
              (L : Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P),
              L.family.a = a ∧ L.family.g = g ∧ L.family.T = T + 1 := by
  intro ν hν T hT a _ha g hg hLife
  have hreg := (maximalPartial.regularThrough_iff ν a g T hT).mpr hLife
  obtain ⟨δ, hδ, ⟨R⟩, _, hlong⟩ := maximalPartial.referenceLifespan ν a g T hT hreg
  have hsub : Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Space) ⊆
      Ico (0 : ℝ) (T + δ) ×ˢ (univ : Set Space) :=
    prod_mono Ioo_subset_Ico_self Subset.rfl
  let P := insertionFromData_packet ν hν
  let C : CorrectionAPI ν P := correction P (T := T) (δ := δ) (r := 1)
    (v := R.velocity) (π := R.pressure) (g := g) 0 hT hδ zero_lt_one
    (R.velocity_smooth.mono hsub) (R.pressure_smooth.mono hsub)
    (fun t ht => R.divergence t ⟨ht.1.le, ht.2⟩) R.momentum
  let S := scaling C thresholds
  let F := insertionFamily S R rfl rfl
  have hregLong : RegularThrough ν F.a F.g (F.T + F.margin) :=
    (maximalPartial.regularThrough_iff ν a g (T + δ) (add_pos hT hδ)).mpr hlong
  exact ⟨P, InsertionLifespan.insertionLifespanV2API F hg hregLong, rfl, rfl, rfl⟩


end BlowupDensity.Bindings
