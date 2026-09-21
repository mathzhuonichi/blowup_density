import NSFormalization.Source.PhysicalRemoval
import NSFormalization.Source.LocalizedInsertion
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# I02, unit 7 and the open form of `eq:bgzero`

Three facts that the manuscript states but that no declaration in the tree
records: the `O(ε³)` volume of the spatial support and the `O(ε²)` length of the
temporal support of a field supported in `Ioo a b ×ˢ ball x₀ R`
(`paper/sections/03-torus.tex:225`), the openness of the scaled plateau
`x₀ + ε · O`, and the vacuity of the rescaled packet slice before its activation
time, which is what makes the open-neighbourhood form of `eq:bgzero`
(`03-torus.tex:190-193`) true on the whole presingular interval and not only on
`[t_ε, T)`.
-/

noncomputable section

namespace NSFormalization.Section4.I02

open NavierStokes NavierStokes.ProblemStatement Set Filter MeasureTheory
open NSFormalization.Source NSFormalization.Source.PacketScaling
open scoped ContDiff Topology ENNReal

/-- The spatial projection of a spacetime support contained in a time interval
times a ball is contained in that ball. -/
theorem snd_tsupport_subset {w : VelocityField} {a b R : ℝ} {x₀ : Space}
    (hs : tsupport w ⊆ Ioo a b ×ˢ Metric.ball x₀ R) :
    Prod.snd '' tsupport w ⊆ Metric.ball x₀ R := by
  rintro x ⟨z, hz, rfl⟩
  exact (hs hz).2

/-- The temporal projection is contained in the time interval. -/
theorem fst_tsupport_subset {w : VelocityField} {a b R : ℝ} {x₀ : Space}
    (hs : tsupport w ⊆ Ioo a b ×ˢ Metric.ball x₀ R) :
    Prod.fst '' tsupport w ⊆ Ioo a b := by
  rintro t ⟨z, hz, rfl⟩
  exact (hs hz).1

/-- "Its spatial support has volume `O(ε³)`", `paper/sections/03-torus.tex:225`,
with the constant made explicit as `R³` times the volume of the unit ball. -/
theorem spatial_support_volume {w : VelocityField} {a b R : ℝ} {x₀ : Space}
    (hs : tsupport w ⊆ Ioo a b ×ˢ Metric.ball x₀ R) (hR : 0 ≤ R) :
    volume (Prod.snd '' tsupport w) ≤
      ENNReal.ofReal (R ^ 3) * volume (Metric.ball (0 : Space) 1) := by
  refine (measure_mono (snd_tsupport_subset hs)).trans ?_
  rw [Measure.addHaar_ball volume x₀ hR]
  simp [finrank_euclideanSpace, Fintype.card_fin]

/-- "Its temporal support has length `O(ε²)`",
`paper/sections/03-torus.tex:225`. -/
theorem temporal_support_length {w : VelocityField} {a b R : ℝ} {x₀ : Space}
    (hs : tsupport w ⊆ Ioo a b ×ˢ Metric.ball x₀ R) :
    volume (Prod.fst '' tsupport w) ≤ ENNReal.ofReal (b - a) := by
  refine (measure_mono (fst_tsupport_subset hs)).trans ?_
  simp [Real.volume_Ioo]

/-- The physical scaling `y ↦ x₀ + ε • y` is an open map, so the transported
plateau of `eq:bgzero` really is an open neighbourhood. -/
theorem isOpen_spaceMap_image {ε : ℝ} (hε : ε ≠ 0) (x₀ : Space) {O : Set Space}
    (hO : IsOpen O) : IsOpen (PhysicalRemoval.spaceMap ε x₀ '' O) := by
  have h1 : IsOpenMap (fun y : Space => ε • y) := (Homeomorph.smulOfNeZero ε hε).isOpenMap
  have h2 : IsOpenMap (fun y : Space => x₀ + y) := (Homeomorph.addLeft x₀).isOpenMap
  exact (h2.comp h1) O hO

/-- Before its activation time the rescaled packet slice is identically zero,
so its topological support is empty.  This is the vacuity step that carries
`eq:bgzero` over the whole presingular interval. -/
theorem scaledPacket_slice_empty (u : VelocityField) {k t₀ t : ℝ}
    (x₀ : Space) (ht : t ≤ t₀) :
    tsupport (fun y : Space => parabolicVelocity k t₀ x₀ (zeroPastField u) (t, y)) = ∅ := by
  have hz : (fun y : Space => parabolicVelocity k t₀ x₀ (zeroPastField u) (t, y)) =
      fun _ => 0 := by
    funext y
    exact zeroPast_dilate_early u k (k ^ 2) k t₀ (sq_nonneg k) x₀ ht y
  rw [hz]
  simp [tsupport]

/-- The packet scaling `scaledSupport` at inverse length `ε⁻¹` is the physical
scaling `spaceMap ε`. -/
theorem scaledSupport_eq_spaceMap (ε : ℝ) (x₀ : Space) (K : Set Space) :
    scaledSupport ε⁻¹ x₀ K = PhysicalRemoval.spaceMap ε x₀ '' K := by
  unfold scaledSupport PhysicalRemoval.spaceMap
  simp only [inv_inv]

/-- The parabolic time scale at inverse length `ε⁻¹` is `ε²`. -/
theorem inv_sq_inv (ε : ℝ) : ((ε⁻¹ : ℝ) ^ 2)⁻¹ = ε ^ 2 := by
  rw [inv_pow, inv_inv]

end NSFormalization.Section4.I02
