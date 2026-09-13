import NSFormalization.Source.RieszPotentialNearField
import Mathlib.MeasureTheory.Covering.Vitali

/-! # Weak estimate for bounded-radius ball witnesses

This is the covering-to-integral component only. It defines no maximal
operator and assumes no weak or strong maximal inequality.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NSFormalization.MaximalBallWeak
abbrev Space := NSFormalization.RieszPotentialNearField.Space

/-- Fourfold dilation multiplies three-dimensional ball volume by 64. -/
theorem volume_ball_four (x : Space) (r : ℝ) :
    volume (Metric.ball x (4 * r)) = 64 * volume (Metric.ball x r) := by
  rw [EuclideanSpace.volume_ball_fin_three, EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), mul_pow]
  norm_num
  ring

/-- A bounded family of positive ball witnesses gives a weak estimate with
constant 64. Neither the witness set nor the density must be measurable,
and total mass may be infinite. -/
theorem boundedRadius_weak (H : Space → ℝ≥0∞) (s : Set Space) (r : Space → ℝ)
    (R ℓ : ℝ) (_hℓ : 0 < ℓ)
    (hr : ∀ x ∈ s, 0 < r x ∧ r x ≤ R)
    (hmass : ∀ x ∈ s,
      ENNReal.ofReal ℓ * volume (Metric.ball x (r x)) ≤
        ∫⁻ y in Metric.ball x (r x), H y) :
    ENNReal.ofReal ℓ * volume s ≤ 64 * ∫⁻ y, H y := by
  obtain ⟨u, hus, hud, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball s id r R
      (fun x hx => (hr x hx).2) 4 (by norm_num)
  simp only [id_eq] at hud hcover
  have huc : u.Countable := hud.countable_of_isOpen (fun _ _ => Metric.isOpen_ball)
    (fun x hx => ⟨x, Metric.mem_ball_self (hr x (hus hx)).1⟩)
  have hs : s ⊆ ⋃ x ∈ u, Metric.ball x (4 * r x) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, hxy (Metric.mem_ball_self (hr x hx).1)⟩⟩
  calc
    _ ≤ ENNReal.ofReal ℓ * volume (⋃ x ∈ u, Metric.ball x (4 * r x)) := by gcongr
    _ ≤ ENNReal.ofReal ℓ * ∑' x : u, volume (Metric.ball (x : Space) (4 * r x)) := by
      gcongr
      exact measure_biUnion_le volume huc _
    _ = 64 * ∑' x : u, ENNReal.ofReal ℓ * volume (Metric.ball (x : Space) (r x)) := by
      simp_rw [volume_ball_four, ENNReal.tsum_mul_left]
      ring
    _ ≤ 64 * ∑' x : u, ∫⁻ y in Metric.ball (x : Space) (r x), H y := by
      gcongr with x
      exact hmass x (hus x.property)
    _ = 64 * ∫⁻ y in ⋃ x ∈ u, Metric.ball x (r x), H y := by
      rw [lintegral_biUnion huc (fun _ _ => measurableSet_ball) hud]
    _ ≤ 64 * ∫⁻ y, H y := by
      gcongr
      exact Measure.restrict_le_self

end NSFormalization.MaximalBallWeak
