import NSFormalization.Section3.T23.LocalCorrection
import NSFormalization.Section3.T23.SpatialExtension
import NSFormalization.Paper1.CorrectionForceProfile

/-! A single fixed solenoidal extension transfers the entire small-scale
physical correction and its force. The threshold is chosen after the cutoffs. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set Filter Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1.CorrectionProfile (physicalCorrection temporalCutoff spatialCutoff)
open NSFormalization.Source.PhysicalRemoval (physical_support temporal_cutoff_support timeMap)
open scoped ContDiff Topology

/-- Construct a fixed global solenoidal reference and one positive scale
threshold on which both actual correction and force agree globally. -/
theorem exists_matching_global_correction (ν : ℝ) {v : VelocityField}
    {x₀ : Space} {r T δ R : ℝ} {θ : Space → ℝ} {η : ℝ → ℝ}
    (hr : 0 < r) (hT : 0 < T) (hδ : 0 < δ) (hR : 0 < R)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ ball x₀ r,
      spatialDivergence v t x = 0)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθs : tsupport θ ⊆ ball (0 : Space) R) (hηs : tsupport η ⊆ Ioo (-2 : ℝ) 2) :
    ∃ (V : VelocityField) (ε₀ : ℝ), ContDiff ℝ ∞ V ∧
      (∀ t x, spatialDivergence V t x = 0) ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ ε ∈ Ioc (0 : ℝ) ε₀,
        physicalCorrection v x₀ T θ η ε = physicalCorrection V x₀ T θ η ε ∧
        NSFormalization.Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε) =
          NSFormalization.Source.correctionForce ν V (physicalCorrection V x₀ T θ η ε) := by
  obtain ⟨V, hV, hVdiv, heq⟩ := exists_solenoidal_window_extension hr hT hδ hv hdiv
  obtain ⟨e, he, ht, hs⟩ := NSFormalization.Section3.T16.exists_threshold hR
    (half_pos hr) (half_pos hT) (half_pos hδ)
  refine ⟨V, min e 1, hV, hVdiv, lt_min he zero_lt_one, min_le_right _ _, ?_⟩
  intro ε hε
  have hεe : ε ∈ Ioc (0 : ℝ) e := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have htime : 2 * ε ^ 2 < min T δ / 2 := by
    rcases le_total T δ with h | h
    · rw [min_eq_left h]
      exact (ht ε hεe).trans_le (min_le_left _ _)
    · rw [min_eq_right h]
      exact (ht ε hεe).trans_le (min_le_right _ _)
  let I := Ioo (T - min T δ / 2) (T + min T δ / 2)
  have hI : IsOpen I := isOpen_Ioo
  have heq' : EqOn v V (I ×ˢ ball x₀ (r / 2)) := by
    intro z hz
    exact (heq ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩).symm
  have hts : tsupport (temporalCutoff η T ε) ⊆ I := by
    intro t ht'
    obtain ⟨s, hs', he'⟩ := temporal_cutoff_support hε.1.ne' T hηc ht'
    have hsi := hηs hs'
    change T + ε ^ 2 * s = t at he'
    change T - min T δ / 2 < t ∧ t < T + min T δ / 2
    constructor
    · nlinarith [mul_lt_mul_of_pos_left hsi.1 (sq_pos_of_pos hε.1)]
    · nlinarith [mul_lt_mul_of_pos_left hsi.2 (sq_pos_of_pos hε.1)]
  have hss : tsupport (spatialCutoff θ x₀ ε) ⊆ ball x₀ (r / 2) :=
    NSFormalization.Section3.T16.spatialCutoff_tsupport_ball hε.1 hθc hθs (hs ε hεe)
  have hw := physicalCorrection_eq_of_cylinder v V x₀ T ε (r / 2) θ η heq' hts hss
  refine ⟨hw, ?_⟩
  let D := localCorrectionData v x₀ T θ η ∅ R (min e 1)
  have hws : tsupport (D.correction ε) ⊆ I ×ˢ ball x₀ (r / 2) := by
    intro z hz
    have hz' := physical_support hε.1 v x₀ T hθc hηc hθs hηs hz
    refine ⟨⟨?_, ?_⟩, ball_subset_ball (hs ε hεe).le hz'.2⟩
    · change T - min T δ / 2 < z.1
      linarith [hz'.1.1]
    · change z.1 < T + min T δ / 2
      linarith [hz'.1.2]
  have hf := correctionForce_eq_of_open_agreement ν v V D ε (hI.prod isOpen_ball) hws heq'
  rw [correctionForce_eq_source, correctionForce_eq_source] at hf
  change NSFormalization.Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε) =
    NSFormalization.Source.correctionForce ν V (physicalCorrection v x₀ T θ η ε) at hf
  exact hf.trans (congrArg (NSFormalization.Source.correctionForce ν V) hw)

/-- The literal I02 mixed correction-jet and spatial force-jet bounds,
with one threshold chosen before either derivative order. -/
theorem exists_local_derivative_bounds (ν : ℝ) {v : VelocityField}
    {x₀ : Space} {r T δ R : ℝ} {θ : Space → ℝ} {η : ℝ → ℝ}
    (hr : 0 < r) (hT : 0 < T) (hδ : 0 < δ) (hR : 0 < R)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ ball x₀ r,
      spatialDivergence v t x = 0)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθs : tsupport θ ⊆ ball (0 : Space) R) (hηs : tsupport η ⊆ Ioo (-2 : ℝ) 2) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      (∀ j m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ z : SpaceTime,
        ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ (j + m) (physicalCorrection v x₀ T θ η ε) z
          (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space)))
            (fun i => ((0 : ℝ), u i)))‖ ≤ C * (ε⁻¹) ^ (2 * j + m)) ∧
      (∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ z : SpaceTime,
        ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ m
          (NSFormalization.Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) z
          (fun i => ((0 : ℝ), u i))‖ ≤ C * (ε⁻¹) ^ (2 + m)) := by
  obtain ⟨V, ε₀, hV, _, he, he1, heq⟩ :=
    exists_matching_global_correction ν hr hT hδ hR hv hdiv hθc hηc hθs hηs
  refine ⟨ε₀, he, he1, ?_, ?_⟩
  · intro j m
    obtain ⟨C, hC, hb⟩ := NSFormalization.Paper1.CorrectionProfile.physical_mixed_derivative_bound
      hV x₀ T hθ hη hθc hηc j m
    refine ⟨C, hC, ?_⟩
    intro ε hε z u hu
    rw [(heq ε hε).1]
    exact hb ε ⟨hε.1, hε.2.trans he1⟩ z u hu
  · intro m
    obtain ⟨C, hC, hb⟩ :=
      NSFormalization.Paper1.CorrectionForceProfile.physicalForce_spatial_derivative_bound
        ν hV x₀ T hθ hη hθc hηc m
    refine ⟨C, hC, ?_⟩
    intro ε hε z u hu
    rw [(heq ε hε).2]
    exact hb ε ⟨hε.1, hε.2.trans he1⟩ z u hu

end NSFormalization.Section3.T23
