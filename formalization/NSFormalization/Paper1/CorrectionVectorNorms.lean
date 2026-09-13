import NSFormalization.Paper1.CorrectionPositiveNorms
import NSFormalization.Source.VectorForceNorms
import NSFormalization.Source.LocalizedInsertion
import NSFormalization.Source.CompactForceConvergence

/-! Actual three-component force norms for the constructed correction. -/
noncomputable section
namespace NSFormalization.Paper1.CorrectionForceNorms
open NavierStokes NavierStokes.ProblemStatement Set MeasureTheory
open CorrectionProfile CorrectionForceProfile
open Filter Topology
open scoped ContDiff ENNReal

theorem physicalCorrection_smooth {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (physicalCorrection v x₀ T θ η ε) := by
  apply localCorrection_smooth hv x₀
  · exact hθ.comp ((contDiff_id.sub contDiff_const).const_smul ε⁻¹)
  · exact hη.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))

theorem physicalForce_smooth (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) :=
  Source.LocalizedInsertion.correctionForce_smooth ν hv (physicalCorrection_smooth hv x₀ T ε hθ hη)

theorem physicalCorrection_compact (v : VelocityField) (x₀ : Space) (T ε : ℝ) (hε : ε ≠ 0)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    HasCompactSupport (physicalCorrection v x₀ T θ η ε) := by
  apply localCorrection_compact
  · exact hθc.comp_homeomorph ((Homeomorph.subRight x₀).trans
      (Homeomorph.smulOfNeZero ε⁻¹ (inv_ne_zero hε)))
  · exact hηc.comp_homeomorph ((Homeomorph.subRight T).trans
      (Homeomorph.smulOfNeZero (ε ^ 2)⁻¹ (inv_ne_zero (pow_ne_zero 2 hε))))

theorem physicalForce_compact (ν : ℝ) (v : VelocityField) (x₀ : Space) (T ε : ℝ) (hε : ε ≠ 0)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    HasCompactSupport (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) :=
  Source.LocalizedInsertion.correctionForce_compact ν v (physicalCorrection_compact v x₀ T ε hε hθc hηc)

theorem scalarPhysicalForce_eLpNorm_mono (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε : ℝ) (hε : ε ≠ 0) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3)
    {s r : ℝ} (hsr : s ≤ r) (q : ℝ≥0∞) :
    eLpNorm (fun t => Source.fourierSobolevNorm s
      (fun x => scalarPhysicalForce ν v x₀ T θ η i ε (t, x))) q volume ≤
    eLpNorm (fun t => Source.fourierSobolevNorm r
      (fun x => scalarPhysicalForce ν v x₀ T θ η i ε (t, x))) q volume := by
  apply eLpNorm_mono_real
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ Source.fourierSobolevNorm s _ from Real.sqrt_nonneg _)]
  exact Source.fourierSobolevNorm_mono_of_compact hsr
    ((Source.coordinateForce_smooth (physicalForce_smooth ν hv x₀ T ε hθ hη) i).comp
      (contDiff_const.prodMk contDiff_id))
    (Paper3.compact_spatial_slice
      (Source.coordinateForce_compact (physicalForce_compact ν v x₀ T ε hε hθc hηc) i) t)

theorem vectorPhysicalForce_uniform_positive_time (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {s : ℝ} (hs : s ≤ 1) (hs0 : 0 ≤ s) (q : ℝ≥0∞) (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C < (⊤ : ℝ≥0∞) ∧ ∀ ε ∈ Ioc (0 : ℝ) 1,
      eLpNorm (Source.vectorFourierSobolevNorm s
        (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε))) q volume ≤
      ENNReal.ofReal (ε ^ (2 / q.toReal - 1 / 2 - s)) * C := by
  have hi (i : Fin 3) := scalarPhysicalForce_uniform_positive_time ν hv x₀ T hθ hη hθc hηc i hs hs0 q
  choose C hC hb using hi
  refine ⟨∑ i, C i, ENNReal.sum_lt_top.mpr (fun i _ => hC i), ?_⟩
  intro ε hε
  calc
    _ ≤ ∑ i : Fin 3, eLpNorm (fun t => Source.fourierSobolevNorm s
        (fun x => scalarPhysicalForce ν v x₀ T θ η i ε (t, x))) q volume :=
      Source.eLpNorm_vector_le_sum s _ q hq (fun i =>
        (Paper3.stronglyMeasurable_fourierSobolev_time s
          (Source.coordinateForce_smooth (physicalForce_smooth ν hv x₀ T ε hθ hη) i).continuous).aestronglyMeasurable)
    _ ≤ ∑ i : Fin 3, ENNReal.ofReal (ε ^ (2 / q.toReal - 1 / 2 - s)) * C i :=
      Finset.sum_le_sum (fun i _ => hb i ε hε)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem vectorPhysicalForce_uniform_negative_time (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0) (q : ℝ≥0∞) (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C < (⊤ : ℝ≥0∞) ∧ ∀ ε ∈ Ioc (0 : ℝ) 1,
      eLpNorm (Source.vectorFourierSobolevNorm s
        (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε))) q volume ≤
      ENNReal.ofReal (ε ^ (2 / q.toReal - 1 / 2 - s)) * C := by
  have hi (i : Fin 3) := scalarPhysicalForce_uniform_negative_time ν hv x₀ T hθ hη hθc hηc i hs hs0 q
  choose C hC hb using hi
  refine ⟨∑ i, C i, ENNReal.sum_lt_top.mpr (fun i _ => hC i), ?_⟩
  intro ε hε
  calc
    _ ≤ ∑ i : Fin 3, eLpNorm (fun t => Source.fourierSobolevNorm s
        (fun x => scalarPhysicalForce ν v x₀ T θ η i ε (t, x))) q volume :=
      Source.eLpNorm_vector_le_sum s _ q hq (fun i =>
        (Paper3.stronglyMeasurable_fourierSobolev_time s
          (Source.coordinateForce_smooth (physicalForce_smooth ν hv x₀ T ε hθ hη) i).continuous).aestronglyMeasurable)
    _ ≤ ∑ i : Fin 3, ENNReal.ofReal (ε ^ (2 / q.toReal - 1 / 2 - s)) * C i :=
      Finset.sum_le_sum (fun i _ => hb i ε hε)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem vectorPhysicalForce_positive_tendsto_zero (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {s : ℝ} (hs : s ≤ 1) (hs0 : 0 ≤ s) (q : ℝ≥0∞) (hq : 1 ≤ q)
    (hβ : 0 < 2 / q.toReal - 1 / 2 - s) :
    Filter.Tendsto (fun ε => eLpNorm (Source.vectorFourierSobolevNorm s
      (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε))) q volume)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  Source.vector_family_tendsto_zero_of_components s q hq
    (fun ε => physicalForce_smooth ν hv x₀ T ε hθ hη)
    (fun i => scalarPhysicalForce_positive_tendsto_zero ν hv x₀ T hθ hη hθc hηc i hs hs0 q hβ)

theorem vectorPhysicalForce_negative_tendsto_zero (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0) (q : ℝ≥0∞) (hq : 1 ≤ q)
    (hβ : 0 < 2 / q.toReal - 1 / 2 - s) :
    Filter.Tendsto (fun ε => eLpNorm (Source.vectorFourierSobolevNorm s
      (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε))) q volume)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  Source.vector_family_tendsto_zero_of_components s q hq
    (fun ε => physicalForce_smooth ν hv x₀ T ε hθ hη)
    (fun i => scalarPhysicalForce_negative_tendsto_zero ν hv x₀ T hθ hη hθc hηc i hs hs0 q hβ)

/-- Orders at or below the homogeneous-integrability threshold are treated
by inhomogeneous monotonicity, never by an invalid low-frequency integral. -/
theorem scalarPhysicalForce_all_negative_tendsto_zero (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3)
    {s : ℝ} (hs0 : s ≤ 0) (q : ℝ≥0∞) (hβ : 0 < 2 / q.toReal - 1 / 2 - s) :
    Filter.Tendsto (fun ε => eLpNorm (fun t => Source.fourierSobolevNorm s
      (fun x => scalarPhysicalForce ν v x₀ T θ η i ε (t, x))) q volume)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  by_cases hs : -3 / 2 < s
  · exact scalarPhysicalForce_negative_tendsto_zero ν hv x₀ T hθ hη hθc hηc i hs hs0 q hβ
  · have hβr : 0 < 2 / q.toReal - 1 / 2 - (-1 : ℝ) := by
      have hn : 0 ≤ 2 / q.toReal := div_nonneg (by norm_num) ENNReal.toReal_nonneg
      linarith
    have ht := scalarPhysicalForce_negative_tendsto_zero ν hv x₀ T hθ hη hθc hηc i
      (s := -1) (by norm_num) (by norm_num) q hβr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    · exact Eventually.of_forall (fun _ => bot_le)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact scalarPhysicalForce_eLpNorm_mono ν hv x₀ T ε (ne_of_gt hε) hθ hη hθc hηc i
        (show s ≤ -1 by linarith) q

theorem vectorPhysicalForce_all_negative_tendsto_zero (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {s : ℝ} (hs0 : s ≤ 0) (q : ℝ≥0∞) (hq : 1 ≤ q)
    (hβ : 0 < 2 / q.toReal - 1 / 2 - s) :
    Filter.Tendsto (fun ε => eLpNorm (Source.vectorFourierSobolevNorm s
      (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε))) q volume)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  Source.vector_family_tendsto_zero_of_components s q hq
    (fun ε => physicalForce_smooth ν hv x₀ T ε hθ hη)
    (fun i => scalarPhysicalForce_all_negative_tendsto_zero ν hv x₀ T hθ hη hθc hηc i hs0 q hβ)

end NSFormalization.Paper1.CorrectionForceNorms
