import NSFormalization.Paper1.PeriodicInsertionEndpointAssembly
import NSFormalization.Paper1.PeriodicInsertionWholeEndpointRates

/-!
# Coordinate reduction for the insertion endpoint assembly

The vector whole-space endpoint bounds imply scalar component bounds because
each component is one summand of the squared Euclidean Fourier norm.  This
file records that finite-dimensional reduction and uses it to replace the
component endpoint profiles in the periodized insertion estimate by common
vector endpoint profiles.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicInsertionEndpointRateBound

open Set Filter MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicInsertionEndpointAssembly
open NSFormalization.Paper1.PeriodicInsertionWholeEndpointRates
open NSFormalization.Paper1.PeriodicForceConvergence
open NSFormalization.Source.InsertionFamily
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal FourierTransform Topology

theorem coordinate_fourierSobolevNorm_le_vector
    (s : ℝ) (F : VelocityField) (i : Fin 3) (t : ℝ) :
    fourierSobolevNorm s (fun x => coordinateForce F i (t, x)) ≤
      vectorFourierSobolevNorm s F t := by
  unfold vectorFourierSobolevNorm
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (fun j _ => fourierSobolevSq_nonneg s
    (fun x => coordinateForce F j (t, x))) (Finset.mem_univ i)

/-- The actual
insertion family has a periodized endpoint bound with common whole-space
endpoint profiles.  The factor three is the finite component count. -/
theorem eventually_actual_insertion_vector_periodized_endpoint_bound
    (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hv : ContDiff ℝ ∞ v) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ C₀ C₁ : ℝ≥0∞, C₀ < (⊤ : ℝ≥0∞) ∧ C₁ < (⊤ : ℝ≥0∞) ∧
      ∀ᶠ ε : ℝ in 𝓝[>] 0,
        eLpNorm (fun t => periodicVectorSobolevNorm s
          (periodize (InsertionFamily.force ν f v 0 T θ η ε)) t) 1 volume ≤
        3 * ((ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * C₀) ^ (1 - s) *
          (ENNReal.ofReal (2 * Real.pi) *
            (ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * C₁)) ^ s) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hrates⟩ :=
    insertion_vector_whole_endpoint_rates ν hf hfc hv T hθ hη hθc hηc
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  filter_upwards [
      eventually_actual_insertion_vector_periodized_endpoint_product
        ν hf hfc hv T hθ hη hθc hηc hs0 hs1,
      self_mem_nhdsWithin,
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with ε hperiod hε hε1
  have hεrange : ε ∈ Ioc (0 : ℝ) 1 := ⟨hε, hε1⟩
  have hr := hrates ε hεrange
  have hcomp0 (i : Fin 3) :
      eLpNorm (fun t => fourierSobolevNorm 0
        (fun x => coordinateForce (InsertionFamily.force ν f v 0 T θ η ε) i (t, x))) 1 volume ≤
        ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * C₀ := by
    apply (eLpNorm_mono_real (p := (1 : ℝ≥0∞)) (μ := volume) (f := fun t =>
      fourierSobolevNorm 0 (fun x => coordinateForce (InsertionFamily.force ν f v 0 T θ η ε) i (t, x)))
      (g := vectorFourierSobolevNorm 0 (InsertionFamily.force ν f v 0 T θ η ε)) ?_).trans
    · exact hr.1
    · intro t
      unfold Source.fourierSobolevNorm
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact coordinate_fourierSobolevNorm_le_vector 0 _ i t
  have hcomp1 (i : Fin 3) :
      eLpNorm (fun t => fourierSobolevNorm 1
        (fun x => coordinateForce (InsertionFamily.force ν f v 0 T θ η ε) i (t, x))) 1 volume ≤
        ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * C₁ := by
    apply (eLpNorm_mono_real (p := (1 : ℝ≥0∞)) (μ := volume) (f := fun t =>
      fourierSobolevNorm 1 (fun x => coordinateForce (InsertionFamily.force ν f v 0 T θ η ε) i (t, x)))
      (g := vectorFourierSobolevNorm 1 (InsertionFamily.force ν f v 0 T θ η ε)) ?_).trans
    · exact hr.2
    · intro t
      unfold Source.fourierSobolevNorm
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact coordinate_fourierSobolevNorm_le_vector 1 _ i t
  calc
    _ ≤ ∑ i : Fin 3,
        (eLpNorm (fun t => fourierSobolevNorm 0
          (fun x => coordinateForce (InsertionFamily.force ν f v 0 T θ η ε) i (t, x))) 1 volume) ^ (1 - s) *
          (ENNReal.ofReal (2 * Real.pi) *
            eLpNorm (fun t => fourierSobolevNorm 1
              (fun x => coordinateForce (InsertionFamily.force ν f v 0 T θ η ε) i (t, x))) 1 volume) ^ s := hperiod
    _ ≤ ∑ _i : Fin 3,
        (ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * C₀) ^ (1 - s) *
          (ENNReal.ofReal (2 * Real.pi) *
            (ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * C₁)) ^ s := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      · exact hcomp0 i
      · exact hcomp1 i
    _ = 3 * ((ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * C₀) ^ (1 - s) *
          (ENNReal.ofReal (2 * Real.pi) *
            (ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * C₁)) ^ s) := by
      simp [Finset.sum_const, Fintype.card_fin]

end NSFormalization.Paper1.PeriodicInsertionEndpointRateBound
