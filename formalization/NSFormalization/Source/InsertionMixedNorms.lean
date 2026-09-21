import NSFormalization.Source.InsertionFamily
import NSFormalization.Source.MixedNormAddition
import NSFormalization.Paper1.CorrectionVectorNorms

/-! Mixed Lebesgue force convergence for the same singular insertion family. -/
noncomputable section
namespace NSFormalization.Source.InsertionFamily
open NavierStokes.ProblemStatement MeasureTheory Filter Topology
open Paper1.CorrectionProfile Paper1.CorrectionForceNorms Paper1.CorrectionMixedNorms
open scoped ContDiff ENNReal

theorem force_mixed_tendsto_zero (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (p q : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hβ : 0 < -3 + 3 / p.toReal + 2 / q.toReal) :
    Tendsto (fun ε : ℝ => mixedNorm p q (force ν f v x₀ T θ η ε))
      (𝓝[>] 0) (𝓝 0) := by
  apply mixed_family_add_tendsto_zero p q hp hq
    (fun ε => physicalForce_smooth ν hv x₀ T ε hθ hη)
    (fun _ => Source.parabolicForce_smooth _ _ _ hf)
    (fun ε hε => physicalForce_compact ν v x₀ T ε hε.ne' hθc hηc)
    (fun _ _ => Source.parabolicForce_compact _ _ _ hfc)
  · exact physical_force_mixed_tendsto_zero ν hv x₀ T hθ hη hθc hηc p q (by linarith)
  · exact compact_force_mixed_tendsto_zero hf hfc p q hβ (fun ε => T - ε ^ 2) (fun _ => x₀)

end NSFormalization.Source.InsertionFamily
