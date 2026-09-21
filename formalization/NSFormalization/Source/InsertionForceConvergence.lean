import NSFormalization.Source.InsertionFamily
import NSFormalization.Source.ForceNormAddition
import NSFormalization.Paper1.CorrectionVectorNorms

/-! Sobolev force convergence for the exact fixed-profile insertion family.
The packet and correction terms are added in their actual vector Hilbert norm. -/
noncomputable section
namespace NSFormalization.Source.InsertionFamily
open NavierStokes.ProblemStatement MeasureTheory Filter Topology
open Paper1.CorrectionProfile Paper1.CorrectionForceNorms
open scoped ContDiff ENNReal

theorem force_smooth_all (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T ε : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (force ν f v x₀ T θ η ε) :=
  (physicalForce_smooth ν hv x₀ T ε hθ hη).add
    (Source.parabolicForce_smooth _ _ _ hf)

theorem force_compact_nonzero (ν : ℝ) (v : VelocityField) {f : VelocityField}
    (hf : HasCompactSupport f) (x₀ : Space) (T ε : ℝ) (hε : ε ≠ 0)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    HasCompactSupport (force ν f v x₀ T θ η ε) :=
  (physicalForce_compact ν v x₀ T ε hε hθc hηc).add
    (Source.parabolicForce_compact _ _ _ hf)

theorem force_L1_tendsto_zero (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {s : ℝ} (hs : s < 1 / 2) :
    Tendsto (fun ε : ℝ => eLpNorm (vectorFourierSobolevNorm s
      (force ν f v x₀ T θ η ε)) 1 volume) (𝓝[>] 0) (𝓝 0) := by
  apply vector_family_add_tendsto_zero s 1 le_rfl
    (fun ε => physicalForce_smooth ν hv x₀ T ε hθ hη)
    (fun _ => Source.parabolicForce_smooth _ _ _ hf)
    (fun ε hε => physicalForce_compact ν v x₀ T ε hε.ne' hθc hηc)
    (fun _ _ => Source.parabolicForce_compact _ _ _ hfc)
  · by_cases hs0 : s ≤ 0
    · exact vectorPhysicalForce_all_negative_tendsto_zero ν hv x₀ T hθ hη hθc hηc
        hs0 1 le_rfl (by norm_num; linarith)
    · exact vectorPhysicalForce_positive_tendsto_zero ν hv x₀ T hθ hη hθc hηc
        (by linarith) (le_of_not_ge hs0) 1 le_rfl (by norm_num; linarith)
  · exact compact_vector_force_L1_tendsto hs hf hfc (fun ε => T - ε ^ 2) (fun _ => x₀)

theorem force_L2_tendsto_zero (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {s : ℝ} (hs : s < -1 / 2) :
    Tendsto (fun ε : ℝ => eLpNorm (vectorFourierSobolevNorm s
      (force ν f v x₀ T θ η ε)) 2 volume) (𝓝[>] 0) (𝓝 0) := by
  apply vector_family_add_tendsto_zero s 2 (by norm_num)
    (fun ε => physicalForce_smooth ν hv x₀ T ε hθ hη)
    (fun _ => Source.parabolicForce_smooth _ _ _ hf)
    (fun ε hε => physicalForce_compact ν v x₀ T ε hε.ne' hθc hηc)
    (fun _ _ => Source.parabolicForce_compact _ _ _ hfc)
  · exact vectorPhysicalForce_all_negative_tendsto_zero ν hv x₀ T hθ hη hθc hηc
      (by linarith) 2 (by norm_num) (by norm_num; linarith)
  · exact compact_vector_force_L2_tendsto hs hf hfc (fun ε => T - ε ^ 2) (fun _ => x₀)

/-- The actual total force perturbation converges in the manuscripts' exact
unitary angular Fourier norm on the entire time axis. -/
theorem force_angular_L1_tendsto_zero (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {s : ℝ} (hs : s < 1 / 2) :
    Tendsto (fun ε : ℝ => eLpNorm (vectorAngularSobolevNorm s
      (force ν f v x₀ T θ η ε)) 1 volume) (𝓝[>] 0) (𝓝 0) :=
  angular_family_tendsto_zero s 1 (fun ε => force_smooth_all ν hf hv x₀ T ε hθ hη)
    (fun ε hε => force_compact_nonzero ν v hfc x₀ T ε hε.ne' hθc hηc)
    (force_L1_tendsto_zero ν hf hfc hv x₀ T hθ hη hθc hηc hs)

theorem force_angular_L2_tendsto_zero (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {s : ℝ} (hs : s < -1 / 2) :
    Tendsto (fun ε : ℝ => eLpNorm (vectorAngularSobolevNorm s
      (force ν f v x₀ T θ η ε)) 2 volume) (𝓝[>] 0) (𝓝 0) :=
  angular_family_tendsto_zero s 2 (fun ε => force_smooth_all ν hf hv x₀ T ε hθ hη)
    (fun ε hε => force_compact_nonzero ν v hfc x₀ T ε hε.ne' hθc hηc)
    (force_L2_tendsto_zero ν hf hfc hv x₀ T hθ hη hθc hηc hs)

end NSFormalization.Source.InsertionFamily
