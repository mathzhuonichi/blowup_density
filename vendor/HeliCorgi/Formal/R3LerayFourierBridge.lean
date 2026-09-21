import Formal.R3LerayL2Operator

namespace MNS2

open MeasureTheory FourierTransform
open scoped FourierTransform

noncomputable section

/-- The closed frequency-side kernel of normalized divergence. -/
def r3L2FrequencySolenoidalSubmodule : Submodule ℂ R3L2Velocity :=
  r3NormalizedDivergenceFrequencyAux.ker

local instance r3L2FrequencySolenoidalSubmodule_completeSpace :
    CompleteSpace r3L2FrequencySolenoidalSubmodule := by
  change CompleteSpace r3NormalizedDivergenceFrequencyAux.ker
  infer_instance

local instance r3L2SolenoidalSubmodule_completeSpace_fourierBridge :
    CompleteSpace r3L2SolenoidalSubmodule := by
  change CompleteSpace r3NormalizedDivergenceL2OperatorAux.ker
  infer_instance

@[simp]
theorem mem_r3L2FrequencySolenoidalSubmodule_iff (f : R3L2Velocity) :
    f ∈ r3L2FrequencySolenoidalSubmodule ↔
      r3NormalizedDivergenceFrequencyAux f = 0 := by
  simp [r3L2FrequencySolenoidalSubmodule]

/-- Physical-space solenoidality is exactly frequency-space solenoidality after Fourier transform. -/
@[simp]
theorem fourier_mem_r3L2FrequencySolenoidalSubmodule_iff (f : R3L2Velocity) :
    𝓕 f ∈ r3L2FrequencySolenoidalSubmodule ↔
      f ∈ r3L2SolenoidalSubmodule := by
  change r3NormalizedDivergenceFrequencyAux (𝓕 f) = 0 ↔
    r3NormalizedDivergenceFrequencyAux (𝓕 f) = 0
  rfl

/-- The Plancherel Fourier equivalence carries the physical solenoidal subspace onto the
frequency-side divergence-free kernel. -/
theorem map_r3L2SolenoidalSubmodule_fourier :
    r3L2SolenoidalSubmodule.map
        ((MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).toLinearEquiv :
          R3L2Velocity →ₗ[ℂ] R3L2Velocity) =
      r3L2FrequencySolenoidalSubmodule := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact (fourier_mem_r3L2FrequencySolenoidalSubmodule_iff f).2 hf
  · intro hg
    refine ⟨(MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).symm g, ?_, ?_⟩
    · apply
        (fourier_mem_r3L2FrequencySolenoidalSubmodule_iff
          ((MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).symm g)).1
      change
        (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C)
            ((MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).symm g) ∈
          r3L2FrequencySolenoidalSubmodule
      rw [(MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).apply_symm_apply]
      exact hg
    · change
        (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C)
            ((MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).symm g) = g
      exact (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).apply_symm_apply g

/-- Orthogonal projection onto the frequency-side normalized-divergence kernel. -/
def r3LerayL2FrequencyOperator : R3L2Velocity →L[ℂ] R3L2Velocity :=
  r3L2FrequencySolenoidalSubmodule.starProjection

/-- The frequency-side projector lands in the normalized-divergence kernel. -/
theorem r3LerayL2FrequencyOperator_mem_solenoidal (f : R3L2Velocity) :
    r3LerayL2FrequencyOperator f ∈ r3L2FrequencySolenoidalSubmodule := by
  simpa [r3LerayL2FrequencyOperator] using
    (Submodule.starProjection_apply_mem r3L2FrequencySolenoidalSubmodule f)

/-- The physical Leray projector is conjugate under Plancherel Fourier transform to the
orthogonal projector onto the frequency-side divergence-free kernel. -/
theorem fourier_r3LerayL2Operator (f : R3L2Velocity) :
    𝓕 (r3LerayL2Operator f) =
      r3LerayL2FrequencyOperator (𝓕 f) := by
  change
    (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C) (r3LerayL2Operator f) =
      r3LerayL2FrequencyOperator
        ((MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C) f)
  have h :=
    Submodule.starProjection_map_apply
      (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C)
      r3L2SolenoidalSubmodule
      ((MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C) f)
  simpa [map_r3L2SolenoidalSubmodule_fourier,
    r3LerayL2Operator, r3LerayL2FrequencyOperator] using h.symm

end

end MNS2
