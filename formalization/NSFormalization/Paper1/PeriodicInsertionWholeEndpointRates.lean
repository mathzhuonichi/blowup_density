import NSFormalization.Source.InsertionForceConvergence
import NSFormalization.Source.ForceNormAddition
import NSFormalization.Paper1.PeriodicPacketEndpointRates
import NSFormalization.Paper1.PeriodicCorrectionEndpointRates
import NSFormalization.Paper3.AllOrderFourierTime

/-! Whole-space endpoint rates for the complete insertion force. -/
noncomputable section
namespace NSFormalization.Paper1.PeriodicInsertionWholeEndpointRates
open Set Filter MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Source NSFormalization.Source.InsertionFamily
open NSFormalization.Paper1.PeriodicPacketEndpointRates
open NSFormalization.Paper1.PeriodicCorrectionEndpointRates
open NSFormalization.Paper1.CorrectionForceNorms
open NSFormalization.Paper1.CorrectionProfile
open scoped ContDiff ENNReal FourierTransform Topology

/-- The correction and packet endpoint rates assemble to finite endpoint rates
for the complete insertion force. -/
theorem insertion_vector_whole_endpoint_rates
    (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hv : ContDiff ℝ ∞ v) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∃ C₀ C₁ : ℝ≥0∞, C₀ < (⊤ : ℝ≥0∞) ∧ C₁ < (⊤ : ℝ≥0∞) ∧
      ∀ ε ∈ Ioc (0 : ℝ) 1,
        eLpNorm (vectorFourierSobolevNorm 0
          (InsertionFamily.force ν f v 0 T θ η ε)) 1 volume ≤
            ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * C₀ ∧
        eLpNorm (vectorFourierSobolevNorm 1
          (InsertionFamily.force ν f v 0 T θ η ε)) 1 volume ≤
            ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * C₁ := by
  obtain ⟨Cc₀, Cc₁, hCc₀, hCc₁, hcorr⟩ :=
    correction_vector_whole_endpoint_rates ν hv 0 T hθ hη hθc hηc
  let Cp₀ : ℝ≥0∞ := ∑ i : Fin 3,
      eLpNorm (fun t => fourierSobolevNorm 0
        (fun x => coordinateForce f i (t, x))) 1 volume
  let Cp₁ : ℝ≥0∞ := ∑ i : Fin 3,
      eLpNorm (fun t => fourierSobolevNorm 1
        (fun x => coordinateForce f i (t, x))) 1 volume
  have hCp₀ : Cp₀ < (⊤ : ℝ≥0∞) := by
    dsimp [Cp₀]
    apply (ENNReal.sum_lt_top).2
    intro i hi
    exact (Paper3.memLp_fourierSobolev_time 0 (coordinateForce_smooth hf i)
      (coordinateForce_compact hfc i) 1).eLpNorm_lt_top
  have hCp₁ : Cp₁ < (⊤ : ℝ≥0∞) := by
    dsimp [Cp₁]
    apply (ENNReal.sum_lt_top).2
    intro i hi
    exact (Paper3.memLp_fourierSobolev_time 1 (coordinateForce_smooth hf i)
      (coordinateForce_compact hfc i) 1).eLpNorm_lt_top
  refine ⟨Cc₀ + Cp₀, Cc₁ + Cp₁,
    (ENNReal.add_lt_top).2 ⟨hCc₀, hCp₀⟩,
    (ENNReal.add_lt_top).2 ⟨hCc₁, hCp₁⟩, ?_⟩
  intro ε hε
  have hεpos : 0 < ε := hε.1
  have hεle : ε ≤ 1 := hε.2
  have hpow0 : ε ^ ((3 : ℝ) / 2) ≤ ε ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hεpos hεle (by norm_num)
  have hpow1 : ε ^ ((1 : ℝ) / 2) ≤ ε ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hεpos hεle (by norm_num)
  have hpow0E := ENNReal.ofReal_le_ofReal hpow0
  have hpow1E := ENNReal.ofReal_le_ofReal hpow1
  have hcorr0 := (hcorr ε hε).1
  have hcorr1 := (hcorr ε hε).2
  have hpacket0 := packet_vector_H0_L1_endpoint_bound hf hfc hεpos hεle
    (T - ε ^ 2)
  have hpacket1 := packet_vector_H1_L1_endpoint_bound hf hfc hεpos hεle
    (T - ε ^ 2)
  have hadd0 := eLpNorm_vector_add_le (s := 0) (q := 1)
    (F := Source.correctionForce ν v (physicalCorrection v 0 T θ η ε))
    (G := Source.parabolicForce ε⁻¹ (T - ε ^ 2) 0 f) le_rfl
    (physicalForce_smooth ν hv 0 T ε hθ hη)
    (Source.parabolicForce_smooth (ε⁻¹) (T - ε ^ 2) 0 hf)
    (physicalForce_compact ν v 0 T ε hεpos.ne' hθc hηc)
    (Source.parabolicForce_compact (ε⁻¹) (T - ε ^ 2) 0 hfc)
  have hadd1 := eLpNorm_vector_add_le (s := 1) (q := 1)
    (F := Source.correctionForce ν v (physicalCorrection v 0 T θ η ε))
    (G := Source.parabolicForce ε⁻¹ (T - ε ^ 2) 0 f) le_rfl
    (physicalForce_smooth ν hv 0 T ε hθ hη)
    (Source.parabolicForce_smooth (ε⁻¹) (T - ε ^ 2) 0 hf)
    (physicalForce_compact ν v 0 T ε hεpos.ne' hθc hηc)
    (Source.parabolicForce_compact (ε⁻¹) (T - ε ^ 2) 0 hfc)
  have heq : InsertionFamily.force ν f v 0 T θ η ε =
      Source.correctionForce ν v (physicalCorrection v 0 T θ η ε) +
        Source.parabolicForce ε⁻¹ (T - ε ^ 2) 0 f := by
    funext z
    rfl
  constructor
  · rw [heq]
    calc
      _ ≤ eLpNorm (vectorFourierSobolevNorm 0
          (Source.correctionForce ν v (physicalCorrection v 0 T θ η ε))) 1 volume +
          eLpNorm (vectorFourierSobolevNorm 0
            (Source.parabolicForce ε⁻¹ (T - ε ^ 2) 0 f)) 1 volume := hadd0
      _ ≤ ENNReal.ofReal (ε ^ ((3 : ℝ) / 2)) * Cc₀ +
          ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * Cp₀ := add_le_add hcorr0 hpacket0
      _ ≤ ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * (Cc₀ + Cp₀) := by
        calc
          _ ≤ ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * Cc₀ +
              ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * Cp₀ := by gcongr
          _ = _ := (mul_add _ _ _).symm
  · rw [heq]
    calc
      _ ≤ eLpNorm (vectorFourierSobolevNorm 1
          (Source.correctionForce ν v (physicalCorrection v 0 T θ η ε))) 1 volume +
          eLpNorm (vectorFourierSobolevNorm 1
            (Source.parabolicForce ε⁻¹ (T - ε ^ 2) 0 f)) 1 volume := hadd1
      _ ≤ ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * Cc₁ +
          ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * Cp₁ := add_le_add hcorr1 hpacket1
      _ ≤ ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * (Cc₁ + Cp₁) := by
        calc
          _ ≤ ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * Cc₁ +
              ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * Cp₁ := by gcongr
          _ = _ := (mul_add _ _ _).symm

end NSFormalization.Paper1.PeriodicInsertionWholeEndpointRates
