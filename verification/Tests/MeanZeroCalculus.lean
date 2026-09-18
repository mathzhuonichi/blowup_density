import Contracts.V1.MeanZeroCalculus
import Bindings.MeanZeroCalculus
import TestSupport.Axioms

/-!
# Tests for `T01.mean_zero_calculus`

This module checks the transported declaration, independently restates every
constant and every one of the nine fields of the reconciled Spec
(`research/T12/Spec.lean:281-478`), and instantiates the critical, gradient and
continuation fields on a genuine nonzero smooth mean-zero periodic field, so
that neither the hypotheses nor the conclusions are vacuous.
-/

noncomputable section

namespace BlowupDensity.Tests

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.MeanZeroCalculus
open scoped ContDiff ENNReal BigOperators

/-- The implementation supplies all nine fields of the mean-zero calculus
contract, with its seven constants. -/
def checkedMeanZeroCalculus : MeanZeroSobolevCalculusAPI :=
  Bindings.meanZeroCalculus

run_cmd TestSupport.checkAxioms ``checkedMeanZeroCalculus

/-! ## Independent conformance with the constants of `research/T12/Spec.lean` -/

example : ∀ m : ℕ, 0 < checkedMeanZeroCalculus.Cproduct m :=
  checkedMeanZeroCalculus.Cproduct_pos

example : 0 < checkedMeanZeroCalculus.Cinfty :=
  checkedMeanZeroCalculus.Cinfty_pos

example : 0 < checkedMeanZeroCalculus.CcriticalHalf :=
  checkedMeanZeroCalculus.CcriticalHalf_pos

example : 0 < checkedMeanZeroCalculus.CcriticalThreeHalves :=
  checkedMeanZeroCalculus.CcriticalThreeHalves_pos

example : 0 < checkedMeanZeroCalculus.Csix :=
  checkedMeanZeroCalculus.Csix_pos

example : 0 < checkedMeanZeroCalculus.CHtwo :=
  checkedMeanZeroCalculus.CHtwo_pos

example : ∀ s : ℝ, 0 ≤ s → 0 < checkedMeanZeroCalculus.Cgap s :=
  checkedMeanZeroCalculus.Cgap_pos

/-! ## Independent conformance with the nine fields of `research/T12/Spec.lean` -/

example :
    ∀ m : ℕ, 2 ≤ m → ∀ a b : Space → ℝ,
      MemPeriodicHmScalar m a → MemPeriodicHmScalar m b →
        periodicScalarSobolevENorm (m : ℝ) (fun x ↦ a x * b x) ≤
          ENNReal.ofReal (checkedMeanZeroCalculus.Cproduct m) *
            (periodicScalarSobolevENorm 2 a * periodicScalarSobolevENorm (m : ℝ) b +
              periodicScalarSobolevENorm 2 b * periodicScalarSobolevENorm (m : ℝ) a) :=
  checkedMeanZeroCalculus.tameProduct

example :
    ∀ v : SpatialField, MemPeriodicHmVector 2 v →
      periodicLpENorm ⊤ v ≤
        ENNReal.ofReal checkedMeanZeroCalculus.Cinfty * periodicSobolevENorm 2 v :=
  checkedMeanZeroCalculus.boundedRepresentative

example :
    ∀ v : SpatialField, MemPeriodicHomogeneous (1 / 2) v →
      periodicLpENorm 3 v ≤
        ENNReal.ofReal checkedMeanZeroCalculus.CcriticalHalf *
          periodicHomogeneousENorm (1 / 2) v :=
  checkedMeanZeroCalculus.velocityCriticalL3

example :
    ∀ v : SpatialField, SmoothPeriodicT v →
      ∃ Lv : SpatialField, IsPeriodicLambda v Lv :=
  checkedMeanZeroCalculus.lambda_exists

example :
    ∀ (v Lv : SpatialField), SmoothPeriodicT v →
      MemPeriodicHomogeneous (3 / 2) v → IsPeriodicLambda v Lv →
        periodicLpENorm 3 (gradientTensor v) + periodicLpENorm 3 Lv ≤
          ENNReal.ofReal checkedMeanZeroCalculus.CcriticalThreeHalves *
            periodicHomogeneousENorm (3 / 2) v :=
  checkedMeanZeroCalculus.gradientLambdaCriticalL3

example :
    ∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v →
      periodicLpENorm 6 (gradientTensor v) ≤
        ENNReal.ofReal checkedMeanZeroCalculus.Csix * periodicLpENorm 2 (laplacian v) :=
  checkedMeanZeroCalculus.gradientLSix

example :
    ∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v →
      periodicSobolevENorm 2 v ≤
        ENNReal.ofReal checkedMeanZeroCalculus.CHtwo * periodicLpENorm 2 (laplacian v) :=
  checkedMeanZeroCalculus.hTwo_le_laplacian

example :
    ∀ s : ℝ, 0 ≤ s → ∀ v : SpatialField,
      MemPeriodicHomogeneous s v →
        periodicSobolevENorm s v ≤
          ENNReal.ofReal (checkedMeanZeroCalculus.Cgap s) * periodicHomogeneousENorm s v :=
  checkedMeanZeroCalculus.spectralGap

example :
    ∀ s : ℝ, 0 ≤ s → ∀ v : SpatialField,
      MemPeriodicHomogeneous s v →
        periodicHomogeneousENorm s v ≤ periodicSobolevENorm s v :=
  checkedMeanZeroCalculus.homogeneous_le_sobolev

/-! ## Non-vacuity on an explicit nonzero mean-zero periodic field

The witness is the one used by the T12 unit probes
(`research/T12/probes/rev396_nonvacuity.lean:70-137`): the mean-zero part of the
single cosine mode `x ↦ cos(2π x₀) · e₀`. -/

/-- A single-mode cosine vector field, `x ↦ cos(2π x₀)·e₀`. -/
def meanZeroProbeMode : SpatialField :=
  fun x => Real.cos (2 * Real.pi * x 0) • coordinateVector 0

theorem meanZeroProbeMode_contDiff : ContDiff ℝ ∞ meanZeroProbeMode := by
  have hproj : ContDiff ℝ ∞ (fun x : Space => x 0) := contDiff_piLp_apply 2
  exact (Real.contDiff_cos.comp (contDiff_const.mul hproj)).smul contDiff_const

theorem meanZeroProbe_coordinateVector_apply (i j : Fin 3) :
    (coordinateVector i) j = (if j = i then (1 : ℝ) else 0) := by
  simp [coordinateVector, PiLp.single_apply]

theorem meanZeroProbeMode_periodic : IsPeriodicSpatial meanZeroProbeMode := by
  intro x i
  show Real.cos (2 * Real.pi * (x + coordinateVector i) 0) • coordinateVector 0
      = Real.cos (2 * Real.pi * x 0) • coordinateVector 0
  have hadd : (x + coordinateVector i) 0 = x 0 + (if (0 : Fin 3) = i then 1 else 0) := by
    show x 0 + (coordinateVector i) 0 = _
    rw [meanZeroProbe_coordinateVector_apply]
  rcases eq_or_ne (0 : Fin 3) i with hi | hi
  · subst hi
    have hx : (x + coordinateVector (0 : Fin 3)) 0 = x 0 + 1 := by rw [hadd]; norm_num
    have heq : 2 * Real.pi * (x 0 + 1) = 2 * Real.pi * x 0 + 2 * Real.pi := by ring
    rw [hx, heq, Real.cos_add_two_pi]
  · have hx : (x + coordinateVector i) 0 = x 0 := by rw [hadd]; simp [hi]
    rw [hx]

/-- The non-vacuity witness: a nonzero smooth mean-zero periodic field. -/
def meanZeroProbe : SpatialField := meanZeroPartT meanZeroProbeMode

theorem meanZeroProbe_smoothPeriodic : SmoothPeriodicT meanZeroProbe := by
  refine ⟨meanZeroProbeMode_contDiff.sub contDiff_const, ?_⟩
  intro x i
  show meanZeroProbeMode (x + coordinateVector i) - meanT meanZeroProbeMode
      = meanZeroProbeMode x - meanT meanZeroProbeMode
  rw [meanZeroProbeMode_periodic x i]

theorem meanZeroProbe_meanZero : IsMeanZeroT meanZeroProbe :=
  (NSFormalization.Section3.T10.mean_decomposition meanZeroProbeMode
    meanZeroProbeMode_periodic
    (NSFormalization.Section3.T13.integrable_torusLift_space
      meanZeroProbeMode_contDiff.continuous)).2

theorem meanZeroProbe_ne_zero : meanZeroProbe ≠ (0 : SpatialField) := by
  intro h
  set p1 : Space := (2⁻¹ : ℝ) • coordinateVector (0 : Fin 3) with hp1
  have hp1coord : p1 0 = (2⁻¹ : ℝ) := by
    show (2⁻¹ : ℝ) • (coordinateVector (0 : Fin 3)) 0 = (2⁻¹ : ℝ)
    rw [meanZeroProbe_coordinateVector_apply]; simp
  have hp0coord : (0 : Space) 0 = (0 : ℝ) := by simp
  have hzero : meanZeroProbeMode (0 : Space) - meanZeroProbeMode p1 = 0 := by
    have e0 : meanZeroProbe (0 : Space) = 0 := by rw [h]; rfl
    have e1 : meanZeroProbe p1 = 0 := by rw [h]; rfl
    have hd : meanZeroProbe (0 : Space) - meanZeroProbe p1
        = meanZeroProbeMode (0 : Space) - meanZeroProbeMode p1 := by
      simp only [meanZeroProbe, meanZeroPartT]; abel
    rw [e0, e1, sub_zero] at hd
    exact hd.symm
  have hz0 : meanZeroProbeMode (0 : Space) = coordinateVector 0 := by
    show Real.cos (2 * Real.pi * (0 : Space) 0) • coordinateVector 0 = coordinateVector 0
    rw [hp0coord]; simp
  have hz1 : meanZeroProbeMode p1 = (-1 : ℝ) • coordinateVector 0 := by
    show Real.cos (2 * Real.pi * p1 0) • coordinateVector 0 = (-1 : ℝ) • coordinateVector 0
    rw [hp1coord]
    have hpi : 2 * Real.pi * (2⁻¹ : ℝ) = Real.pi := by ring
    rw [hpi, Real.cos_pi]
  rw [hz0, hz1, neg_one_smul, sub_neg_eq_add] at hzero
  have hcv : coordinateVector (0 : Fin 3) ≠ 0 := by
    intro hc
    have hca := meanZeroProbe_coordinateVector_apply 0 0
    rw [hc] at hca
    simp at hca
  have hs : (2 : ℝ) • coordinateVector (0 : Fin 3) = 0 := by rw [two_smul]; exact hzero
  exact hcv ((smul_eq_zero.mp hs).resolve_left (by norm_num))

theorem meanZeroProbe_memHomogeneous (s : ℝ) (hs : 0 < s) :
    MemPeriodicHomogeneous s meanZeroProbe :=
  ⟨meanZeroProbe_smoothPeriodic.2,
    NSFormalization.Section3.T10.memLp_torusLift_vector
      meanZeroProbe_smoothPeriodic.1.continuous 2,
    meanZeroProbe_meanZero,
    (NSFormalization.Section3.T13.periodicHomogeneousENorm_lt_top hs
      meanZeroProbeMode_periodic meanZeroProbeMode_contDiff).ne⟩

/-- The field is genuinely nonzero, so the instantiations below are not
vacuous. -/
example : meanZeroProbe ≠ (0 : SpatialField) := meanZeroProbe_ne_zero

/-- The critical field at the nonzero witness, with a finite right-hand side. -/
example :
    periodicLpENorm 3 meanZeroProbe ≤
      ENNReal.ofReal checkedMeanZeroCalculus.CcriticalHalf *
        periodicHomogeneousENorm (1 / 2) meanZeroProbe :=
  checkedMeanZeroCalculus.velocityCriticalL3 meanZeroProbe
    (meanZeroProbe_memHomogeneous (1 / 2) (by norm_num))

/-- The gradient-`L⁶` field at the nonzero witness. -/
example :
    periodicLpENorm 6 (gradientTensor meanZeroProbe) ≤
      ENNReal.ofReal checkedMeanZeroCalculus.Csix *
        periodicLpENorm 2 (laplacian meanZeroProbe) :=
  checkedMeanZeroCalculus.gradientLSix meanZeroProbe
    meanZeroProbe_smoothPeriodic meanZeroProbe_meanZero

/-- The continuation comparison at the nonzero witness. -/
example :
    periodicSobolevENorm 2 meanZeroProbe ≤
      ENNReal.ofReal checkedMeanZeroCalculus.CHtwo *
        periodicLpENorm 2 (laplacian meanZeroProbe) :=
  checkedMeanZeroCalculus.hTwo_le_laplacian meanZeroProbe
    meanZeroProbe_smoothPeriodic meanZeroProbe_meanZero

/-- The Lambda representative and the order-three-halves sum field at the
nonzero witness. -/
example :
    ∃ Lv : SpatialField, IsPeriodicLambda meanZeroProbe Lv ∧
      periodicLpENorm 3 (gradientTensor meanZeroProbe) + periodicLpENorm 3 Lv ≤
        ENNReal.ofReal checkedMeanZeroCalculus.CcriticalThreeHalves *
          periodicHomogeneousENorm (3 / 2) meanZeroProbe := by
  obtain ⟨Lv, hLv⟩ :=
    checkedMeanZeroCalculus.lambda_exists meanZeroProbe meanZeroProbe_smoothPeriodic
  exact ⟨Lv, hLv, checkedMeanZeroCalculus.gradientLambdaCriticalL3 meanZeroProbe Lv
    meanZeroProbe_smoothPeriodic
    (meanZeroProbe_memHomogeneous (3 / 2) (by norm_num)) hLv⟩

/-- The spectral-gap pair at the nonzero witness. -/
example :
    periodicSobolevENorm (1 / 2) meanZeroProbe ≤
        ENNReal.ofReal (checkedMeanZeroCalculus.Cgap (1 / 2)) *
          periodicHomogeneousENorm (1 / 2) meanZeroProbe ∧
      periodicHomogeneousENorm (1 / 2) meanZeroProbe ≤
        periodicSobolevENorm (1 / 2) meanZeroProbe :=
  ⟨checkedMeanZeroCalculus.spectralGap (1 / 2) (by norm_num) meanZeroProbe
      (meanZeroProbe_memHomogeneous (1 / 2) (by norm_num)),
    checkedMeanZeroCalculus.homogeneous_le_sobolev (1 / 2) (by norm_num) meanZeroProbe
      (meanZeroProbe_memHomogeneous (1 / 2) (by norm_num))⟩

end BlowupDensity.Tests
