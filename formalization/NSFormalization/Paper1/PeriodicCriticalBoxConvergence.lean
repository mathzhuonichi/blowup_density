import NSFormalization.Paper1.PeriodicCriticalLowQuantitative
import NSFormalization.Paper1.FourierReconstructionAdapter
import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Radius and box truncation of the periodic Fourier series

The finite low-frequency estimates retain a cutoff-dependent cardinality.  This
file adds an independent convergence statement for the canonical integer boxes:
box partial sums converge to the physical field under absolute coefficient
summability, and their order-zero spectral energies converge by Parseval.  No
critical uniform embedding is used.
-/
noncomputable section
namespace NSFormalization.Paper1

open Set Filter MeasureTheory NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped BigOperators ContDiff ENNReal Topology

/-- The integer radius needed to contain one frequency vector. -/
def periodicFrequencyRadius (k : PeriodicFrequency) : ℕ :=
  ∑ i : Fin 3, (k i).natAbs

/-- Every frequency lies in a sufficiently large integer frequency box. -/
theorem mem_periodicFrequencyBox_of_le_radius (k : PeriodicFrequency) :
    k ∈ periodicFrequencyBox (periodicFrequencyRadius k) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi : (k i).natAbs ≤ periodicFrequencyRadius k := by
    unfold periodicFrequencyRadius
    exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (f := fun j : Fin 3 => (k j).natAbs) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hi_cast : ((k i).natAbs : ℤ) ≤ (periodicFrequencyRadius k : ℤ) := by
    exact_mod_cast hi
  have hk_upper : k i ≤ (periodicFrequencyRadius k : ℤ) :=
    (Int.le_natAbs (a := k i)).trans hi_cast
  have hk_abs : |k i| ≤ (periodicFrequencyRadius k : ℤ) := by
    simpa only [Int.natCast_natAbs] using hi_cast
  have hk_lower : -(periodicFrequencyRadius k : ℤ) ≤ k i :=
    neg_le_of_abs_le hk_abs
  exact Finset.mem_Icc.mpr ⟨hk_lower, hk_upper⟩

/-- The frequency boxes are monotone in their radius. -/
theorem monotone_periodicFrequencyBox :
    Monotone periodicFrequencyBox := by
  intro R₁ R₂ hR
  intro k hk
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi := (Fintype.mem_piFinset.mp hk) i
  have hRz : (R₁ : ℤ) ≤ (R₂ : ℤ) := by exact_mod_cast hR
  have hneg : -(R₂ : ℤ) ≤ -(R₁ : ℤ) := neg_le_neg hRz
  exact Finset.Icc_subset_Icc hneg hRz hi

/-- Integer boxes exhaust the full frequency lattice. -/
theorem tendsto_periodicFrequencyBox_atTop :
    Tendsto periodicFrequencyBox (atTop : Filter ℕ) (atTop : Filter (Finset PeriodicFrequency)) := by
  apply Filter.tendsto_atTop_finset_of_monotone monotone_periodicFrequencyBox
  intro k
  exact ⟨periodicFrequencyRadius k, mem_periodicFrequencyBox_of_le_radius k⟩

/-- Order-zero Parseval energy of box truncations converges to the physical L² energy. -/
theorem tendsto_periodicFourier_box_energy
    {f : Space → ℂ} (hf : Continuous f) :
    Tendsto (fun R : ℕ =>
      ∑ k ∈ periodicFrequencyBox R, ‖periodicFourierCoeff f k‖ ^ 2)
      atTop (𝓝 (cubeIntegral (fun x => ‖f x‖ ^ 2))) := by
  exact (hasSum_sq_periodicFourierCoeff f hf).comp
    tendsto_periodicFrequencyBox_atTop

/-- Physical Fourier sums over expanding integer boxes converge pointwise. -/
theorem tendsto_periodicFourier_box_sum
    {f : Space → ℂ} (hf : Continuous f) (hp : UnitPeriods f)
    (hc : Summable (periodicFourierCoeff f)) (x : Space) :
    Tendsto (fun R : ℕ =>
      finitePeriodicFourierSum (fun k => periodicFourierCoeff f k)
        (periodicFrequencyBox R) x)
      atTop (𝓝 (f x)) := by
  exact (hasSum_periodicFourier_physical hf hp hc x).comp
    tendsto_periodicFrequencyBox_atTop

end NSFormalization.Paper1

namespace NSFormalization.Paper1
open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped BigOperators ContDiff ENNReal

/-- The box truncation inherits the finite critical estimate with its explicit
cardinality `(2 R + 1)^3`; the factor is not made uniform in `R`. -/
theorem cubeIntegral_norm_periodicFourier_box_sum_pow_three_le
    {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f)
    (R : ℕ) (hmean : cubeIntegral f = 0) :
    cubeIntegral (fun x =>
      ‖finitePeriodicFourierSum (fun k => periodicFourierCoeff f k)
        (periodicFrequencyBox R) x‖ ^ (3 : ℕ)) ≤
      (Real.sqrt ((2 * R + 1) ^ 3) *
        periodicSobolevNorm (1 / 2 : ℝ) f) ^ (3 : ℕ) := by
  have h := cubeIntegral_norm_fin_periodicFourier_sum_pow_three_le_of_periodicSobolev
    hf hp (periodicFrequencyBox R) hmean
  rw [card_periodicFrequencyBox] at h
  convert h using 1 <;> norm_num

end NSFormalization.Paper1
