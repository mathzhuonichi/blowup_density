import Mathlib.Analysis.Real.Pi.Bounds
import NSFormalization.Paper1.PeriodicMeanZero
import NSFormalization.Paper1.PeriodicSobolevHilbert
import NSFormalization.Paper1.PeriodicFiniteMode

/-! Finite mean-zero Poincare estimate for periodic Fourier data.

The estimate is stated with an explicit positive lower bound on the nonzero
angular frequencies.  This keeps the arithmetic lower-bound obligation
separate from the analytic finite-spectral argument.
-/
noncomputable section
namespace NSFormalization.Paper1
open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped BigOperators

/-- Finite spectral Poincare estimate after removing the zero Fourier mode. -/
theorem finite_meanZero_l2_le_homogeneousHalfEnergy
    (c : TorusFreq → ℂ) (S : Finset TorusFreq) (lam : ℝ)
    (hlam : 0 < lam)
    (hlower : ∀ k ∈ S, k ≠ 0 → lam ≤ periodicAngularMagnitude k)
    (hzero : c 0 = 0) :
    (S.sum (fun k => ‖c k‖ ^ 2)) ≤ lam⁻¹ * homogeneousHalfEnergy c S := by
  have hlam0 : 0 ≤ lam := hlam.le
  have hlaminv : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam0
  have hterm : ∀ k ∈ S, ‖c k‖ ^ 2 ≤
      lam⁻¹ * (periodicAngularMagnitude k * ‖c k‖ ^ 2) := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp [hzero]
    · have hfreq : lam ≤ periodicAngularMagnitude k := hlower k hk hk0
      have hnonneg : 0 ≤ ‖c k‖ ^ 2 := sq_nonneg _
      have hmul : lam * ‖c k‖ ^ 2 ≤ periodicAngularMagnitude k * ‖c k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hfreq hnonneg
      calc
        ‖c k‖ ^ 2 = lam⁻¹ * (lam * ‖c k‖ ^ 2) := by
          field_simp
        _ ≤ lam⁻¹ * (periodicAngularMagnitude k * ‖c k‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hmul hlaminv
  calc
    S.sum (fun k => ‖c k‖ ^ 2) ≤
        S.sum (fun k => lam⁻¹ * (periodicAngularMagnitude k * ‖c k‖ ^ 2)) := by
      exact Finset.sum_le_sum (fun k hk => hterm k hk)
    _ = lam⁻¹ * homogeneousHalfEnergy c S := by
      simp only [homogeneousHalfEnergy]
      rw [Finset.mul_sum]

/-- The same estimate for the actual Fourier coefficients of a mean-zero field. -/
theorem finite_periodicFourier_meanZero_l2_le_homogeneousHalfEnergy
    (f : Space → ℂ) (S : Finset TorusFreq) (lam : ℝ)
    (hlam : 0 < lam)
    (hlower : ∀ k ∈ S, k ≠ 0 → lam ≤ periodicAngularMagnitude k)
    (hmean : cubeIntegral f = 0) :
    (S.sum (fun k => ‖periodicFourierCoeff f k‖ ^ 2)) ≤
      lam⁻¹ * homogeneousHalfEnergy (fun k => periodicFourierCoeff f k) S := by
  apply finite_meanZero_l2_le_homogeneousHalfEnergy
  · exact hlam
  · exact hlower
  · exact periodicFourierCoeff_zero_eq_zero_iff f |>.mpr hmean

lemma exists_nonzero_coordinate (k : TorusFreq) (hk : k ≠ 0) :
    ∃ i : Fin 3, k i ≠ 0 := by
  by_contra h
  push_neg at h
  apply hk
  funext i
  exact h i

/-- Every nonzero integer torus frequency has angular magnitude at least one. -/
theorem one_le_periodicAngularMagnitude {k : TorusFreq} (hk : k ≠ 0) :
    1 ≤ periodicAngularMagnitude k := by
  obtain ⟨i, hi⟩ := exists_nonzero_coordinate k hk
  unfold periodicAngularMagnitude
  rw [periodicFrequencyWeight_eq]
  simp only [add_sub_cancel_left]
  have hcoord : (1 : ℝ) ≤ (k i : ℝ)^2 := by
    have hz : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
    have hz' : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast hz
    simpa [sq_abs] using hz'
  have hsum : (1 : ℝ) ≤ ∑ j : Fin 3, (k j : ℝ)^2 := by
    exact le_trans hcoord (Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (f := fun j : Fin 3 => (k j : ℝ)^2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  have hpi : (1 : ℝ) ≤ (2 * Real.pi)^2 := by
    have hp : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [sq_nonneg (2 * Real.pi - 1)]
  have harg : (1 : ℝ) ≤ (2 * Real.pi)^2 * ∑ j : Fin 3, (k j : ℝ)^2 := by
    have hp2 : 0 ≤ (2 * Real.pi)^2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsum hp2]
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt harg

/-- Canonical unit lower bound for finite nonzero torus spectra. -/
theorem finite_meanZero_l2_le_homogeneousHalfEnergy_one
    (c : TorusFreq → ℂ) (S : Finset TorusFreq) (hzero : c 0 = 0) :
    S.sum (fun k => ‖c k‖ ^ 2) ≤ homogeneousHalfEnergy c S := by
  have h := finite_meanZero_l2_le_homogeneousHalfEnergy c S 1 one_pos
    (fun k hk hk0 => one_le_periodicAngularMagnitude hk0) hzero
  simpa using h

end NSFormalization.Paper1
