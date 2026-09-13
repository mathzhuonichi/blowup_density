import NSFormalization.Paper1.PeriodicSobolev

/-! Finite homogeneous half-order spectral energy in the unit-torus angular
frequency convention. The L3 embedding is a separate analytic theorem. -/
noncomputable section
namespace NSFormalization.Paper1
open scoped BigOperators

abbrev TorusFreq := PeriodicFrequency

/-- The Euclidean angular frequency magnitude |2πk| from the existing Bessel weight. -/
def periodicAngularMagnitude (k : TorusFreq) : ℝ :=
  Real.sqrt (periodicFrequencyWeight k - 1)

@[simp] theorem periodicAngularMagnitude_zero : periodicAngularMagnitude 0 = 0 := by
  simp [periodicAngularMagnitude, periodicFrequencyWeight]

def homogeneousHalfEnergy (c : TorusFreq → ℂ) (S : Finset TorusFreq) : ℝ :=
  ∑ k ∈ S, periodicAngularMagnitude k * ‖c k‖ ^ 2

theorem homogeneousHalfEnergy_nonneg (c : TorusFreq → ℂ) (S : Finset TorusFreq) :
    0 ≤ homogeneousHalfEnergy c S := by
  exact Finset.sum_nonneg (fun k hk => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))

/-- The zero frequency contributes zero regardless of its coefficient. -/
theorem homogeneousHalfEnergy_zero_mode (c : TorusFreq → ℂ) (S : Finset TorusFreq) :
    homogeneousHalfEnergy c (S.erase 0) = homogeneousHalfEnergy c S := by
  classical
  by_cases hm : 0 ∈ S
  · have h := Finset.sum_erase_add S (fun k => periodicAngularMagnitude k * ‖c k‖ ^ 2) hm
    simpa [homogeneousHalfEnergy] using h
  · simp [homogeneousHalfEnergy, hm]

/-- The correct homogeneous half-energy is controlled by the finite
inhomogeneous H^(1/2) spectral energy, with no support-size constant. -/
theorem homogeneousHalfEnergy_le_bessel (c : TorusFreq → ℂ) (S : Finset TorusFreq) :
    homogeneousHalfEnergy c S ≤
      ∑ k ∈ S, periodicFrequencyWeight k ^ (1/2 : ℝ) * ‖c k‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  rw [periodicAngularMagnitude, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_sqrt (by linarith)

/-- Monotonicity under enlargement of the finite spectral support. -/
theorem homogeneousHalfEnergy_mono {c : TorusFreq → ℂ}
    {S T : Finset TorusFreq} (hST : S ⊆ T) :
    homogeneousHalfEnergy c S ≤ homogeneousHalfEnergy c T := by
  classical
  unfold homogeneousHalfEnergy
  exact Finset.sum_le_sum_of_subset_of_nonneg hST
    (fun k hkS hkT => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))

end NSFormalization.Paper1
