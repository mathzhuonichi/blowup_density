import NSFormalization.Paper1.PeriodicCrossComponentTransport

noncomputable section
namespace NSFormalization.Paper1.PeriodicCrossComponentTransport

open NSFormalization.Paper1.PeriodicFiniteVectorBound
open NSFormalization.Paper1.PeriodicLerayCoeffCore
open NSFormalization.Paper1.PeriodicPicardBilinear
open NSFormalization.Paper1.PeriodicHeatMultiplier
open scoped BigOperators

/-- Fourier coefficient obtained by applying the `j`-th derivative symbol to
the `i`-th component of the second vector. -/
def derivativeMul (v : FiniteVector) (j i : Fin 3) :
    NSFormalization.Paper1.PeriodicPicardBilinear.FiniteFourier :=
  Finsupp.onFinset (v i).support (fun m => derivativeSymbol j m * v i m) (by
    intro m hm
    have hv : (v i) m ≠ 0 := by
      intro hz
      simp [hz] at hm
    exact (Finsupp.mem_support_iff.mpr hv))

def transportCoeffConv (u v : FiniteVector) (i : Fin 3) (k : PeriodicFrequency) : ℂ :=
  ∑ j : Fin 3, convolutionCoeff (u j) (derivativeMul v j i) k

@[simp] theorem derivativeMul_zero (v : FiniteVector) (j i : Fin 3) :
    derivativeMul v j i 0 = 0 := by
  simp [derivativeMul, derivativeSymbol]

@[simp] theorem derivativeMul_add (v z : FiniteVector) (j i : Fin 3) :
    derivativeMul (v + z) j i = derivativeMul v j i + derivativeMul z j i := by
  ext m
  simp [derivativeMul, mul_add]

theorem transportCoeffConv_eq_transportCoeff (u v : FiniteVector) (i : Fin 3)
    (k : PeriodicFrequency) :
    transportCoeffConv u v i k = transportCoeff u v i k := by
  classical
  unfold transportCoeffConv transportCoeff
  apply Finset.sum_congr rfl
  intro j hj
  rw [convolutionCoeff_eq_sum_support]
  apply Finset.sum_congr rfl
  intro l hl
  simp [derivativeMul]
  ring

theorem transportCoeffConv_explicit (u v : FiniteVector) (i : Fin 3)
    (k : PeriodicFrequency) :
    transportCoeffConv u v i k =
      ∑ j : Fin 3, ∑ l ∈ (u j).support,
        (u j l) * derivativeSymbol j (k - l) * (v i (k - l)) := by
  exact transportCoeffConv_eq_transportCoeff u v i k

theorem transportCoeffConv_add_left (u w v : FiniteVector) (i : Fin 3)
    (k : PeriodicFrequency) :
    transportCoeffConv (u + w) v i k =
      transportCoeffConv u v i k + transportCoeffConv w v i k := by
  classical
  unfold transportCoeffConv
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact convolutionCoeff_add_left (u j) (w j) (derivativeMul v j i) k

theorem transportCoeffConv_add_right (u v z : FiniteVector) (i : Fin 3)
    (k : PeriodicFrequency) :
    transportCoeffConv u (v + z) i k =
      transportCoeffConv u v i k + transportCoeffConv u z i k := by
  classical
  unfold transportCoeffConv
  simp_rw [derivativeMul_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact convolutionCoeff_add_right (u j) (derivativeMul v j i)
    (derivativeMul z j i) k

theorem transportCoeffConv_norm_aggregate_le (u v : FiniteVector)
    (k : PeriodicFrequency) :
    ∑ i : Fin 3, ‖transportCoeffConv u v i k‖ ≤
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l ∈ (u j).support,
        ‖u j l‖ * ‖derivativeSymbol j (k - l)‖ * ‖v i (k - l)‖ := by
  apply Finset.sum_le_sum
  intro i hi
  rw [transportCoeffConv_eq_transportCoeff]
  exact norm_transportCoeff_le u v i k

theorem heat_transportCoeffConv_norm_aggregate_le (ν t : ℝ)
    (u v : FiniteVector) (k : PeriodicFrequency) :
    ∑ i : Fin 3, ‖(heatSymbol ν t k : ℂ) * transportCoeffConv u v i k‖ ≤
      heatSymbol ν t k *
        (∑ i : Fin 3, ∑ j : Fin 3, ∑ l ∈ (u j).support,
          ‖u j l‖ * ‖derivativeSymbol j (k - l)‖ * ‖v i (k - l)‖) := by
  simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (heatSymbol_nonneg ν t k)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [transportCoeffConv_eq_transportCoeff]
  exact mul_le_mul_of_nonneg_left (norm_transportCoeff_le u v i k)
    (heatSymbol_nonneg ν t k)

end NSFormalization.Paper1.PeriodicCrossComponentTransport
