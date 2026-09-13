import NSFormalization.Paper1.PeriodicFiniteMode
import Mathlib.Analysis.Real.Sqrt
noncomputable section
namespace NSFormalization.Paper1
open scoped BigOperators ComplexConjugate

def finiteWeightedPairing (c d : TorusFreq → ℂ) (S : Finset TorusFreq) : ℂ :=
  ∑ k ∈ S, (periodicAngularMagnitude k : ℂ) * c k * conj (d k)

theorem norm_finiteWeightedPairing_le (c d : TorusFreq → ℂ) (S : Finset TorusFreq) :
    ‖finiteWeightedPairing c d S‖ ≤
      Real.sqrt (homogeneousHalfEnergy c S) * Real.sqrt (homogeneousHalfEnergy d S) := by
  unfold finiteWeightedPairing
  calc
    ‖∑ k ∈ S, (periodicAngularMagnitude k : ℂ) * c k * conj (d k)‖ ≤
        ∑ k ∈ S, periodicAngularMagnitude k * ‖c k‖ * ‖d k‖ := by
          calc
            ‖∑ k ∈ S, (periodicAngularMagnitude k : ℂ) * c k * conj (d k)‖ ≤
                ∑ k ∈ S, ‖(periodicAngularMagnitude k : ℂ) * c k * conj (d k)‖ :=
              norm_sum_le S _
            _ = ∑ k ∈ S, periodicAngularMagnitude k * ‖c k‖ * ‖d k‖ := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (by unfold periodicAngularMagnitude; positivity),
                starRingEnd_apply, norm_star]
    _ ≤ Real.sqrt (∑ k ∈ S, (Real.sqrt (periodicAngularMagnitude k) * ‖c k‖)^2) *
        Real.sqrt (∑ k ∈ S, (Real.sqrt (periodicAngularMagnitude k) * ‖d k‖)^2) := by
          calc
            _ = ∑ k ∈ S, (Real.sqrt (periodicAngularMagnitude k) * ‖c k‖) *
                (Real.sqrt (periodicAngularMagnitude k) * ‖d k‖) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hw : 0 ≤ periodicAngularMagnitude k := by
                unfold periodicAngularMagnitude
                exact Real.sqrt_nonneg _
              calc
                periodicAngularMagnitude k * ‖c k‖ * ‖d k‖ =
                    (Real.sqrt (periodicAngularMagnitude k)) ^ 2 *
                      (‖c k‖ * ‖d k‖) := by
                        rw [Real.sq_sqrt hw]
                        ring
                _ = (Real.sqrt (periodicAngularMagnitude k) * ‖c k‖) *
                    (Real.sqrt (periodicAngularMagnitude k) * ‖d k‖) := by
                  ring
            _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt S
              (fun k => Real.sqrt (periodicAngularMagnitude k) * ‖c k‖)
              (fun k => Real.sqrt (periodicAngularMagnitude k) * ‖d k‖)
    _ = _ := by
      congr 1
      · apply congrArg Real.sqrt
        apply Finset.sum_congr rfl
        intro k hk
        have hw : 0 ≤ periodicAngularMagnitude k := by
          unfold periodicAngularMagnitude
          exact Real.sqrt_nonneg _
        calc
          (Real.sqrt (periodicAngularMagnitude k) * ‖c k‖) ^ 2 =
              (Real.sqrt (periodicAngularMagnitude k)) ^ 2 * ‖c k‖ ^ 2 := by ring
          _ = periodicAngularMagnitude k * ‖c k‖ ^ 2 := by rw [Real.sq_sqrt hw]
      · apply congrArg Real.sqrt
        apply Finset.sum_congr rfl
        intro k hk
        have hw : 0 ≤ periodicAngularMagnitude k := by
          unfold periodicAngularMagnitude
          exact Real.sqrt_nonneg _
        calc
          (Real.sqrt (periodicAngularMagnitude k) * ‖d k‖) ^ 2 =
              (Real.sqrt (periodicAngularMagnitude k)) ^ 2 * ‖d k‖ ^ 2 := by ring
          _ = periodicAngularMagnitude k * ‖d k‖ ^ 2 := by rw [Real.sq_sqrt hw]
end NSFormalization.Paper1
