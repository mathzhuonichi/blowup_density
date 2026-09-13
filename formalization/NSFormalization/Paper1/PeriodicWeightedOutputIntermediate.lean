import NSFormalization.Paper1.PeriodicWeightedOutputSquare
noncomputable section
namespace NSFormalization.Paper1.PeriodicWeightedCoeffBound
open PeriodicPicardBilinear
open scoped BigOperators
 theorem weighted_output_intermediate_le (r : ℕ) (f g : FiniteFourier) (K : Finset PeriodicFrequency) :
    (∑ n ∈ K, periodicFrequencyWeight n ^ r * ‖convolutionCoeff f g n‖ ^ 2) ≤
      ∑ n ∈ K, (2 : ℝ)^r * (∑ l ∈ f.support, Real.sqrt (periodicFrequencyWeight l ^ r) * ‖f l‖) *
        ∑ l ∈ f.support, (Real.sqrt (periodicFrequencyWeight l ^ r) * ‖f l‖) *
          (Real.sqrt (periodicFrequencyWeight (n-l) ^ r) * ‖g (n-l)‖)^2 := by
  apply Finset.sum_le_sum
  intro n hn
  exact weighted_convolutionCoeff_sq_le r f g n
end NSFormalization.Paper1.PeriodicWeightedCoeffBound
