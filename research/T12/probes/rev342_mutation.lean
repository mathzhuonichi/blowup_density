import NSFormalization.Section3.T12.TameProduct

/- A substantive negative probe: weakening the order guard from `2 ≤ m` to
   `1 ≤ m` must not let the delivered proof close the altered statement. -/

noncomputable section

namespace NSFormalization.Section3.T12

open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open scoped ENNReal

example :
    ∀ m : ℕ, 1 ≤ m → ∀ a b : Space → ℝ,
      MemPeriodicHmScalar m a → MemPeriodicHmScalar m b →
        periodicScalarSobolevENorm (m : ℝ) (fun x ↦ a x * b x) ≤
          ENNReal.ofReal (tameProductConst m) *
            (periodicScalarSobolevENorm 2 a * periodicScalarSobolevENorm (m : ℝ) b +
              periodicScalarSobolevENorm 2 b * periodicScalarSobolevENorm (m : ℝ) a) := by
  exact tameProduct

end NSFormalization.Section3.T12
