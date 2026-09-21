import NSFormalization.Section3.T10.Leray

noncomputable section

namespace NSFormalization.Section3.T10

/- Reviewer mutation: replace the sharp contraction constant `1` by `1 / 2`.
The lane theorem must not close this strictly stronger statement. -/
example :
    ∀ (s : ℝ) (A : PeriodicSobolev s),
      ∃ B : PeriodicSobolev s,
        IsPeriodicLerayDatum A B ∧
          ‖B‖ ≤ ((1 : ℝ) / 2) * ‖A‖ ∧ IsSolenoidalPeriodicDatum B :=
  leray_exists_contraction

end NSFormalization.Section3.T10
