import NSFormalization.Section3.T10.Leray

noncomputable section

namespace NSFormalization.Section3.T10

example :
    ∀ (s : ℝ) (A : PeriodicSobolev s),
      ∃ B : PeriodicSobolev s,
        IsPeriodicLerayDatum A B ∧ ‖B‖ ≤ ‖A‖ ∧ IsSolenoidalPeriodicDatum B :=
  leray_exists_contraction

example :
    ∀ (s : ℝ) (A B C : PeriodicSobolev s),
      IsPeriodicLerayDatum A B → IsPeriodicLerayDatum B C → C = B :=
  leray_projector

example :
    ∀ (s : ℝ) (A B : PeriodicSobolev s), IsSolenoidalPeriodicDatum A →
      IsPeriodicLerayDatum A B → B = A := by
  intro s A B hsol hAB
  apply Subtype.ext
  apply PiLp.ext
  intro i
  apply lp.ext
  funext k
  rw [hAB i k]
  exact periodicLeray_of_solenoidal A hsol i k

end NSFormalization.Section3.T10
