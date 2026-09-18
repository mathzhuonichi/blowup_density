import NSFormalization.Section3.T11.PairingBound

/- Negative review probe: changing the explicit constant to zero is a substantive
   mutation of the claimed hpair statement.  The original proof term must fail. -/
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)

example :
    ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T) (m : ℕ), 3 ≤ m →
          ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ Gm Nm : PeriodicSobolev (m : ℝ),
            IsPeriodicDatum (m : ℝ) (fun x ↦ w.velocity (t, x)) Gm →
            IsPeriodicDatum (m : ℝ) (fun x ↦ convectionFieldT w.velocity (t, x)) Nm →
            |torusRealPairing Gm Nm| ≤
              (0 : ℝ) * torusSobolevNormAt 2 w.velocity t *
                torusSobolevNormAt (m : ℝ) w.velocity t *
                torusGradientNormAt (m : ℝ) w.velocity t := by
  exact torusPairingBound_classical
