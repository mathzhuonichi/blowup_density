import NSFormalization.Section3.T10.FourierCalculus
open NSFormalization.Section3.T10 NavierStokes.ProblemStatement
open scoped ContDiff BigOperators

example (c : ℂ) : Summable (periodicFourierCoeff (fun _ : Space ↦ c)) :=
  summable_periodicFourierCoeff_of_smooth (fun _ _ ↦ rfl) contDiff_const

example (k : PeriodicFrequency) :
    IsPeriodicSpatial (fun x : Space ↦ Complex.exp
      ((2 * Real.pi * Complex.I : ℂ) * ∑ i, (k i : ℂ) * (x i : ℂ))) ∧
    ContDiff ℝ ∞ (fun x : Space ↦ Complex.exp
      ((2 * Real.pi * Complex.I : ℂ) * ∑ i, (k i : ℂ) * (x i : ℂ))) := by
  have he : (fun x : Space ↦ Complex.exp
      ((2 * Real.pi * Complex.I : ℂ) * ∑ i, (k i : ℂ) * (x i : ℂ))) =
      NSFormalization.Paper1.periodicCharacter k := by
    funext x
    simp only [NSFormalization.Paper1.periodicCharacter,
      NSFormalization.Paper1.periodicPhase_apply]
  rw [he]
  exact ⟨NSFormalization.Paper1.periodicCharacter_periodic k,
    NSFormalization.Paper1.periodicCharacter_smooth k⟩

example (k : PeriodicFrequency) :
    Summable (periodicFourierCoeff (NSFormalization.Paper1.periodicCharacter k)) :=
  summable_periodicFourierCoeff_of_smooth
    (NSFormalization.Paper1.periodicCharacter_periodic k)
    (NSFormalization.Paper1.periodicCharacter_smooth k)

example (k : PeriodicFrequency) (x : Space) :
    NSFormalization.Paper1.periodicCharacter k x =
      ∑' l, periodicFourierCoeff (NSFormalization.Paper1.periodicCharacter k) l *
        Complex.exp ((2 * Real.pi * Complex.I : ℂ) * ∑ i, (l i : ℂ) * (x i : ℂ)) :=
  periodic_eq_tsum_mFourier (NSFormalization.Paper1.periodicCharacter_periodic k)
    (NSFormalization.Paper1.periodicCharacter_smooth k).continuous
    (summable_periodicFourierCoeff_of_smooth
      (NSFormalization.Paper1.periodicCharacter_periodic k)
      (NSFormalization.Paper1.periodicCharacter_smooth k)) x
