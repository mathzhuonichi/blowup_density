import NSFormalization.Paper1.PeriodicMildWitnessAdapter

noncomputable section
namespace NSFormalization.Paper1

/-- Extract the fixed-point equation from a packaged mild witness. -/
theorem MildPicardFixedPointWitness.fixed_point
    {E : Type*} [NormedAddCommGroup E]
    (W : MildPicardFixedPointWitness E) : W.map W.trajectory = W.trajectory := W.fixed

/-- The residual of a packaged mild witness vanishes. -/
theorem MildPicardFixedPointWitness.residual_zero
    {E : Type*} [NormedAddCommGroup E]
    (W : MildPicardFixedPointWitness E) : W.map W.trajectory - W.trajectory = 0 := by
  rw [W.fixed]
  exact sub_self _

end NSFormalization.Paper1
