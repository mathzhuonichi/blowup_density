import NSFormalization.Paper1.CriticalBootstrapInterface

/-!
# Auxiliary scalar energy inequalities

Stable wrappers around the proved real-variable lemmas in `ScalarEnergy`.
No PDE, pressure, flow, or lifespan object is introduced here.
-/
namespace NSFormalization.Paper1

/-- Absorb the critical nonlinear coefficient while retaining dissipation. -/
theorem absorbed_energy_inequality {ν C y z b E' : ℝ}
    (hsmall : C * y ≤ ν / 2)
    (henergy : E' / 2 + (ν - C * y) * z ^ 2 ≤ b * y) :
    E' / 2 + (ν / 2) * z ^ 2 ≤ b * y := by
  exact critical_energy_absorption hsmall henergy

/-- Dropping the nonnegative dissipation term gives a squared-norm derivative bound. -/
theorem derivative_bound_of_absorbed_energy {ν y z b E' : ℝ}
    (hν : 0 ≤ ν)
    (habsorbed : E' / 2 + (ν / 2) * z ^ 2 ≤ b * y) :
    E' ≤ 2 * b * y := by
  exact critical_squared_derivative_bound hν habsorbed

end NSFormalization.Paper1
