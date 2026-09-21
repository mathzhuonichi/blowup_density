import NSFormalization.Section4.R43.CriticalPairing

open NSFormalization.Paper3
open scoped RealInnerProductSpace

namespace NSFormalization.Section4.R43

/- Deliberately false-strengthened proof attempt: replace the sharp Hilbert
Cauchy--Schwarz factor `1` by `1/2`.  The original proof must not typecheck. -/
example (A F : RealVectorSobolev (1 / 2)) :
    |⟪F, A⟫| ≤ (1 / 2 : ℝ) * ‖F‖ * ‖A‖ := by
  exact critical_force_pairing A F

end NSFormalization.Section4.R43
