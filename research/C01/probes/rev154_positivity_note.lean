import NSFormalization.Section4.C01.EnergyBounds
/-! REVIEW PROBE (lane 154): honesty check on the ATTEMPTS bullet
"`by positivity` on `0 < 2·√(E x + δ²)` fails without `hs` in context".
First example: no `hs` — expected to FAIL.  Second: with `hs` — expected to succeed. -/
example (E : ℝ → ℝ) (x δ : ℝ) : 0 < 2 * Real.sqrt (E x + δ ^ 2) := by positivity
example (E : ℝ → ℝ) (x δ : ℝ) (hs : 0 < Real.sqrt (E x + δ ^ 2)) :
    0 < 2 * Real.sqrt (E x + δ ^ 2) := by positivity
