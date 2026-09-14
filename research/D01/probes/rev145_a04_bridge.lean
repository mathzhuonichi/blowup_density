-- REVIEW PROBE (lane 145): step (i) of the worker's A3-L1·k decomposition (the "A04 norm bridge")
-- is ALREADY in the tree — `A04.Forcing.sobolevENorm_eq` (Forcing.lean:126), with the weaker
-- `D01.sobolevENorm_le_of_isSobolevDatum` (SmoothDatum.lean:309) already enough for the ≤ half.
-- Combined with lane 145's `norm_isSobolevDatum_le_two` it gives the t-free order-2 cap directly.
-- Run: cd verification && lake env lean ../research/D01/probes/rev145_a04_bridge.lean
import NSFormalization.Section4.A04.Forcing
import NSFormalization.Section4.D01.FiniteOrderNorm

set_option autoImplicit false

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open NSFormalization.Section4.A04
open NSFormalization.Section4.A02 (SpaceTimeField)

noncomputable section

/-- The whole remaining A3-L1·k arithmetic, once the Euler side supplies `HasWeakDerivsL2Bound`:
`sobolevNormAt 2 u t ≤ 16·√M`.  Nothing here is new mathematics — it is lane 145's
`norm_isSobolevDatum_le_two` plus the existing A04 bridge. -/
theorem probe_sobolevNormAt_le (u : SpaceTimeField) (t : ℝ) (M : ℝ)
    (h : HasWeakDerivsL2Bound (fun x => u (t, x)) M 2) :
    sobolevNormAt ((2 : ℕ) : ℝ) u t ≤ 16 * Real.sqrt M := by
  obtain ⟨A, hA, _⟩ := exists_isSobolevDatum_norm_le 2 (fun x => u (t, x)) M h
  have hbridge : sobolevENorm ((2 : ℕ) : ℝ) (fun x => u (t, x)) = ‖A‖ₑ := sobolevENorm_eq hA
  have hM : (0 : ℝ) ≤ M := le_trans (sq_nonneg _) h.1.2
  have hA256 : ‖A‖ ^ 2 ≤ 256 * M :=
    norm_isSobolevDatum_le_two (fun x => u (t, x)) M h A hA
  have hle : ‖A‖ ≤ 16 * Real.sqrt M := by
    nlinarith [Real.sq_sqrt hM, Real.sqrt_nonneg M, norm_nonneg A,
      sq_nonneg (‖A‖ - 16 * Real.sqrt M)]
  rw [sobolevNormAt, hbridge]
  simpa [Real.enorm_eq_ofReal (norm_nonneg A), ENNReal.toReal_ofReal (norm_nonneg A)] using hle
