import NSFormalization.Paper1.PeriodicPicardIteration
import NSFormalization.Paper1.PeriodicPicardDuhamelLipschitz

noncomputable section
namespace NSFormalization.Paper1

/-- Explicit recurrence obtained when each Picard error step is bounded by a
Duhamel gain and that gain is compared to `q` times the previous error. -/
theorem picard_duhamel_iteration_geometric
    {e : ℕ → ℝ} {q : ℝ} (hE : ∀ n, 0 ≤ e n)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hstep : ∀ n, e (n + 1) ≤ q * e n) (n : ℕ) :
    e n ≤ q ^ n * e 0 := by
  let C : PicardIterationContract e q :=
    { error_nonneg := hE
      q_nonneg := hq0
      q_lt_one := hq1
      step := hstep }
  exact C.geometric_bound n

/-- A Duhamel time-gain contract supplies the scalar step bound needed by the
metric recurrence; the carrier-level estimate is intentionally explicit. -/
theorem picard_duhamel_step_to_geometric
    {e : ℕ → ℝ} {q : ℝ} (hE : ∀ n, 0 ≤ e n)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hgain : ∀ n, e (n + 1) ≤ q * e n) (n : ℕ) :
    e n ≤ q ^ n * e 0 :=
  picard_duhamel_iteration_geometric hE hq0 hq1 hgain n

end NSFormalization.Paper1
