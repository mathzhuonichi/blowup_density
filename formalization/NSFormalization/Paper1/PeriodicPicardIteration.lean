import NSFormalization.Paper1.PeriodicPicardContraction

noncomputable section
namespace NSFormalization.Paper1

/-- Pure metric recurrence contract for Picard errors. -/
structure PicardIterationContract (e : ℕ → ℝ) (q : ℝ) : Prop where
  error_nonneg : ∀ n, 0 ≤ e n
  q_nonneg : 0 ≤ q
  q_lt_one : q < 1
  step : ∀ n, e (n + 1) ≤ q * e n

/-- Iterated errors obey the geometric bound supplied by the one-step factor. -/
theorem PicardIterationContract.geometric_bound
    {e : ℕ → ℝ} {q : ℝ} (C : PicardIterationContract e q) (n : ℕ) :
    e n ≤ q ^ n * e 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        e (Nat.succ n) = e (n + 1) := by rfl
        _ ≤ q * e n := C.step n
        _ ≤ q * (q ^ n * e 0) := by
          exact mul_le_mul_of_nonneg_left ih C.q_nonneg
        _ = q ^ (Nat.succ n) * e 0 := by
          rw [pow_succ]
          ring

end NSFormalization.Paper1
