import NSFormalization.Paper1.PeriodicPicardIteration

noncomputable section
namespace NSFormalization.Paper1

open Set

/-- Geometric error bound for an explicitly iterated contractive Picard orbit. -/
theorem PicardContractionContract.iterate_error_bound
    {E : Type*} [NormedAddCommGroup E]
    (C : PicardContractionContract E) (x : ℕ → E) (xstar : E)
    (hx0 : x 0 ∈ C.ball) (hxstar : xstar ∈ C.ball)
    (horbit : ∀ n, x (n + 1) = C.map (x n))
    (hfix : C.map xstar = xstar) (n : ℕ) :
    ‖x n - xstar‖ ≤ C.q ^ n * ‖x 0 - xstar‖ := by
  have hxball : ∀ n, x n ∈ C.ball := by
    intro n
    induction n with
    | zero => exact hx0
    | succ n ih =>
        rw [horbit n]
        exact C.self_map _ ih
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        ‖x (Nat.succ n) - xstar‖ = ‖C.map (x n) - C.map xstar‖ := by
          rw [show Nat.succ n = n + 1 by omega, horbit n, hfix]
        _ ≤ C.q * ‖x n - xstar‖ := C.lipschitz_on (hxball n) hxstar
        _ ≤ C.q * (C.q ^ n * ‖x 0 - xstar‖) := by
          exact mul_le_mul_of_nonneg_left ih C.q_nonneg
        _ = C.q ^ (Nat.succ n) * ‖x 0 - xstar‖ := by
          rw [pow_succ]
          ring

end NSFormalization.Paper1
