import NSFormalization.Paper1.ScalarEnergy

/-!
Reviewer non-vacuity probe for lane 176.

The generalized scalar lemma is instantiated on the nonempty interval `[0,1]`
with nonzero constant energy `E = 4` and budget `N = 2`.  Thus its hypotheses
are jointly satisfiable away from the zero solution and its endpoint condition
is the sharp equality `sqrt 4 = 2`.
-/

open Set

example : Real.sqrt (4 : ℝ) ≤ 2 := by
  have h := NSFormalization.Paper1.sqrt_energy_le_primitive_general
    (T := (1 : ℝ))
    (E := fun _ : ℝ => 4) (E' := fun _ : ℝ => 0)
    (N := fun _ : ℝ => 2) (b := fun _ : ℝ => 0)
    (by norm_num) continuousOn_const continuousOn_const
    (by rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)])
    (by intro t ht; norm_num)
    (by intro t ht; norm_num)
    (by intro t ht; simpa using (hasDerivAt_const (x := t) (c := (4 : ℝ))))
    (by intro t ht; simpa using (hasDerivAt_const (x := t) (c := (2 : ℝ))))
    (by intro t ht; norm_num)
  exact h (1 / 2) (by constructor <;> norm_num)
