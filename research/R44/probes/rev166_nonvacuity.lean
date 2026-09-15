import NSFormalization.Section4.R44.Pieces

open Set intervalIntegral MeasureTheory
open NSFormalization.Section4.R44

/- A nonzero instance of the scalar bootstrap: on `[0,1]`, take
   `Y(t) = t/2`, `B(t) = 1`, `nu = 2`, and `R = 1`. -/
example : ∀ t ∈ Icc (0 : ℝ) 1, (fun s : ℝ => s / 2) t ≤ (1 : ℝ) * 2 / 2 := by
  apply criticalSquaredNormBound_radius
    (T := 1) (nu := 2) (theta := 1) (C₂ := 0) (C₃ := 1) (R := 1)
    (Y := fun s => s / 2) (E' := fun s => s / 2)
    (Z := fun _ => 0) (B := fun _ => 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num [Real.exp_zero]
  · fun_prop
  · norm_num
  · intro t ht
    linarith [ht.1]
  · fun_prop
  · intro t ht
    simp
    linarith [ht.2]
  · intro t ht
    have h := ((hasDerivAt_id t).div_const (2 : ℝ)).pow 2
    have h' : HasDerivAt ((fun x : ℝ => id x / 2) ^ 2) (t / 2) t :=
      h.congr_deriv (by norm_num [id_eq]; ring)
    exact h'.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ => rfl))
  · exact (continuous_id.div_const 2).intervalIntegrable 0 1
  · intro t ht hbootstrap
    norm_num
    linarith [ht.2]
