import NSFormalization.Paper1.PeriodicForcedDuhamel
noncomputable section
namespace NSFormalization.Paper1.PeriodicForcedDuhamel
open Set MeasureTheory
open NSFormalization.Paper1.PeriodicHeatMultiplier
 theorem norm_duhamel_le_mul_of_norm_le
    {ν t M : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) {G : ℝ → FourierHilbert}
    (_hG : IntervalIntegrable (fun τ => heat hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ)) volume 0 t)
    (hbound : ∀ τ ∈ Icc (0 : ℝ) t, ‖G τ‖ ≤ M) : ‖duhamel ν hν t G‖ ≤ t * M := by
  have hpoint : ∀ τ ∈ uIoc (0 : ℝ) t, ‖heat hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ)‖ ≤ M := by
    intro τ hτ
    have hτ' : τ ∈ Icc (0 : ℝ) t := by
      have hh : 0 < τ ∧ τ ≤ t := by simpa [uIoc, ht] using hτ
      exact ⟨le_of_lt hh.1, hh.2⟩
    exact (norm_heat_le hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ)).trans (hbound τ hτ')
  have hraw := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  simpa [duhamel, abs_of_nonneg ht, mul_comm, mul_left_comm, mul_assoc] using hraw

theorem norm_duhamel_sub_le_mul_of_norm_sub_le
    {ν t D : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) {G H : ℝ → FourierHilbert}
    (hG : IntervalIntegrable (fun τ => heat hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ)) volume 0 t)
    (hH : IntervalIntegrable (fun τ => heat hν (show 0 ≤ max (t - τ) 0 by positivity) (H τ)) volume 0 t)
    (hbound : ∀ τ ∈ Icc (0 : ℝ) t, ‖G τ - H τ‖ ≤ D) : ‖duhamel ν hν t G - duhamel ν hν t H‖ ≤ t * D := by
  have hdiff : duhamel ν hν t G - duhamel ν hν t H = duhamel ν hν t (fun τ => G τ - H τ) := by
    unfold duhamel
    have hfun : (fun τ => heat hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ - H τ)) =
        (fun τ => heat hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ) -
          heat hν (show 0 ≤ max (t - τ) 0 by positivity) (H τ)) := by
      funext τ
      exact (heatCLM hν (show 0 ≤ max (t - τ) 0 by positivity)).map_sub (G τ) (H τ)
    rw [hfun]
    exact (intervalIntegral.integral_sub hG hH).symm
  rw [hdiff]
  have hpoint : ∀ τ ∈ uIoc (0 : ℝ) t, ‖heat hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ - H τ)‖ ≤ D := by
    intro τ hτ
    have hτ' : τ ∈ Icc (0 : ℝ) t := by
      have hh : 0 < τ ∧ τ ≤ t := by simpa [uIoc, ht] using hτ
      exact ⟨le_of_lt hh.1, hh.2⟩
    exact (norm_heat_le hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ - H τ)).trans (hbound τ hτ')
  have hraw := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  simpa [duhamel, abs_of_nonneg ht, mul_comm, mul_left_comm, mul_assoc] using hraw
end NSFormalization.Paper1.PeriodicForcedDuhamel
