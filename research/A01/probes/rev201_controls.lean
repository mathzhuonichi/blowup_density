import NSFormalization.Section4.A01.RootComparison
namespace NSFormalization.Section4.A01
example : (1 : ℝ)*1+1*1^2 ≤ 2*1*1+0*1 ∧ ¬ ((1 : ℝ) ≤ 2^2/(8*1)*1+0) := by norm_num
example (q : ℕ) : mildNormConstant q ≤ max 1 (mildNormConstant q) := le_max_right _ _
example : (1 : ℝ) ≤ energyComparison (fun _ => 0) 1 0 1 := by
  have h := energyComparison_unique_on_Icc (α := fun _ => 0) (b := 1) (c := 0) (T := 1) (by norm_num) continuous_const
    continuous_id.continuousOn rfl (fun s _ => by simpa using hasDerivAt_id s) 1 (by constructor <;> norm_num)
  exact h.le
end NSFormalization.Section4.A01
