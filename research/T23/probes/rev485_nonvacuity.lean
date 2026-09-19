import NSFormalization.Section3.T23.Rates

noncomputable section
namespace Rev485Nonvacuity

open Set
open NSFormalization.Section3.T23

/-- The scale interval used by every rate field is inhabited. -/
example : (1 / 2 : ℝ) ∈ Ioc (0 : ℝ) 1 := by
  constructor <;> norm_num

/-- The chosen force-rate constant is genuinely positive even for zero suppliers. -/
example : forceDiffSobolevConst (fun _ => 0) (fun _ => 0) 0 = 1 := by
  norm_num [forceDiffSobolevConst]

/-- A positive correction constant is not erased by `energyConst`. -/
example : energyConst 2 = 2 := by
  norm_num [energyConst]

end Rev485Nonvacuity
