import NSFormalization.Section3.T21.Main

noncomputable section

namespace NSFormalization.Section3.T21.Rev474Nonvacuity

open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T19 (periodicDensityAPI)
open NSFormalization.Section3.T21

/-- A closed, concrete subcritical instance: viscosity and horizon are one,
the initial datum is zero, and the Sobolev order is zero. -/
example :
    RelativelyDenseT 1 0 forceClassT
      (breakdownSetT 1 (fun _ : Space ↦ 0) 1) := by
  exact fixedInitialDensity periodicDensityAPI
    (fun _ : Space ↦ 0) zeroInitialClass
    1 (by norm_num) 1 (by norm_num) 0 (by norm_num)

end NSFormalization.Section3.T21.Rev474Nonvacuity
