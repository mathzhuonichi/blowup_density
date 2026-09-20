import NSFormalization.Section3.T21.MainAssembly
import Bindings.TorusMain

/-! End-to-end non-vacuity probes for T21 unit A. -/

noncomputable section

namespace NSFormalization.Section3.T21.AssemblyCloses

open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T20 (criticalRegularityT criticalSmallnessH1)
open NSFormalization.Section4.A02 (SpatialField)

/-- The index of the closed package is the actual canonical T20 constant. -/
example : criticalRegularityT.c = criticalSmallnessH1 := rfl

/-- All nine fields close at that explicit index. -/
example : Nonempty (NonDensityAPI criticalSmallnessH1) :=
  nonemptyNonDensityAPI

/-- All five main-theorem fields close. -/
example : Nonempty MainTheoremAPI :=
  nonemptyMainTheoremAPI

/-- Read off zero-datum non-density at `ν = T = s = 1`. -/
example :
    ¬ RelativelyDenseT 1 1 forceClassT (breakdownSetTZero 1 1) :=
  closedMainTheoremAPI.zeroInitialNonDensity
    1 zero_lt_one 1 zero_lt_one 1 (by norm_num)

/-- Read off fixed-initial density at the admissible zero datum, with
`ν = T = 1` and the concrete subcritical order `s = 0`. -/
example : RelativelyDenseT 1 0 forceClassT
    (breakdownSetT 1 (fun _ : Space ↦ 0) 1) :=
  closedMainTheoremAPI.fixedInitialDensity
    (fun _ : Space ↦ 0) closedMainTheoremAPI.zeroInitialClass
    1 zero_lt_one 1 zero_lt_one 0 (by norm_num)

/-- Both unconditional paper statements are available. -/
example : nonDensityStatement ∧ mainStatement :=
  ⟨nonDensityStatement_unconditional, mainStatement_holds⟩

end NSFormalization.Section3.T21.AssemblyCloses

namespace BlowupDensity.T21.RegisteredAssemblyCloses

open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V1.TorusNonDensity
open BlowupDensity.Contracts.V1.TorusMain

/-- The same critical-order specialization closes in registered vocabulary. -/
example :
    ¬ RelativelyDenseT 1 1 forceClassT (breakdownSetTZero 1 1) :=
  BlowupDensity.Bindings.TorusMain.closedMainTheoremAPI.zeroInitialNonDensity
    1 zero_lt_one 1 zero_lt_one 1 (by norm_num)

/-- The registered main paper statement is unconditional. -/
example : mainStatement :=
  BlowupDensity.Bindings.TorusMain.mainStatement_holds

end BlowupDensity.T21.RegisteredAssemblyCloses
