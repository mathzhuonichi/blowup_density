/-
  Lane 144 reviewer — P7: the lane's witness travels through the registered
  Bindings bridge to the frozen contract structure.
  Run:  cd verification && lake env lean ../research/MAINT/probes/rev144_contract_bridge.lean
-/
import NSFormalization.Section4.A04.ZeroSolution
import Bindings.MaximalPartial

open NSFormalization.Section4.A04

noncomputable section

/-- `zeroSol` crosses the A02 → `Contracts.V1.Data` bridge. -/
example (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T) :
    BlowupDensity.Contracts.V1.Data.ClassicalSolutionR ν 0 0 T :=
  BlowupDensity.Bindings.maximalPartial_ofA02 (zeroSol ν T hν hT)

end
