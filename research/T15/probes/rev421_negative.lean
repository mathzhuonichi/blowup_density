import NSFormalization.Section3.T15.SingleCopy
namespace NSFormalization.Section3.T15
open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open scoped BigOperators
example {V : Type*} [NormedAddCommGroup V] {g : Space → V}
    (hsupp : tsupport g ⊆ interior fundamentalCube)
    {x : Space} (hx : x ∈ fundamentalCube) :
    (∑' n : PeriodicFrequency, g (x - latticeVector n)) = g x + g x := by
  exact tsum_eq_single_copy_of_mem_cube hsupp hx
end NSFormalization.Section3.T15
