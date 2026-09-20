import NSFormalization.Section4.A02.MaximalWiring
import NSFormalization.Section4.A04.ZeroSolution

open NSFormalization.Section4
open A02

#print axioms exists_maximal'
#print axioms horizon_le_lifespan'
#print axioms maximalLifespanR_pos
#print axioms IsMaximalSolution.exists_solution_after
#print axioms ClassicalSolutionR.restart_datum
#print axioms restart_datum
#print axioms maximal_unique

example : ∃ u p, IsMaximalSolution 1 0 0 u p :=
  exists_maximal' 1 0 0 (by norm_num) A04.zero_mem_initialClassR A04.memForceR_zero

example : (fun x => (A04.zeroSol 1 1 (by norm_num) (by norm_num)).velocity (0, x))
    ∈ initialClassR :=
  (A04.zeroSol 1 1 (by norm_num) (by norm_num)).restart_datum ⟨le_rfl, by norm_num⟩
