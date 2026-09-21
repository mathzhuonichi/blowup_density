import NSFormalization.Section4.A01.GronwallEndpoint
import NSFormalization.Section4.A04.ZeroSolution

noncomputable section
open Set MeasureTheory
open NSFormalization.Section4 NSFormalization.Section4.A01
open NSFormalization.Section4.A04
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerCylinderSobolev
open scoped ENNReal

#print axioms highOrder_bddAbove_of_kbnd_Ico_full
#print axioms highOrder_bddAbove_all_orders_Ico_full
#print axioms hOne_uniform_Ico_full

-- A positive horizon and concrete zero cylinder witness exercise every input.
example : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ t ∈ Ico (0 : ℝ) 1,
    D01.sobolevENorm 1 (fun x => (zeroSol 1 1 (by norm_num) (by norm_num)).velocity (t, x)) ≤ K := by
  apply hOne_uniform_Ico_full (R := 0) (q := 4) (by norm_num)
    zero_mem_initialClassR memForceR_zero (zeroSol 1 1 (by norm_num) (by norm_num))
    (path_zero 1 1 (by norm_num) (by norm_num)) (by norm_num)
    (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 (4 + 1)))
    (0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2))
  · intro θ t
    exact map_zero _
  · intro t
    exact map_zero _
  · norm_num
  · intro t
    exact (Lp.coeFn_zero _ _ _).symm
  · simp
