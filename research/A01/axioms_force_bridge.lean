import NSFormalization.Section4.A01.ForceBridge

/-! Transitive-axiom audit and concrete non-vacuity for lane 167-A01-force-bridge. -/

open NSFormalization.Section4.A01

#print axioms forceOfPath
#print axioms forceOfPath_apply
#print axioms forceOfPath_forcePath_eq_on_horizon
#print axioms forcePath_of_memForceR
#print axioms initialClassR_of_smoothL2

open Set Metric MeasureTheory NavierStokes.ProblemStatement
open EulerLpTranslation EulerLpTranslation.SmoothL2Field
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity
open scoped ContDiff

noncomputable section
set_option autoImplicit false

namespace NSFormalization.Section4.A01

/-! A concrete nonzero member of `F_R`, so the consumer bridge is tested beyond the zero force. -/

private def tb : ContDiffBump (2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
private def xb : ContDiffBump (0 : Space) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

private def endpointBump : A02.SpaceTimeField :=
  fun p => (tb p.1 * xb p.2) • (EuclideanSpace.single 0 1 : Space)

private def endpointBumpSupport : Set SpaceTime :=
  closedBall (2 : ℝ) 1 ×ˢ closedBall (0 : Space) 1

private theorem endpointBump_zero_outside :
    ∀ p ∉ endpointBumpSupport, endpointBump p = 0 := by
  intro p hp
  have hz : tb p.1 * xb p.2 = 0 := by
    by_cases h1 : p.1 ∈ closedBall (2 : ℝ) 1
    · have h2 : p.2 ∉ closedBall (0 : Space) 1 := fun h => hp ⟨h1, h⟩
      have hd : (1 : ℝ) ≤ dist p.2 0 := le_of_lt (by simpa [mem_closedBall] using h2)
      rw [show xb p.2 = 0 from xb.zero_of_le_dist hd, mul_zero]
    · have hd : (1 : ℝ) ≤ dist p.1 2 := le_of_lt (by simpa [mem_closedBall] using h1)
      rw [show tb p.1 = 0 from tb.zero_of_le_dist hd, zero_mul]
  rw [endpointBump, hz, zero_smul]

private theorem endpointBump_compact : D01.MemForceCompact endpointBump := by
  have hKc : IsCompact endpointBumpSupport :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hKcl : IsClosed endpointBumpSupport := isClosed_closedBall.prod isClosed_closedBall
  refine ⟨?_, HasCompactSupport.intro hKc endpointBump_zero_outside, ?_⟩
  · exact (((tb.contDiff (n := (⊤ : ℕ∞))).comp contDiff_fst).mul
      ((xb.contDiff (n := (⊤ : ℕ∞))).comp contDiff_snd)).smul contDiff_const
  · refine (closure_minimal
      (Function.support_subset_iff'.2 endpointBump_zero_outside) hKcl).trans ?_
    rintro ⟨t, y⟩ ⟨ht, -⟩
    refine ⟨?_, mem_univ y⟩
    have hb : |t - 2| ≤ 1 := by simpa [Real.dist_eq] using ht
    obtain ⟨ha, -⟩ := abs_le.mp hb
    simpa only [mem_Ioi] using (show 0 < t by linarith)

private theorem endpointBump_memForceR : D01.MemForceR endpointBump :=
  D01.memForceR_of_memForceCompact endpointBump_compact

private theorem endpointBump_ne_zero : endpointBump (2, 0) ≠ 0 := by
  have h1 : tb (2 : ℝ) = 1 := tb.one_of_mem_closedBall (by norm_num [tb, mem_closedBall])
  have h2 : xb (0 : Space) = 1 := xb.one_of_mem_closedBall (by norm_num [xb, mem_closedBall])
  rw [endpointBump, h1, h2, one_mul, one_smul]
  intro h
  have hcoord := congrFun (congrArg (fun v : Space => (v : Fin 3 → ℝ)) h) 0
  simp at hcoord

/-! The canonical carrier package exists for the nonzero force and keeps the original force in
`MemL1Hm`; the on-horizon field identity is nontrivial at the right endpoint. -/
example :
    ∃ F : Icc (0 : ℝ) 2 → SmoothL2Field Space,
      F = C01.forcePath endpointBump_memForceR ∧
      (∀ n, Continuous fun t => (F t).jetLp n) ∧
      A04.MemL1Hm endpointBump :=
  forcePath_of_memForceR endpointBump_memForceR

example :
    forceOfPath (C01.forcePath (S := (2 : ℝ)) endpointBump_memForceR) (2, 0) =
      endpointBump (2, 0) ∧ endpointBump (2, 0) ≠ 0 := by
  exact ⟨forceOfPath_forcePath_eq_on_horizon endpointBump_memForceR
    ⟨2, by norm_num, by norm_num⟩ 0, endpointBump_ne_zero⟩

/-! The initial-datum theorem is inhabited by the zero cylinder slice, with every lane-162
handoff hypothesis supplied explicitly. -/
example : (zeroField : SmoothL2Field Space).field ∈ A02.initialClassR := by
  apply initialClassR_of_smoothL2 (q := 0)
    (u := (0 : SobolevSpace 1 (0 + 1)))
    (U := (0 : EulerMeanSolenoidal.L2))
  · intro θ
    simp
  · change ordinaryLift 0 = valueOperator 1 1 0
    rw [map_zero, map_zero]
  · rw [show value 1 (0 : SobolevSpace 1 1) = 0 from map_zero (valueOperator 1 1)]
    exact Submodule.zero_mem _
  · exact (Lp.coeFn_zero Space 2 volume).symm

end NSFormalization.Section4.A01
