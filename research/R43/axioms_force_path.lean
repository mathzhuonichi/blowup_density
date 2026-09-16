import NSFormalization.Section4.R43.ForcePath

open Set Metric MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Homogeneous
open NSFormalization.Section4.R43
open scoped ContDiff

#print axioms NSFormalization.Section4.R43.ofSobolevVector_norm_le
#print axioms NSFormalization.Section4.R43.isHomogeneousPath_of_isSobolevPath
#print axioms NSFormalization.Section4.R43.forceHomogeneousENorm_le_forceSobolevENormL1
#print axioms NSFormalization.Section4.R43.forceHomogeneousENorm_one_half_ne_top
#print axioms NSFormalization.Section4.R43.criticalForceHalf_eq_of_orderOnePath
#print axioms NSFormalization.Section4.R43.criticalForceHalf_continuousOn
#print axioms NSFormalization.Section4.R43.criticalForceHalf_isHomogeneousPath
#print axioms NSFormalization.Section4.R43.criticalForceHalf_memLp_one
#print axioms NSFormalization.Section4.R43.criticalForceHalf_aestronglyMeasurable
#print axioms NSFormalization.Section4.R43.criticalForceAt_eq_norm_criticalForceHalf
#print axioms NSFormalization.Section4.R43.criticalForceAt_continuousOn_future
#print axioms NSFormalization.Section4.R43.criticalForceAt_continuousOn
#print axioms NSFormalization.Section4.R43.criticalForceAt_continuousOn_Ico
#print axioms NSFormalization.Section4.R43.criticalForceAt_nonneg
#print axioms NSFormalization.Section4.R43.criticalForceAt_intervalIntegrable
#print axioms NSFormalization.Section4.R43.criticalForcePrimitive
#print axioms NSFormalization.Section4.R43.criticalForcePrimitive_continuousOn
#print axioms NSFormalization.Section4.R43.criticalForcePrimitive_hasDerivAt
#print axioms NSFormalization.Section4.R43.criticalForcePrimitive_zero
#print axioms NSFormalization.Section4.R43.criticalForcePrimitive_monotoneOn
#print axioms NSFormalization.Section4.R43.criticalForcePrimitive_le_forceHomogeneousENorm
#print axioms NSFormalization.Section4.R43.criticalForcePrimitive_le_forceSobolevENormL1
#print axioms NSFormalization.Section4.R43.zero_dotHomogeneousENorm_half
#print axioms NSFormalization.Section4.R43.zero_mem_initialClassR
#print axioms NSFormalization.Section4.R43.critical_bootstrap_zero_datum

/-! The zero force exercises the path, FTC, and G3 statements. -/
example :
    forceHomogeneousENorm 1 (1 / 2)
        (0 : NSFormalization.Section4.A02.SpaceTimeField) ≠ ⊤ ∧
      criticalForcePrimitive (0 : NSFormalization.Section4.A02.SpaceTimeField) 0 = 0 := by
  exact ⟨forceHomogeneousENorm_one_half_ne_top
    NSFormalization.Section4.A04.memForceR_zero, criticalForcePrimitive_zero 0⟩

/-! A concrete nonzero compactly supported smooth force exercises `MemForceR`.
This is the established bump witness from `research/A01/probes/memForceR_bump_witness.lean`. -/
example : ∃ f : NSFormalization.Section4.A02.SpaceTimeField,
    NSFormalization.Section4.D01.MemForceR f ∧ f ≠ 0 := by
  let tb : ContDiffBump (2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let xb : ContDiffBump (0 : Space) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let F : NSFormalization.Section4.A02.SpaceTimeField :=
    fun p => (tb p.1 * xb p.2) • (EuclideanSpace.single 0 1 : Space)
  let K : Set SpaceTime := closedBall (2 : ℝ) 1 ×ˢ closedBall (0 : Space) 1
  have hzero : ∀ p ∉ K, F p = 0 := by
    intro p hp
    have hz : tb p.1 * xb p.2 = 0 := by
      by_cases h1 : p.1 ∈ closedBall (2 : ℝ) 1
      · have h2 : p.2 ∉ closedBall (0 : Space) 1 := fun h => hp ⟨h1, h⟩
        have hd : (1 : ℝ) ≤ dist p.2 0 :=
          le_of_lt (by simpa [mem_closedBall] using h2)
        rw [show xb p.2 = 0 from xb.zero_of_le_dist hd, mul_zero]
      · have hd : (1 : ℝ) ≤ dist p.1 2 :=
          le_of_lt (by simpa [mem_closedBall] using h1)
        rw [show tb p.1 = 0 from tb.zero_of_le_dist hd, zero_mul]
    change (tb p.1 * xb p.2) • (EuclideanSpace.single 0 1 : Space) = 0
    rw [hz, zero_smul]
  have hcompact : NSFormalization.Section4.D01.MemForceCompact F := by
    have hKc : IsCompact K :=
      (isCompact_closedBall (2 : ℝ) 1).prod (isCompact_closedBall (0 : Space) 1)
    have hKcl : IsClosed K := isClosed_closedBall.prod isClosed_closedBall
    refine ⟨?_, HasCompactSupport.intro hKc hzero, ?_⟩
    · exact (((tb.contDiff (n := (⊤ : ℕ∞))).comp contDiff_fst).mul
        ((xb.contDiff (n := (⊤ : ℕ∞))).comp contDiff_snd)).smul contDiff_const
    · refine (closure_minimal (Function.support_subset_iff'.2 hzero) hKcl).trans ?_
      rintro ⟨t, x⟩ ⟨ht, -⟩
      refine ⟨?_, mem_univ _⟩
      have hb : |t - 2| ≤ 1 := by simpa [Real.dist_eq] using ht
      obtain ⟨ha, _⟩ := abs_le.mp hb
      simp only [mem_Ioi]
      linarith
  refine ⟨F, NSFormalization.Section4.D01.memForceR_of_memForceCompact hcompact, ?_⟩
  intro hF
  have htb : tb (2 : ℝ) = 1 :=
    tb.one_of_mem_closedBall (by norm_num [tb, mem_closedBall])
  have hxb : xb (0 : Space) = 1 :=
    xb.one_of_mem_closedBall (by norm_num [xb, mem_closedBall])
  have hp := congrFun hF (2, 0)
  change (tb (2 : ℝ) * xb (0 : Space)) •
    (EuclideanSpace.single 0 1 : Space) = 0 at hp
  rw [htb, hxb, one_mul, one_smul] at hp
  have := congrFun (congrArg (fun v : Space => (v : Fin 3 → ℝ)) hp) 0
  simp at this
