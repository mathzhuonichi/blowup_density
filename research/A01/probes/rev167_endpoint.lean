import NSFormalization.Section4.A01.ForceBridge

/-! Reviewer probe: the zero extension is not smooth at a nonzero right endpoint. -/

open Set Metric
open NavierStokes.ProblemStatement
open EulerLpTranslation
open NSFormalization.Section4.D01
open scoped ContDiff

noncomputable section

namespace NSFormalization.Section4.A01

/-- Restricting a genuine global force and then zero-extending it creates a jump at every
endpoint where the force is nonzero. -/
theorem not_forcePathSmoothness_forcePath_of_endpoint_ne_zero
    {S : ℝ} (hS : 0 ≤ S) {f : A02.SpaceTimeField} (hf : D01.MemForceR f)
    (x : Space) (hne : f (S, x) ≠ 0) :
    ¬ ForcePathSmoothness (C01.forcePath (S := S) hf) := by
  intro hsmooth
  let F : Icc (0 : ℝ) S → SmoothL2Field Space := C01.forcePath hf
  let g : A02.SpaceTimeField := forceOfPath F
  have hfuture : (S, x) ∈ futureDomain := ⟨hS, mem_univ x⟩
  have hc : ContinuousWithinAt g (Ioi S ×ˢ (univ : Set Space)) (S, x) :=
    (hsmooth.1.continuousOn (S, x) hfuture).mono (by
      rintro ⟨t, y⟩ ⟨ht, -⟩
      exact ⟨hS.trans ht.le, mem_univ y⟩)
  have hclosure : (S, x) ∈ closure (Ioi S ×ˢ (univ : Set Space)) := by
    rw [closure_prod_eq, closure_Ioi, closure_univ]
    exact ⟨show S ≤ S from le_rfl, mem_univ x⟩
  have hzero : g (S, x) = 0 := hc.eq_const_of_mem_closure hclosure (by
    rintro ⟨t, y⟩ ⟨ht, -⟩
    have hnot : t ∉ Icc (0 : ℝ) S := fun h => (not_lt_of_ge h.2) ht
    simp only [g, forceOfPath, hnot, dite_false])
  have heq : g (S, x) = f (S, x) := by
    calc
      g (S, x) = (F ⟨S, hS, le_rfl⟩).field x := forceOfPath_apply F ⟨S, hS, le_rfl⟩ x
      _ = f (S, x) := rfl
  exact hne (heq.symm.trans hzero)

/-! A concrete nonzero member of `F_R`, reused from the lane-137 non-vacuity construction. -/

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

example : ¬ ForcePathSmoothness (C01.forcePath (S := (2 : ℝ)) endpointBump_memForceR) :=
  not_forcePathSmoothness_forcePath_of_endpoint_ne_zero (by norm_num) endpointBump_memForceR
    0 endpointBump_ne_zero

/-! The constructor-facing direction needs no invented force: on `[0,S]`, the path reconstructed
from the original global `f` has exactly the original physical slices. -/
theorem forceOfPath_forcePath_eq_on_horizon
    {S : ℝ} {f : A02.SpaceTimeField} (hf : D01.MemForceR f)
    (t : Icc (0 : ℝ) S) (x : Space) :
    forceOfPath (C01.forcePath (S := S) hf) (t.1, x) = f (t.1, x) := by
  rw [forceOfPath_apply]
  rfl

#print axioms not_forcePathSmoothness_forcePath_of_endpoint_ne_zero
#print axioms forceOfPath_forcePath_eq_on_horizon

end NSFormalization.Section4.A01
