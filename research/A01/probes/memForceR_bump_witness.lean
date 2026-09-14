/-
# First nonzero closed `F_R` term — reviewer's non-vacuity witness (lane 137)

Preserved **verbatim** from the lane-137 reviewer's probe `/tmp/rev137/nonzero.lean`
(`research/A01/REVIEW_A3_FORCE.md`, Finding 3), credited to that review.  A time
`ContDiffBump` supported in `[1,3] ⊂ (0,∞)` times a space bump, `• e₀`, fed through
`D01.memForceR_of_memForceCompact`; `forceCap` and the L¹ cap are instantiated on it.

This is the **first nonzero closed `MemForceR` term in the project** (every prior witness
was the degenerate zero force, both sides of the L¹ cap `= 0`).  **Promotion candidate for
D01** as `memForceR_bump` — every future non-vacuity audit of an `F_R` consumer wants a
nonzero witness.  Pin gotcha (worth a LESSON): `ContDiffBump.contDiff`'s `n : ℕ∞`, so
`(n := ∞)` mismatches (`∞` there is `ℕ∞ω`); write `(n := (⊤ : ℕ∞))`.

Checked with `lake env lean` (four declarations, standard-3 axioms).
-/
import NSFormalization.Section4.A01.ForceCap

open Set Metric MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01 NSFormalization.Section4.A04 NSFormalization.Section4.D01
open scoped ContDiff

noncomputable section

def tb : ContDiffBump (2 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩
def xb : ContDiffBump (0 : Space) := ⟨1/2, 1, by norm_num, by norm_num⟩

/-- A nonzero `C_c^∞(ℝ³ × (0,∞);ℝ³)` force: a time bump on `[1,3]` times a space bump. -/
def Fbump : VelocityField :=
  fun p => (tb p.1 * xb p.2) • (EuclideanSpace.single 0 1 : Space)

def Kb : Set SpaceTime := closedBall (2 : ℝ) 1 ×ˢ closedBall (0 : Space) 1

theorem Fbump_zero_outside : ∀ p ∉ Kb, Fbump p = 0 := by
  intro p hp
  have hz : tb p.1 * xb p.2 = 0 := by
    by_cases h1 : p.1 ∈ closedBall (2 : ℝ) 1
    · have h2 : p.2 ∉ closedBall (0 : Space) 1 := fun h => hp ⟨h1, h⟩
      have hd : (1 : ℝ) ≤ dist p.2 0 := le_of_lt (by simpa [mem_closedBall] using h2)
      rw [show xb p.2 = 0 from xb.zero_of_le_dist (by exact hd), mul_zero]
    · have hd : (1 : ℝ) ≤ dist p.1 2 := le_of_lt (by simpa [mem_closedBall] using h1)
      rw [show tb p.1 = 0 from tb.zero_of_le_dist (by exact hd), zero_mul]
  show (tb p.1 * xb p.2) • (EuclideanSpace.single 0 1 : Space) = 0
  rw [hz, zero_smul]

theorem Fbump_compact : MemForceCompact Fbump := by
  have hKc : IsCompact Kb := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hKcl : IsClosed Kb := isClosed_closedBall.prod isClosed_closedBall
  refine ⟨?_, HasCompactSupport.intro hKc Fbump_zero_outside, ?_⟩
  · exact (((tb.contDiff (n := (⊤ : ℕ∞))).comp contDiff_fst).mul
      ((xb.contDiff (n := (⊤ : ℕ∞))).comp contDiff_snd)).smul contDiff_const
  · refine (closure_minimal (Function.support_subset_iff'.2 Fbump_zero_outside) hKcl).trans ?_
    rintro ⟨t, x⟩ ⟨ht, -⟩
    refine ⟨?_, mem_univ _⟩
    have hb : |t - 2| ≤ 1 := by simpa [Real.dist_eq] using ht
    obtain ⟨ha, _⟩ := abs_le.mp hb
    simp only [mem_Ioi]
    linarith

theorem Fbump_ne_zero : Fbump (2, 0) ≠ 0 := by
  have h1 : tb (2 : ℝ) = 1 := tb.one_of_mem_closedBall (by norm_num [tb, mem_closedBall])
  have h2 : xb (0 : Space) = 1 := xb.one_of_mem_closedBall (by norm_num [xb, mem_closedBall])
  show (tb (2:ℝ) * xb (0:Space)) • (EuclideanSpace.single 0 1 : Space) ≠ 0
  rw [h1, h2, one_mul, one_smul]
  intro h
  have := congrFun (congrArg (fun v : Space => (v : Fin 3 → ℝ)) h) 0
  simp at this

/-- The nonzero force lies in `F_R`. -/
theorem memForceR_Fbump : MemForceR Fbump := memForceR_of_memForceCompact Fbump_compact

theorem nonvac_forceCap_nonzero (m : ℕ) :
    ∃ Bbnd : ℝ,
      ContinuousOn (fun s => sobolevNormAt (m : ℝ) Fbump s) (Ico (0 : ℝ) 5) ∧
      (∀ t ∈ Ico (0 : ℝ) 5, 0 ≤ sobolevNormAt (m : ℝ) Fbump t) ∧
      (∀ t ∈ Ico (0 : ℝ) 5,
        (∫ s in (0 : ℝ)..t, sobolevNormAt (m : ℝ) Fbump s) ≤ Bbnd) :=
  forceCap memForceR_Fbump m (by norm_num)

theorem nonvac_L1_nonzero (m : ℕ) :
    (∫ s in (0 : ℝ)..5, sobolevNormAt (m : ℝ) Fbump s)
      ≤ (forceSobolevENormL1 (m : ℝ) Fbump).toReal :=
  intervalIntegral_le_forceSobolevENormL1_of_memForceR memForceR_Fbump m (by norm_num)

end

#print axioms Fbump_ne_zero
#print axioms memForceR_Fbump
#print axioms nonvac_forceCap_nonzero
#print axioms nonvac_L1_nonzero
