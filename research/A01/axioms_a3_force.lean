import NSFormalization.Section4.A01.ForceCap

/-!
# Axiom + non-vacuity audit for `Section4/A01/ForceCap.lean` (row A3-L1·f)

`#print axioms` for every new declaration must be exactly
`[propext, Classical.choice, Quot.sound]`.

Non-vacuity is exhibited on **two** members of `F_R`:

* the zero force `memForceR_zero` (degenerate: both sides of the L¹ cap are `0`), and
* the reviewer's **nonzero** bump force `memForceR_Fbump` (`research/A01/REVIEW_A3_FORCE.md`
  Finding 3, preserved verbatim in `research/A01/probes/memForceR_bump_witness.lean`) — the
  first nonzero closed `F_R` term in the project, reproduced here so its axioms are audited
  alongside the lane's exports.

`MemForceR` is faithful to the paper: eq:Rclasses (`02-preliminaries.tex:17`) is
`C^∞([0,∞);H^∞)` **with** `‖f‖_{L¹_tH^m}+‖f‖_{L²_tH^m}<∞` at every order, and `MemForceR`
carries exactly those two clauses (`MemLp G 1/2 forceTimeMeasure`), so the L¹ finiteness the
cap uses is the manuscript's own hypothesis, free via `A04.memL1Hm_of_memForceR` (review
Finding 1).
-/

open Set Metric MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A04
open NSFormalization.Section4.D01
open NSFormalization.Section4.A01
open scoped ContDiff

noncomputable section

/-! ## 1. Degenerate witness: the zero force -/

/-- Non-vacuity witness: the zero force lies in `F_R`. -/
theorem memForceR_zero : MemForceR (0 : VelocityField) :=
  memForceR_of_memForceCompact ⟨contDiff_const, by
    simp only [HasCompactSupport, tsupport, Function.support_zero, closure_empty]
    exact isCompact_empty, by simp [tsupport]⟩

/-- `forceCap` is non-vacuous: applied to the zero force at horizon `T₀ = 1`. -/
theorem nonvac_forceCap :
    ∃ Bbnd : ℝ,
      ContinuousOn (fun s => sobolevNormAt ((0 : ℕ) : ℝ) (0 : VelocityField) s) (Ico (0 : ℝ) 1) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ sobolevNormAt ((0 : ℕ) : ℝ) (0 : VelocityField) t) ∧
      (∀ t ∈ Ico (0 : ℝ) 1,
        (∫ s in (0 : ℝ)..t, sobolevNormAt ((0 : ℕ) : ℝ) (0 : VelocityField) s) ≤ Bbnd) :=
  forceCap memForceR_zero 0 (by norm_num)

/-- The manuscript L¹ cap is non-vacuous on the zero force. -/
theorem nonvac_L1cap :
    (∫ s in (0 : ℝ)..1, sobolevNormAt ((0 : ℕ) : ℝ) (0 : VelocityField) s)
      ≤ (forceSobolevENormL1 ((0 : ℕ) : ℝ) (0 : VelocityField)).toReal :=
  intervalIntegral_le_forceSobolevENormL1_of_memForceR memForceR_zero 0 (by norm_num)

/-- `forceCap_L1` is non-vacuous on the zero force. -/
theorem nonvac_forceCap_L1 :
    ContinuousOn (fun s => sobolevNormAt ((0 : ℕ) : ℝ) (0 : VelocityField) s) (Ico (0 : ℝ) 1) ∧
    (∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ sobolevNormAt ((0 : ℕ) : ℝ) (0 : VelocityField) t) ∧
    (∀ t ∈ Ico (0 : ℝ) 1,
      (∫ s in (0 : ℝ)..t, sobolevNormAt ((0 : ℕ) : ℝ) (0 : VelocityField) s)
        ≤ (forceSobolevENormL1 ((0 : ℕ) : ℝ) (0 : VelocityField)).toReal) :=
  forceCap_L1 memForceR_zero 0 1

/-! ## 2. Nonzero witness (reviewer's bump force, `REVIEW_A3_FORCE.md` Finding 3)

Verbatim from `research/A01/probes/memForceR_bump_witness.lean`; reproduced so the four
declarations are covered by this audit file. -/

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

-- New declarations of `ForceCap.lean`:
#print axioms sobolevNormAt_nonneg
#print axioms forceCap
#print axioms intervalIntegral_le_forceSobolevENormL1
#print axioms intervalIntegral_le_forceSobolevENormL1_of_memForceR
#print axioms forceCap_L1
-- Non-vacuity, zero force:
#print axioms memForceR_zero
#print axioms nonvac_forceCap
#print axioms nonvac_L1cap
#print axioms nonvac_forceCap_L1
-- Non-vacuity, nonzero bump force (review Finding 3):
#print axioms Fbump_ne_zero
#print axioms memForceR_Fbump
#print axioms nonvac_forceCap_nonzero
#print axioms nonvac_L1_nonzero
