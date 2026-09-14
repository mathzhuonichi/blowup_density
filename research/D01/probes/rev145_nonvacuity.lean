-- REVIEW PROBE (lane 145): non-vacuity of the m = 2 quantitative constructor on a CONCRETE
-- nonzero, smooth, compactly supported field, plus name resolution of `IsSobolevDatum`.
-- Run: cd verification && lake env lean ../research/D01/probes/rev145_nonvacuity.lean
import NSFormalization.Section4.D01.FiniteOrderNorm

open MeasureTheory NavierStokes.ProblemStatement EulerLpTranslation
open NSFormalization.Section4.D01
open scoped ContDiff ENNReal

noncomputable section

-- Which `IsSobolevDatum` does the module actually use?  (D01's, not A02's.)
#check @NSFormalization.Section4.D01.norm_isSobolevDatum_le_two
#check @IsSobolevDatum

/-- A concrete nonzero smooth compactly supported vector field on ℝ³:
a `ContDiffBump` scalar times a fixed unit vector. -/
def probeBump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩

def probeField : Space → Space := fun x => (probeBump x) • (EuclideanSpace.single 0 (1 : ℝ))

theorem probeField_smooth : ContDiff ℝ ∞ probeField :=
  (probeBump.contDiff (n := (⊤ : ℕ∞))).smul contDiff_const

theorem probeField_hasCompactSupport : HasCompactSupport probeField := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) probeBump.rOut) ?_
  intro x hx
  have hd : probeBump.rOut ≤ dist x 0 := by
    simpa [Metric.mem_closedBall, not_le] using le_of_lt (not_le.mp (by simpa using hx))
  simp [probeField, probeBump.zero_of_le_dist hd]

def probeSmoothField : SmoothL2Field Space where
  field := probeField
  smooth := probeField_smooth
  integrable n :=
    (probeField_smooth.continuous_iteratedFDeriv (by simp)).memLp_of_hasCompactSupport
      (probeField_hasCompactSupport.iteratedFDeriv n)

-- the field is genuinely nonzero (the bump is 1 at the centre)
example : probeField 0 = EuclideanSpace.single 0 (1 : ℝ) := by
  have h1 : probeBump 0 = 1 :=
    probeBump.one_of_mem_closedBall (Metric.mem_closedBall_self probeBump.rIn_pos.le)
  simp [probeField, h1]

-- the order-2 quantitative chain, end to end, on this concrete field, with a FINITE explicit M
example : ∃ (M : ℝ) (A : NSFormalization.Paper3.RealVectorSobolev ((2 : ℕ) : ℝ)),
    HasWeakDerivsL2Bound probeField M 2 ∧
    IsSobolevDatum ((2 : ℕ) : ℝ) probeField A ∧ ‖A‖ ^ 2 ≤ 256 * M := by
  obtain ⟨M, hM⟩ := exists_hasWeakDerivsL2Bound_smooth 2 probeSmoothField
  obtain ⟨A, hA, _⟩ := exists_isSobolevDatum_norm_le 2 probeField M hM
  exact ⟨M, A, hM, hA, norm_isSobolevDatum_le_two probeField M hM A hA⟩

-- the order-0 bound on the same concrete field
example : ‖orderZeroDatum probeSmoothField.memLp‖ ≤ ‖probeSmoothField.memLp.toLp‖ :=
  norm_orderZeroDatum_le _
