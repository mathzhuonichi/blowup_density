import NSFormalization.Section3.T22.RestrictBridge

/-! Reviewer non-vacuity probe: both sides are finite for the lane's nonzero bump. -/

noncomputable section

namespace NSFormalization.Section3.T22.ReviewProbe

open Set MeasureTheory Metric
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T22
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff

def reviewBump : ContDiffBump (0 : Space) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def reviewField : SpatialField :=
  fun x => reviewBump x • coordinateVector 0

theorem reviewField_contDiff : ContDiff ℝ ∞ reviewField := by
  exact reviewBump.contDiff.smul_const (coordinateVector 0)

theorem reviewField_hasCompactSupport : HasCompactSupport reviewField := by
  exact reviewBump.hasCompactSupport.smul_right

theorem reviewField_tsupport :
    tsupport reviewField ⊆ ball (0 : Space) 1 := by
  refine (tsupport_smul_subset_left (reviewBump : Space → ℝ)
    (fun _ : Space => coordinateVector 0)).trans ?_
  rw [reviewBump.tsupport_eq]
  apply closedBall_subset_ball
  change (1 / 2 : ℝ) < 1
  norm_num

theorem reviewField_nonzero : reviewField 0 ≠ 0 := by
  rw [reviewField]
  have hzero : (0 : Space) ∈ closedBall (0 : Space) reviewBump.rIn := by
    simp [reviewBump]
  rw [reviewBump.one_of_mem_closedBall hzero, one_smul]
  intro h
  have hi := congrArg (fun x : Space => x 0) h
  simp [coordinateVector] at hi

theorem zeroExtension_reviewField :
    zeroExtension (ball (0 : Space) 1) reviewField = reviewField := by
  funext x
  by_cases hx : x ∈ ball (0 : Space) 1
  · simp [zeroExtension, hx]
  · have hz : reviewField x = 0 := by
      by_contra hne
      have hsupp : x ∈ Function.support reviewField := hne
      have htsupp : x ∈ tsupport reviewField := subset_closure hsupp
      exact hx (reviewField_tsupport htsupp)
    simp [zeroExtension, hx, hz]

theorem concrete_left_conjunct_nonvacuous (s : ℝ) :
    domainSobolevENorm (ball (0 : Space) 1) s
          (restrictField (ball (0 : Space) 1) reviewField) ≠ ⊤ ∧
      sobolevENorm s
          (zeroExtension (ball (0 : Space) 1) reviewField) ≠ ⊤ := by
  have hfinite : sobolevENorm s reviewField ≠ ⊤ := by
    apply sobolevENorm_ne_top_of_contDiff_memLp reviewField_contDiff
    intro n
    exact (reviewField_contDiff.continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).memLp_of_hasCompactSupport
      (reviewField_hasCompactSupport.iteratedFDeriv n)
  rw [zeroExtension_reviewField]
  have hle := domainSobolevENorm_le_sobolevENorm
    (Ω := ball (0 : Space) 1) (s := s) (z := reviewField)
  rw [zeroExtension_reviewField] at hle
  exact ⟨ne_top_of_le_ne_top hfinite hle, hfinite⟩

end NSFormalization.Section3.T22.ReviewProbe
