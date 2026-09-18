import NSFormalization.Section3.T22.RestrictBridge

/-!
# Concrete closure probe for the T22 left inequality

The field below is a nonzero smooth compactly supported vector bump whose
topological support is contained in `ball 0 1`.  The final theorem instantiates
the left conjunct of `zeroExtensionComparison` on that field and domain.
-/

noncomputable section

namespace NSFormalization.Section3.T22.Probe

open Set MeasureTheory Metric
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T22
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpatialField)
open scoped ENNReal ContDiff

def bridgeBump : ContDiffBump (0 : Space) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def bridgeField : SpatialField :=
  fun x => bridgeBump x • coordinateVector 0

theorem bridgeField_contDiff : ContDiff ℝ ∞ bridgeField := by
  exact bridgeBump.contDiff.smul_const (coordinateVector 0)

theorem bridgeField_hasCompactSupport : HasCompactSupport bridgeField := by
  exact bridgeBump.hasCompactSupport.smul_right

theorem bridgeField_tsupport :
    tsupport bridgeField ⊆ ball (0 : Space) 1 := by
  refine (tsupport_smul_subset_left (bridgeBump : Space → ℝ)
    (fun _ : Space => coordinateVector 0)).trans ?_
  rw [bridgeBump.tsupport_eq]
  apply closedBall_subset_ball
  change (1 / 2 : ℝ) < 1
  norm_num

theorem bridgeField_nonzero : bridgeField 0 ≠ 0 := by
  rw [bridgeField]
  have hzero : (0 : Space) ∈ closedBall (0 : Space) bridgeBump.rIn := by
    simp [bridgeBump]
  rw [bridgeBump.one_of_mem_closedBall hzero, one_smul]
  intro h
  have hi := congrArg (fun x : Space => x 0) h
  simp [coordinateVector] at hi

theorem concrete_left_conjunct (s : ℝ) :
    domainSobolevENorm (ball (0 : Space) 1) s
        (restrictField (ball (0 : Space) 1) bridgeField) ≤
      sobolevENorm s
        (zeroExtension (ball (0 : Space) 1) bridgeField) :=
  domainSobolevENorm_le_sobolevENorm

#print axioms bridgeBump
#print axioms bridgeField
#print axioms bridgeField_contDiff
#print axioms bridgeField_hasCompactSupport
#print axioms bridgeField_tsupport
#print axioms bridgeField_nonzero
#print axioms concrete_left_conjunct

end NSFormalization.Section3.T22.Probe
