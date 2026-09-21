-- Reviewer probe (lane 136 review, REVIEW_E2.md), preserved verbatim; compiles on this branch.
import Contracts.V1.Data
import Contracts.V1.GradientL6
import NSFormalization.Section4.C01.Vocabulary

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff

namespace Rev136NV
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open EulerLpTranslation EulerOrdinarySobolev
open NSFormalization.Section4.C01

def l2Sq (z : SpatialField) : ℝ := ∫ x : Space, ‖z x‖ ^ 2

/-- any compactly supported smooth field is a carrier-B element -/
def bumpField (φ : Space → Space) (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    SmoothL2Field Space where
  field := φ
  smooth := hs
  integrable n :=
    (hs.continuous_iteratedFDeriv (by simp)).memLp_of_hasCompactSupport (hc.iteratedFDeriv n)

def b : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩

def w : Space → Space := fun x => b x • axis 0

theorem w_smooth : ContDiff ℝ ∞ w := b.contDiff.smul contDiff_const

theorem w_compact : HasCompactSupport w := b.hasCompactSupport.smul_right

def W : SmoothL2Field Space := bumpField w w_smooth w_compact

theorem W_ne_zero : W.field ≠ 0 := by
  intro h
  have h0 : w 0 = 0 := by rw [show w = W.field from rfl, h]; rfl
  rw [show w 0 = b 0 • axis 0 from rfl,
    b.one_of_mem_closedBall (by simpa using b.rIn_pos.le), one_smul] at h0
  have := axis_norm (0 : Fin 3)
  rw [h0, norm_zero] at this
  exact zero_ne_one this

-- the three bridges instantiated on a NONZERO carrier element
#check (l2Sq_eq_inner W)
#check (gradientSq_eq_sum W)
#check (pairing_eq_inner W W)
#check (norm_toLp_sq_eq_l2Sq W)

#print axioms W_ne_zero

end Rev136NV
