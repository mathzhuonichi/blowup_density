import NSFormalization.Section3.T12.HaarCube
import NSFormalization.Section3.T13.ConstantEndpoints

noncomputable section
namespace NSFormalization.Section3.T12

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField)

/-- Centre of the fundamental cube. -/
def rev366Center : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1 / 2 : ℝ))

/-- A genuine smooth bump supported in `closedBall rev366Center (1/4)`. -/
def rev366Bump : ContDiffBump rev366Center :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- A nonzero smooth vector field supported strictly inside the cube. -/
def rev366Field : SpatialField := fun x => (rev366Bump x) • coordinateVector 0

theorem rev366_ball_admissible :
    closure (Metric.ball rev366Center (3 / 8 : ℝ)) ⊆ interior fundamentalCube := by
  refine (Metric.closure_ball_subset_closedBall).trans ?_
  rw [interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - rev366Center‖ ≤ 3 / 8 := by
    rw [← dist_eq_norm]
    exact hx
  have h1 : |x i - rev366Center i| ≤ 3 / 8 := by
    have h := abs_spaceCoord_le_norm (x - rev366Center) i
    have h2 : (x - rev366Center) i = x i - rev366Center i := rfl
    rw [h2] at h
    linarith
  have hc : rev366Center i = 1 / 2 := rfl
  rw [hc, abs_le] at h1
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

theorem rev366Field_supported :
    tsupport rev366Field ⊆ Metric.ball rev366Center (3 / 8 : ℝ) := by
  have hsub : Function.support rev366Field ⊆ Function.support (⇑rev366Bump) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hg
    exact hx (by simp [rev366Field, hg])
  have h1 : tsupport rev366Field ⊆ tsupport (⇑rev366Bump) := closure_mono hsub
  rw [rev366Bump.tsupport_eq] at h1
  refine h1.trans ?_
  intro y hy
  rw [Metric.mem_closedBall] at hy
  rw [Metric.mem_ball]
  have hr : rev366Bump.rOut = 1 / 4 := rfl
  rw [hr] at hy
  linarith

theorem rev366Field_support_interior :
    Function.support rev366Field ⊆ interior fundamentalCube :=
  (subset_tsupport rev366Field).trans
    (rev366Field_supported.trans (subset_closure.trans rev366_ball_admissible))

theorem rev366Field_ne_zero : rev366Field rev366Center ≠ 0 := by
  have h1 : rev366Bump rev366Center = 1 :=
    rev366Bump.one_of_mem_closedBall (Metric.mem_closedBall_self rev366Bump.rIn_pos.le)
  have h2 : rev366Field rev366Center = coordinateVector 0 := by
    simp [rev366Field, h1]
  rw [h2]
  intro hcon
  have hz : (coordinateVector (0 : Fin 3)) 0 = 0 := by rw [hcon]; rfl
  rw [coordinateVector] at hz
  simp at hz

example :
    eLpNorm rev366Field 3 (volume.restrict fundamentalCube) =
      eLpNorm rev366Field 3 volume :=
  eLpNorm_restrict_eq_of_support rev366Field rev366Field_support_interior 3

example :
    eLpNorm rev366Field 6 (volume.restrict fundamentalCube) =
      eLpNorm rev366Field 6 volume :=
  eLpNorm_restrict_eq_of_support rev366Field rev366Field_support_interior 6

end NSFormalization.Section3.T12
