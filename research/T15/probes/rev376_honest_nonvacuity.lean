import NSFormalization.Section3.T15.Placement
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

noncomputable section

namespace NSFormalization.Section3.T15

open Set NavierStokes.ProblemStatement
open NSFormalization.Source NSFormalization.Source.PacketScaling

def rev376ReviewBump : ContDiffBump (0 : Space) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def rev376ReviewField : Space → Space :=
  fun x => rev376ReviewBump x • coordinateVector 0

def rev376ReviewVelocity : VelocityField := fun z => rev376ReviewField z.2

theorem rev376ReviewField_tsupport :
    tsupport rev376ReviewField ⊆ Metric.closedBall (0 : Space) (1 / 4) := by
  have hsub : Function.support rev376ReviewField ⊆
      Function.support (⇑rev376ReviewBump) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hz
    exact hx (by simp [rev376ReviewField, hz])
  have h : tsupport rev376ReviewField ⊆ tsupport (⇑rev376ReviewBump) :=
    closure_mono hsub
  rwa [rev376ReviewBump.tsupport_eq] at h

-- The worker's theorem application at t = 1/2 is before activation t₀ = 3/4.
example :
    scaledVelocity rev376ReviewVelocity 0 1 (1 / 2) (1 / 2, (0 : Space)) = 0 := by
  norm_num [scaledVelocity, scaledSourcePoint, scaledStartTime, zeroPastField]

-- At t = 7/8 the source time is 1/2, so this is a genuine nonzero
-- presingular slice to which the lane theorem applies.
example :
    scaledVelocity rev376ReviewVelocity 0 1 (1 / 2) (7 / 8, (0 : Space)) ≠ 0 := by
  have hv : rev376ReviewField (0 : Space) ≠ 0 := by
    have hb : rev376ReviewBump (0 : Space) = 1 :=
      rev376ReviewBump.one_of_mem_closedBall (by norm_num [rev376ReviewBump])
    simp [rev376ReviewField, hb, coordinateVector]
  simpa [scaledVelocity, scaledSourcePoint, scaledStartTime, zeroPastField,
    rev376ReviewVelocity] using And.intro
      (by norm_num : (1 : ℝ) - (2 ^ 2)⁻¹ < 7 / 8)
      (smul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hv)

example :
    tsupport (fun x : Space =>
      scaledVelocity rev376ReviewVelocity 0 1 (1 / 2) (7 / 8, x)) ⊆
      (fun y : Space => (0 : Space) + (1 / 2 : ℝ) • y) ''
        Metric.closedBall (0 : Space) (1 / 4) :=
  scaledVelocity_tsupp_subset (carrier := Metric.closedBall (0 : Space) (1 / 4))
    (by norm_num) (isCompact_closedBall _ _)
    (fun t _ => by
      have he : (fun x : Space => rev376ReviewVelocity (t, x)) = rev376ReviewField := rfl
      rw [he]; exact rev376ReviewField_tsupport)
    Subset.rfl (by norm_num : (7 / 8 : ℝ) < 1)

end NSFormalization.Section3.T15
