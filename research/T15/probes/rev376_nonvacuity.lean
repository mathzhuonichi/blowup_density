import NSFormalization.Section3.T15.Placement
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

noncomputable section

namespace NSFormalization.Section3.T15

open Set NavierStokes.ProblemStatement
open NSFormalization.Source NSFormalization.Source.PacketScaling

def rev376Bump : ContDiffBump (0 : Space) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def rev376Field : Space → Space := fun x => rev376Bump x • coordinateVector 0

def rev376Velocity : VelocityField := fun z => rev376Field z.2

theorem rev376Field_tsupport :
    tsupport rev376Field ⊆ Metric.closedBall (0 : Space) (1 / 4) := by
  have hsub : Function.support rev376Field ⊆ Function.support (⇑rev376Bump) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hz
    exact hx (by simp [rev376Field, hz])
  have h : tsupport rev376Field ⊆ tsupport (⇑rev376Bump) := closure_mono hsub
  rwa [rev376Bump.tsupport_eq] at h

theorem rev376_zeroPast_slice_tsupport (s : ℝ) :
    tsupport (fun x : Space => zeroPastField rev376Velocity (s, x)) ⊆
      Metric.closedBall (0 : Space) (1 / 4) := by
  by_cases hs : 0 < s
  · simpa [zeroPastField, hs, rev376Velocity] using rev376Field_tsupport
  · simp [zeroPastField, hs, tsupport]

theorem rev376_scaled_support (t : ℝ) :
    tsupport (fun x : Space =>
      scaledVelocity rev376Velocity 0 1 (1 / 2) (t, x)) ⊆
      (fun y : Space => (0 : Space) + (1 / 2 : ℝ) • y) ''
        Metric.closedBall (0 : Space) (1 / 4) := by
  rw [scaledVelocity_eq_parabolicVelocity]
  have h :=
    parabolic_support (isCompact_closedBall (0 : Space) (1 / 4 : ℝ))
      (by norm_num : 0 < (1 / 2 : ℝ)⁻¹) (0 : Space)
      (rev376_zeroPast_slice_tsupport
        (((1 / 2 : ℝ)⁻¹) ^ 2 * (t - (1 - (1 / 2 : ℝ) ^ 2))))
  simpa only [scaledSupport, inv_inv] using h

example : (1 / 2 : ℝ) ∈ Ioc 0 1 := by norm_num

example : rev376Field (0 : Space) ≠ 0 := by
  have hb : rev376Bump (0 : Space) = 1 :=
    rev376Bump.one_of_mem_closedBall (by norm_num [rev376Bump])
  simp [rev376Field, hb, coordinateVector]

example :
    scaledVelocity rev376Velocity 0 1 (1 / 2) (1, (0 : Space)) ≠ 0 := by
  have hv : rev376Field (0 : Space) ≠ 0 := by
    have hb : rev376Bump (0 : Space) = 1 :=
      rev376Bump.one_of_mem_closedBall (by norm_num [rev376Bump])
    simp [rev376Field, hb, coordinateVector]
  simpa [scaledVelocity, scaledSourcePoint, scaledStartTime, zeroPastField,
    rev376Velocity] using (smul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hv)

/-- The lane theorem `scaledVelocity_tsupp_subset` fires on this concrete packet
at a genuine presingular time `t = 1/2 ∈ Ico 0 1` (here `T = 1`), from its raw
support clauses: the bump slice support is `t`-independent and compact, with
`Kstar = carrier = closedBall 0 (1/4)`.  (The reviewer's original check evaluated
at `t = 1`, which is `= T` and outside the honest window `Ico 0 T`; the
`t`-uniform direct bound `rev376_scaled_support` above still covers that time.) -/
example :
    tsupport (fun x : Space =>
      scaledVelocity rev376Velocity 0 1 (1 / 2) (1 / 2, x)) ⊆
      (fun y : Space => (0 : Space) + (1 / 2 : ℝ) • y) ''
        Metric.closedBall (0 : Space) (1 / 4) :=
  scaledVelocity_tsupp_subset (carrier := Metric.closedBall (0 : Space) (1 / 4))
    (by norm_num) (isCompact_closedBall _ _)
    (fun t _ => by
      have he : (fun x : Space => rev376Velocity (t, x)) = rev376Field := rfl
      rw [he]; exact rev376Field_tsupport)
    Subset.rfl (by norm_num : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) 1)

end NSFormalization.Section3.T15
