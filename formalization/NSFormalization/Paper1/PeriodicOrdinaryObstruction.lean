import NSFormalization.Paper1.PeriodicOrdinaryLocal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The ordinary `L²` obstruction for a periodic lift

The whole-space solver in `OrdinaryForcedLocal` is a valid finite-order
construction, but its datum is an ordinary `L²` field.  A periodic manuscript
datum is not automatically such a field.  This file records a small, fully
proved obstruction: a continuous one-periodic field on the line that is
whole-space `L¹` must vanish identically.  The result is deliberately
one-dimensional and makes the slice-integrability hypothesis explicit; it is
the exact ingredient still needed to turn this observation into a
three-dimensional obstruction for an ordinary representative.
-/

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace NSFormalization.Paper1.PeriodicOrdinaryObstruction

/-- Every continuous one-periodic scalar with finite whole-line `L¹` norm
vanishes on the closed fundamental interval.  The proof uses the existing
decomposition of the line into integer translates and the fact that a
summable constant family indexed by `ℤ` must have zero constant. -/
theorem periodic_continuous_integrable_zero_on_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg_cont : Continuous g)
    (hg_periodic : Function.Periodic g 1)
    (hg_int : Integrable g MeasureTheory.volume) :
    ∀ x : ℝ, g x = 0 := by
  let hnorm : ℝ → ℝ := fun x => ‖g x‖
  have hnorm_cont : Continuous hnorm := hg_cont.norm
  have hnorm_int : Integrable hnorm MeasureTheory.volume := by
    simpa only [hnorm] using hg_int.norm
  have hnorm_periodic : Function.Periodic hnorm 1 := by
    intro x
    dsimp [hnorm]
    rw [hg_periodic x]
  have hsum := hnorm_int.hasSum_intervalIntegral (0 : ℝ)
  let c : ℝ := ∫ x in (0 : ℝ)..1, hnorm x
  have hterm : ∀ n : ℤ,
      (∫ x in ((0 : ℝ) + (n : ℝ))..(((0 : ℝ) + (n : ℝ)) + 1), hnorm x) = c := by
    intro n
    dsimp [c]
    simpa only [zero_add] using
      hnorm_periodic.intervalIntegral_add_eq (n : ℝ) 0
  have hsummable_const : Summable (fun _ : ℤ => c) :=
    hsum.summable.congr hterm
  have hc : c = 0 := by
    by_contra hcn
    have hcpos : 0 < c := by
      exact lt_of_le_of_ne (intervalIntegral.integral_nonneg (by norm_num)
        (fun x _ => norm_nonneg (g x))) (Ne.symm hcn)
    have hfinite : (Set.univ : Set ℤ).Finite :=
      Set.Finite.of_summable_const hcpos hsummable_const
    exact Set.Infinite.not_finite (Set.infinite_univ : (Set.univ : Set ℤ).Infinite) hfinite
  have hzero_int : (∫ x in (0 : ℝ)..1, hnorm x) = 0 := hc
  intro x
  by_contra hne
  have hpos : 0 < hnorm x := (norm_pos_iff.mpr hne)
  have hlt : x < x + 1 := by linarith
  have hstrict : 0 < ∫ y in x..(x + 1), hnorm y := by
    apply intervalIntegral.integral_pos hlt hnorm_cont.continuousOn
      (fun y hy => norm_nonneg (g y))
    exact ⟨x, ⟨le_rfl, le_add_of_nonneg_right zero_le_one⟩, hpos⟩
  have htranslate : (∫ y in x..(x + 1), hnorm y) =
      ∫ y in (0 : ℝ)..1, hnorm y := by
    simpa only [zero_add] using hnorm_periodic.intervalIntegral_add_eq x 0
  exact (ne_of_gt hstrict) (htranslate.trans hzero_int)

end NSFormalization.Paper1.PeriodicOrdinaryObstruction
