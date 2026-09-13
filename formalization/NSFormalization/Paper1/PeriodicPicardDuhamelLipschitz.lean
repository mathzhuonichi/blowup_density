import NSFormalization.Paper1.PeriodicDuhamelNormBound

noncomputable section
namespace NSFormalization.Paper1.PeriodicForcedDuhamel

open Set MeasureTheory
open NSFormalization.Paper1.PeriodicHeatMultiplier

/-- Explicit conditional Lipschitz contract for the Duhamel part of a Picard
map. The carrier-level integrand bound remains a hypothesis; this theorem only
supplies the genuine time-length gain. -/
structure PicardDuhamelLipschitzContract
    {ν t D : ℝ} (G H : ℝ → FourierHilbert) : Prop where
  hν : 0 ≤ ν
  ht : 0 ≤ t
  hG : IntervalIntegrable
    (fun τ => heat hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ)) volume 0 t
  hH : IntervalIntegrable
    (fun τ => heat hν (show 0 ≤ max (t - τ) 0 by positivity) (H τ)) volume 0 t
  pointwise : ∀ τ ∈ Icc (0 : ℝ) t, ‖G τ - H τ‖ ≤ D

/-- A Picard Duhamel contract yields a `t * D` norm bound. -/
theorem PicardDuhamelLipschitzContract.bound
    {ν t D : ℝ} {G H : ℝ → FourierHilbert}
    (C : PicardDuhamelLipschitzContract (ν := ν) (t := t) (D := D) G H) :
    ‖duhamel ν C.hν t G - duhamel ν C.hν t H‖ ≤ t * D := by
  exact norm_duhamel_sub_le_mul_of_norm_sub_le C.hν C.ht C.hG C.hH C.pointwise

end NSFormalization.Paper1.PeriodicForcedDuhamel
