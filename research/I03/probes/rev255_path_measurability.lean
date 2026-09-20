import NSFormalization.Section4.I03.PathMeasurability

noncomputable section

namespace NSFormalization.Section4.I03

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 NSFormalization.Source
open NSFormalization.Section4.D01.Homogeneous
open scoped ContDiff ENNReal

/- The main continuity theorem has a concrete satisfiable instance, independent
of the existence of a downstream `PacketAPI`. -/
example :
    Continuous (compactHomogeneousPath
      (by norm_num : -3 / 2 < (-1 : ℝ))
      (by exact contDiff_const : ContDiff ℝ ∞ (0 : VelocityField))
      (by
        simp only [HasCompactSupport, tsupport, Function.support_zero, closure_empty]
        exact isCompact_empty)) := by
  exact compactHomogeneousPath_continuous (by norm_num) (by norm_num)
    (by exact contDiff_const) (by
      simp only [HasCompactSupport, tsupport, Function.support_zero, closure_empty]
      exact isCompact_empty)

/- Negative mutation: replacing the sharp Fourier-normalization factor
`(2π)^(-3)` by the strictly smaller `(2π)^(-4)` is not supplied by the main
estimate.  The attempted reuse below must fail by a RHS type mismatch. -/
example {s : ℝ}
    (hs : -3 / 2 < s) (hs0 : s ≤ 0) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t u : ℝ) :
    ‖compactHomogeneousPath hs hF hc t - compactHomogeneousPath hs hF hc u‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal ((2 * Real.pi) ^ (-(4 : ℝ)) *
          ∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)) *
          eLpNorm (fun x : Space => F (t, x) - F (u, x)) 1 volume ^ (2 : ℝ) +
        eLpNorm (fun x : Space => F (t, x) - F (u, x)) 2 volume ^ (2 : ℝ) := by
  exact compactHomogeneousPath_sub_enorm_sq_le hs hs0 hF hc t u

end NSFormalization.Section4.I03
