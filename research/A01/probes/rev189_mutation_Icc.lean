import NSFormalization.Section4.A01.PressureRegularity

/-!
Intentional failing mutation: widen the per-time `MemLp` conclusion from
`Ico 0 S` to `Icc 0 S`, while leaving every premise unchanged.  Applying the
production theorem must fail because its conclusion supplies only `t < S`.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open scoped ContDiff

theorem rev189_pressureGradient_memLp_widened {S : ℝ} (ν : ℝ)
    (f u : VelocityField)
    (hc3 : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hf : D01.MemForceR f)
    (htime : ContDiffOn ℝ ∞
      (fun z : SpaceTime => temporalDerivative u z.1 z.2)
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hmom : ProjectedMomentumDatumOn ν f u S) :
    ∀ t ∈ Icc (0 : ℝ) S,
      MemLp (fun x : Space => pressureGradientOfVelocity ν f u (t, x)) 2 volume := by
  exact pressureGradient_memLp ν f u hc3 hf htime hmom

end NSFormalization.Section4.A01
