/-
Conformance check for B02 unit 7 (`low_high_split`).

`research/B02/Spec.lean` (namespace `BlowupDensity.B02.Draft`) is not on the Lake
module path, so its `def`s `lowHighConstant` and `SplitRange` are restated here
**verbatim** (from `Spec.lean:231-237`) in `BlowupDensity.B02.SpecMirror`.  The
`homogeneousFourierENorm` and `eLpNorm` in the spec field are the frozen ones of
`Contracts.V1.Data`, imported directly.  The `example` has the exact type of the
spec field `HomogeneousApproxAPI.lowHighSplit` (`Spec.lean:421-425`) and is
discharged by `NSFormalization.Section4.B02.lowHighSplit`; it type-checks because
the mirrored `SpecMirror.*` definitions are token-for-token copies, hence
definitionally equal, and `homogeneousFourierENorm s k` unfolds to the sum the
theorem bounds.

Check with:
  cd verification && lake env lean ../research/B02/axioms_u7.lean
-/
import Contracts.V1.Data
import NSFormalization.Section4.B02.LowHigh

open Set MeasureTheory NavierStokes.ProblemStatement NSFormalization.Source
open BlowupDensity.Contracts.V1.Data

noncomputable section

namespace BlowupDensity.B02.SpecMirror

/-- Verbatim `research/B02/Spec.lean:231`. -/
def lowHighConstant (s : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(3 : ℝ)) * ∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)

/-- Verbatim `research/B02/Spec.lean:237`. -/
def SplitRange (s : ℝ) : Prop := -3 / 2 < s ∧ s ≤ 0

/-- The type of `HomogeneousApproxAPI.lowHighSplit` (`research/B02/Spec.lean:421-425`),
discharged by `NSFormalization.Section4.B02.lowHighSplit`. -/
example : ∀ s : ℝ, SplitRange s → ∀ k : SpatialField,
      MemLp k 1 volume → MemLp k 2 volume →
    homogeneousFourierENorm s k ^ (2 : ℝ) ≤
      ENNReal.ofReal (lowHighConstant s) * eLpNorm k 1 volume ^ (2 : ℝ) +
        eLpNorm k 2 volume ^ (2 : ℝ) :=
  fun s hs k hk1 hk2 =>
    NSFormalization.Section4.B02.lowHighSplit s hs.1 hs.2 k hk1 hk2

#print axioms NSFormalization.Section4.B02.lowHighSplit

end BlowupDensity.B02.SpecMirror
