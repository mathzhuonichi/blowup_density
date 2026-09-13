import NSFormalization.Paper3.SobolevDensity
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Direct reuse of Banach-valued temporal smoothing

Mathlib's existing compact smooth approximation theorem applies directly to
Bochner Lq paths valued in the complete Sobolev Hilbert model. Compact support
in this theorem is temporal. It does not assert compact physical spatial
support of each Sobolev distribution represented by the path.
-/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory
open scoped ContDiff ENNReal

/-- Compact smooth Sobolev-valued time paths are dense in genuine Bochner Lq. -/
theorem dense_temporal_compact_smooth_sobolev (s : ℝ) (q : ℝ≥0∞)
    (hq : q ≠ ⊤) [Fact (1 ≤ q)] :
    Dense {f : Lp (SobolevHilbert s) q (volume : Measure ℝ) |
      ∃ g : ℝ → SobolevHilbert s,
        f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} :=
  Lp.dense_hasCompactSupport_contDiff hq

/-- The same existing theorem supplies an actual approximation with an explicit
Bochner norm error bound, including both manuscript exponents q=1 and q=2. -/
theorem exists_temporal_compact_smooth_sobolev_approx (s : ℝ) (q : ℝ≥0∞)
    (hq : q ≠ ⊤) (hqone : 1 ≤ q) (f : ℝ → SobolevHilbert s)
    (hf : MemLp f q volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → SobolevHilbert s,
      HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
        eLpNorm (f - g) q volume ≤ ENNReal.ofReal ε :=
  hf.exist_eLpNorm_sub_le hq hqone hε

end NSFormalization.Paper3
