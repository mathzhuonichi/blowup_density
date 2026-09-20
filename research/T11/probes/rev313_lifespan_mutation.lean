import NSFormalization.Section3.T11.LocalExistence

noncomputable section
namespace NSFormalization.Section3.T11.Rev313

open Set
open NSFormalization.Section3.T10

local instance rev313NormedGroup : NormedAddCommGroup (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance rev313NormedSpace : NormedSpace ℝ (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedSpace

/-- Deliberately unsafe mutation: replacing `2 / √ν` by `1 / √ν` widens the
claimed interval in the quantitative fixed-point theorem. -/
def torusKernelTimeWidened (ν η : ℝ) : ℝ :=
  min 1 ((η / (1 + (Real.sqrt ν)⁻¹)) ^ 2)

example {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (A : PeriodicSobolev 3) (F : ℝ → PeriodicSobolev 3) (B : ℝ) (hB : 0 ≤ B)
    (hF : ContinuousOn F (Icc 0 1)) (hFB : ∀ t ∈ Icc (0 : ℝ) 1, ‖F t‖ ≤ B) :
    let b := ‖A‖ + B
    let T := torusKernelTimeWidened ν (torusPicardThreshold ‖C.analytic.bilinear‖ b)
    0 < T ∧ T ≤ 1 ∧ ∃ u : ℝ → PeriodicSobolev 3,
      TorusForcedMildOn C A F T u ∧ (∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ b+1) ∧
      ∀ v : ℝ → PeriodicSobolev 3, TorusForcedMildOn C A F T v →
        (∀ t ∈ Icc (0 : ℝ) T, ‖v t‖ ≤ b+1) → ∀ t ∈ Icc (0 : ℝ) T, v t = u t := by
  exact torusForcedPicard_quantitative hν C A F B hB hF hFB

end NSFormalization.Section3.T11.Rev313
