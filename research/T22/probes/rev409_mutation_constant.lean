import NSFormalization.Section3.T22.CutoffDatum

/-! Reviewer mutation probe: changing the cutoff value `1` to `2` must make the
    delivered `exists_cutoff` proof inapplicable.  This file is intentionally
    not a successful Lean module; the expected type mismatch is recorded in the
    review. -/

noncomputable section

open Set Filter
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section3.T22
open scoped ContDiff ENNReal Topology

example {Ω K : Set Space} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ χ : Space → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      (∀ᶠ x in 𝓝ˢ K, χ x = 2) := by
  simpa using (exists_cutoff hΩ hK hKΩ)
