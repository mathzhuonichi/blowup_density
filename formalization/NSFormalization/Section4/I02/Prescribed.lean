import NSFormalization.Paper1.LocalCutoff

/-!
# I02 version 2: the cutoff built around a prescribed enlargement of the carrier

`paper/sections/03-torus.tex:101-102` starts the insertion by choosing a compact
`K_*` containing the packet carrier `K` **and** the spatial projection of
`supp F`, and only then builds the cutoff `θ` and the radius `R_*` around it
(`03-torus.tex:167-174, 181, 212`).  `NSFormalization.Paper1.exists_spatial_cutoff`
produces a cutoff around a single compact set inside a prescribed ball, and
`Source/InsertionFamily.lean:218-234` already forms `Kall = K ∪ Prod.snd ''
tsupport f` inline -- but it then builds the plateau around `K` alone and
recovers the force radius separately.

This file records the one step that the version-two correction contract
(`verification/Contracts/V2/Correction.lean`) needs and that no declaration in
the tree states: a *single* cutoff whose open plateau covers two prescribed
compact sets at once, with the enclosing radius produced rather than assumed.
It is the only new mathematics of the version-two binding; everything else in
`verification/Bindings/CorrectionV2.lean` is the version-one argument verbatim.
-/

noncomputable section

namespace NSFormalization.Section4.I02

open NavierStokes.ProblemStatement Set Metric
open scoped ContDiff Topology

/-- A smooth compactly supported cutoff, centred at the origin, whose open
plateau contains two prescribed compact sets, together with the radius that
encloses its support.

Applied with `K₁ = K` the packet carrier and `K₂ = K_*` the caller's compact
enlargement, this is `03-torus.tex:101-102` followed by `03-torus.tex:181`: the
radius it returns is the manuscript's `R_*` (`03-torus.tex:212`), and because the
plateau covers `K₂` as well, the smallness clause `ε R_* < r` places
`x₀ + ε K_*` inside the coordinate ball `B` and not merely `x₀ + ε K`. -/
theorem exists_prescribed_cutoff {K₁ K₂ : Set Space}
    (h₁ : IsCompact K₁) (h₂ : IsCompact K₂) :
    ∃ R : ℝ, ∃ θ : Space → ℝ, ∃ O : Set Space,
      0 < R ∧ ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
        tsupport θ ⊆ ball (0 : Space) R ∧ IsOpen O ∧ K₁ ⊆ O ∧ K₂ ⊆ O ∧
        EqOn θ (fun _ => 1) O := by
  obtain ⟨B, hB, hb⟩ := (h₁.union h₂).isBounded.exists_pos_norm_le
  have hR : (0 : ℝ) < B + 1 := by linarith
  have hKR : K₁ ∪ K₂ ⊆ ball (0 : Space) (B + 1) := by
    intro y hy
    have hyb := hb y hy
    rw [mem_ball, dist_zero_right]
    linarith
  obtain ⟨θ, O, hθ, hθc, hθR, hO, hKO, hθone⟩ :=
    Paper1.exists_spatial_cutoff (h₁.union h₂) hR hKR
  exact ⟨B + 1, θ, O, hR, hθ, hθc, hθR, hO, subset_union_left.trans hKO,
    subset_union_right.trans hKO, hθone⟩

end NSFormalization.Section4.I02
