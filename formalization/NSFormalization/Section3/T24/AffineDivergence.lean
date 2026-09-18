import NSFormalization.Section3.T24.AffineBasics

/-!
# T24a Ua2: divergence of affine variations

The packet structure is deliberately absent from this canonical layer.  The
two packet clauses used here are supplied in their raw forms: smoothness of the
velocity on the presingular slab and vanishing spatial divergence there.
-/

noncomputable section

namespace NSFormalization.Section3.T24

open Set
open NavierStokes.ProblemStatement
open scoped ContDiff

/-- Ua2 `divergence_free` (`Spec.lean:1038-1040`).  Spatial divergence is
additive because the raw packet smoothness and affine admissibility give the
genuine spatial differentiability required by `ResidualCalculus` at each
point. -/
theorem divergence_free {U : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain)
    (hdivergence : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
      spatialDivergence U t x = 0) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
        spatialDivergence (affineVelocity U b) t x = 0 := by
  intro b hb t ht x
  have hU_slice : ContDiff ℝ ∞ (fun y : Space ↦ U (t, y)) :=
    hvelocity_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun y ↦ ⟨ht, mem_univ y⟩)
  have hb_slice : ContDiff ℝ ∞ (fun y : Space ↦ b (t, y)) :=
    hb.1.comp (contDiff_const.prodMk contDiff_id)
  change spatialDivergence (fun z ↦ U z + b z) t x = 0
  rw [NavierStokes.ResidualCalculus.spatialDivergence_add U b t x
    (hU_slice.differentiable (by simp) x)
    (hb_slice.differentiable (by simp) x),
    hdivergence t ht x, hb.2.2.2 t x, add_zero]

end NSFormalization.Section3.T24
