import NSFormalization.Paper3.SobolevBochnerDensity
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Finite separated-variable Bochner density

This adapter uses Mathlib's continuous bilinear lift `compLpL₂`, closed-submodule
machinery, and `Lp.induction`. It does not reconstruct simple-function density.
-/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory ContinuousLinearMap
open scoped ContDiff ENNReal

variable {μ : Measure ℝ}
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The actual Bochner vector represented by `t ↦ g(t) • h`. -/
def separatedLp (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    H →L[ℝ] Lp ℝ q μ →L[ℝ] Lp H q μ :=
  ((ContinuousLinearMap.smulRightL ℝ ℝ H) (ContinuousLinearMap.id ℝ ℝ)).compLpL₂ q μ

 theorem separatedLp_ae (q : ℝ≥0∞) [Fact (1 ≤ q)] (h : H)
    (g : Lp ℝ q μ) :
    separatedLp q h g =ᵐ[μ] fun t => g t • h :=
  (ContinuousLinearMap.toSpanSingleton ℝ h).coeFn_compLp g

/-- A dense set of coefficients and a dense set of scalar temporal functions
have a dense finite separated-variable span in genuine Bochner Lq. -/
theorem dense_span_separatedLp (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q ≠ ⊤)
    {D : Set H} (hD : Dense D)
    {A : Set (Lp ℝ q μ)} (hA : Dense A) :
    Dense (Submodule.span ℝ {v : Lp H q μ |
      ∃ h ∈ D, ∃ g ∈ A, v = separatedLp q h g} : Set (Lp H q μ)) := by
  let S := Submodule.span ℝ {v : Lp H q μ |
      ∃ h ∈ D, ∃ g ∈ A, v = separatedLp q h g}
  let C := S.topologicalClosure
  have hclosed : IsClosed (C : Set (Lp H q μ)) := S.isClosed_topologicalClosure
  have htensor : ∀ (h : H) (g : Lp ℝ q μ), separatedLp q h g ∈ C := by
    intro h g
    apply hA.induction (P := fun g => separatedLp q h g ∈ C) ?_
      (hclosed.preimage (separatedLp q h).continuous) g
    intro g hg
    apply hD.induction (P := fun h => separatedLp q h g ∈ C) ?_
      (hclosed.preimage ((separatedLp (H := H) q).flip g).continuous) h
    intro h hh
    exact S.le_topologicalClosure (Submodule.subset_span ⟨h, hh, g, hg, rfl⟩)
  have hall : ∀ f : Lp H q μ, f ∈ C := by
    apply Lp.induction hq (fun f => f ∈ C)
    · intro h E hE hμE
      have heq : separatedLp q h (indicatorConstLp q hE hμE.ne (1 : ℝ)) =
          indicatorConstLp q hE hμE.ne h := by
        apply Lp.ext
        filter_upwards [separatedLp_ae q h (indicatorConstLp q hE hμE.ne (1 : ℝ)),
          indicatorConstLp_coeFn (p := q) (hs := hE) (hμs := hμE.ne) (c := (1 : ℝ)),
          indicatorConstLp_coeFn (p := q) (hs := hE) (hμs := hμE.ne) (c := h)] with t ht h1 hh
        rw [ht, h1, hh]
        by_cases hmem : t ∈ E <;> simp [hmem]
      rw [Lp.simpleFunc.coe_indicatorConst, ← heq]
      exact htensor _ _
    · intro f g hf hg hd hfc hgc
      exact C.add_mem hfc hgc
    · exact hclosed
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (Submodule.eq_top_iff'.mpr hall)

/-- Dense finite sums with compact smooth time factors and physically compact
smooth spatial coefficients, in every real Sobolev order and finite q≥1. -/
theorem dense_span_physical_separated_sobolev (s : ℝ) (q : ℝ≥0∞)
    [IsFiniteMeasureOnCompacts μ] [Fact (1 ≤ q)] (hq : q ≠ ⊤) :
    Dense (Submodule.span ℝ {v : Lp (SobolevHilbert s) q μ |
      ∃ h ∈ ((weightedFourierLp s) ''
        {ψ : SchwartzMap NavierStokes.ProblemStatement.Space ℂ |
          HasCompactSupport (ψ : NavierStokes.ProblemStatement.Space → ℂ)}),
      ∃ g : Lp ℝ q μ,
        (∃ a : ℝ → ℝ, g =ᵐ[μ] a ∧ HasCompactSupport a ∧ ContDiff ℝ ∞ a) ∧
        v = separatedLp q h g} : Set (Lp (SobolevHilbert s) q μ)) :=
  dense_span_separatedLp q hq (dense_compact_weightedFourierLp s)
    (Lp.dense_hasCompactSupport_contDiff hq)

end NSFormalization.Paper3
