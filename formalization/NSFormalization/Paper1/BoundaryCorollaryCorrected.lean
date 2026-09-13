import NSFormalization.Paper1.BoundaryCorollary

/-!
# Conditional interface for the bounded-domain corollary

The manuscript-shaped theorem in `BoundaryCorollary` has two missing bridges:
its support hypothesis does not imply separation from the boundary, and its
force limit is not the background-difference norm.  This file records the
corrected conditional interface without asserting either analytic bridge.
-/
noncomputable section
namespace NSFormalization.Paper1.BoundaryCorollary

open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal
open NavierStokes NavierStokes.ProblemStatement

/-- Interior support is separated from the boundary. -/
theorem disjoint_frontier_of_subset_interior
    {Ω B : Set Space} (hBinterior : B ⊆ interior Ω) :
    ∀ x ∈ B, x ∉ frontier Ω := by
  intro x hxB hxfront
  exact (disjoint_interior_frontier.le_bot ⟨hBinterior hxB, hxfront⟩)

/-- Corrected analytic insertion contract.  The fields are explicit because
local existence, the actual velocity/pressure witnesses, support control, and
force convergence are logically independent obligations. -/
structure InteriorNoSlipInsertionContract
    {Ω : Set Space} {ν T δ : ℝ} {a : Space → Space}
    {v : VelocityField} {π : PressureField} {g : VelocityField}
    (B : Set Space) (U : ℝ → VelocityField)
    (G : ℝ → VelocityField) : Prop where
  support_interior : B ⊆ interior Ω
  flow : ∀ ε, 0 < ε → BoundedFlow Ω ν a (G ε) T
  velocity_boundary : ∀ ε, 0 < ε → ∀ t ∈ Icc (0 : ℝ) T,
    ∀ x ∈ frontier Ω, U ε (t, x) = 0
  supported_difference : ∀ ε, 0 < ε → ∀ t ∈ Ico (0 : ℝ) T,
    tsupport (fun x => U ε (t, x) - v (t, x)) ⊆ B
  force_difference_tendsto : ∀ s : ℝ, s < (1 : ℝ) / 2 →
    Tendsto (fun ε : ℝ => domainForceNorm Ω s (G ε - g))
      (𝓝[>] 0) (𝓝 0)

/-- The corrected conclusion follows by projection from the explicit contract.
The `G ε - g` limit is the background-difference norm. -/
theorem corrected_interior_noSlip_insertion
    {Ω : Set Space} {ν T δ : ℝ} {a : Space → Space}
    {v : VelocityField} {π : PressureField} {g : VelocityField}
    {B : Set Space} {U : ℝ → VelocityField} {G : ℝ → VelocityField}
    (hcontract : InteriorNoSlipInsertionContract (Ω := Ω) (ν := ν) (T := T)
      (δ := δ) (a := a) (v := v) (π := π) (g := g) B U G) :
    (B ⊆ interior Ω) ∧
      (∀ ε, 0 < ε → BoundedFlow Ω ν a (G ε) T) ∧
      (∀ ε, 0 < ε → ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ frontier Ω,
        U ε (t, x) = 0) ∧
      (∀ ε, 0 < ε → ∀ t ∈ Ico (0 : ℝ) T,
        tsupport (fun x => U ε (t, x) - v (t, x)) ⊆ B) ∧
      (∀ s : ℝ, s < (1 : ℝ) / 2 →
        Tendsto (fun ε : ℝ => domainForceNorm Ω s (G ε - g))
          (𝓝[>] 0) (𝓝 0)) := by
  exact ⟨hcontract.support_interior, hcontract.flow,
    hcontract.velocity_boundary, hcontract.supported_difference,
    hcontract.force_difference_tendsto⟩

end NSFormalization.Paper1.BoundaryCorollary
