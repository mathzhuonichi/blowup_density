import NSFormalization.Section4.A01.ConvectionDivergence
import NSFormalization.Section4.A02.SolutionClass

/-!
# A01 unit E1, harvested: `projected` holds for every `ClassicalSolutionR`

With unit E1 (`Section4/A01/ConvectionDivergence.lean`) in hand, the projected
forced equation of `research/A01/Spec.lean`'s `ManuscriptLocalRegularity.projected`
field (`:214`) is a **theorem about any `ClassicalSolutionR`** — it needs no
transport from any mild/strong source, only the structure's own `velocity_smooth`,
`divergence` and `momentum` fields plus the lane's
`navierStokesResidual_eq_iff_projected`.

This means `ManuscriptLocalRegularity.projected` is not a separate A01 obligation:
it is discharged by whatever produces the `ClassicalSolutionR` (units c7/B2 of
`research/A01/A01_SPLIT.md`).

The proof was written by the lane-093 reviewer (`research/A01/REVIEW_SPLIT.md`,
Finding 3) and is copied here with credit; the differentiability extraction
follows the reviewer's probe 3 recipe.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02

/-- **`ManuscriptLocalRegularity.projected` is free.**  For every classical
whole-space solution `u` of `eq:NS` at viscosity `ν` with force `f`, the
projected forced equation `∂ₜu − νΔu = (f − ∇·(u⊗u)) − ∇p` holds at every
interior time.  A theorem, not an obligation: it follows from `velocity_smooth`
(differentiability in space), `divergence` (`∇·u = 0`) and `momentum`
(eq:NS in the `(u·∇)u + ∇p` form) through unit E1's
`navierStokesResidual_eq_iff_projected`.

Reviewer harvest, `research/A01/REVIEW_SPLIT.md` Finding 3. -/
theorem projected_of_classicalSolution
    (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      temporalDerivative u.velocity t x - ν • spatialLaplacian u.velocity t x =
        (f (t, x) - convectionDivergence u.velocity t x)
          - pressureGradient u.pressure t x := by
  intro t ht x
  -- `velocity_smooth` gives spatial differentiability at the interior point.
  have hopen : IsOpen (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)) :=
    isOpen_Ioo.prod isOpen_univ
  have hsub : Ioo (0 : ℝ) T ×ˢ (univ : Set Space) ⊆ Ico (0 : ℝ) T ×ˢ (univ : Set Space) :=
    Set.prod_mono Ioo_subset_Ico_self subset_rfl
  have hmem : ((t, x) : SpaceTime) ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set Space) :=
    ⟨ht, Set.mem_univ _⟩
  have hdiff2 : DifferentiableAt ℝ u.velocity (t, x) :=
    ((u.velocity_smooth.mono hsub).differentiableOn (by simp)).differentiableAt
      (hopen.mem_nhds hmem)
  have hspace : DifferentiableAt ℝ (fun y : Space => u.velocity (t, y)) x :=
    hdiff2.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  -- `divergence` and `momentum` are the remaining two inputs.
  have hdiv : spatialDivergence u.velocity t x = 0 :=
    u.divergence t (Ioo_subset_Ico_self ht) x
  have hmom : NavierStokesR3.ProblemStatement.navierStokesResidual ν u.velocity u.pressure t x
      = f (t, x) := u.momentum t ht x
  exact (navierStokesResidual_eq_iff_projected ν u.velocity u.pressure t x (f (t, x))
    hspace hdiv).mp hmom

end NSFormalization.Section4.A01
