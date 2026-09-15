import Contracts.V1.Data
import Contracts.V1.InsertionFamily
import Contracts.V1.InsertionLifespan
import Contracts.V2.InsertionLifespan

/-!
# R41D blind specification draft B: the subcritical density branch of Theorem 4.1

Task `collaboration/tasks/R41D.md`, graph node `R41D` (consumer of `R42`).
Statement: Theorem 4.1(i), `thm:Rmain`,
`paper/sections/04-whole-space.tex:7-13`; density proof `:176-177`.  The ambient
force-class parameter also records the two replacements asserted by
`cor:Rclasses`, `:183-195`, as required by `PLAN.md` section 9.

This file is a **statement draft only**.  It contains one `def` and one
`structure`, proves nothing, and introduces no axiom, admitted term, native
decision procedure, or abstract proposition placeholder.  Every proposition is
spelled in the registered `Contracts.V1.Data` vocabulary.

## Literal content

For each of the two time exponents the theorem is expanded rather than hidden
behind `Data.RelativelyDense`.  After the fixed viscosity, horizon and Sobolev
order, the decisive binders are therefore visible in the task-card order

    forall a, forall g, forall positive radius, exists f.

The witness belongs to `Data.breakdownSetIn Y nu a T`; hence it both remains in
the selected relative ambient class `Y` and satisfies
`Data.maximalLifespanR nu a f <= ENNReal.ofReal T`.  Its distance from the
reference is the full-time Bochner norm of the physical difference `f - g`,
using `Data.forceSobolevENormL1` or `Data.forceSobolevENormL2`.

## The proof split pinned by the task card

The fields below state the density conclusion, not a proof hypothesis.  Their
intended implementation must nevertheless preserve the manuscript's split
(`04-whole-space.tex:176-177`):

* if `Data.maximalLifespanR nu a g <= ENNReal.ofReal T`, choose `f = g`;
* otherwise choose a positive amount of reference lifespan beyond `T` and use
  the **same** inserted family exported by R42.  The R42 projections consumed
  by that branch are
  `Contracts.V1.InsertionFamilyAPI.force`,
  `InsertionFamilyAPI.forceDifference_compact`, and
  `InsertionFamilyAPI.forceConvergence`, together with the inherited
  `Contracts.V1.InsertionLifespan.InsertionLifespanAPI.regular`,
  `.referenceLifespan`, and `.lifespan` fields of
  `Contracts.V2.InsertionLifespan.InsertionLifespanV2API`.

Here `.lifespan` gives the stronger second-case conclusion
`T_max(a,g_eps) = T` (`04-whole-space.tex:34`), while the theorem's breakdown
set only asks for `T_max(a,g_eps) <= T`.  `forceConvergence` supplies the
arbitrarily small radius at precisely the two subcritical thresholds.  The
compact-difference field is what makes the same proof reusable for each of the
three ambient classes once its elementary class-closure instance is supplied.

## Blindness record

This draft was prepared without opening, grepping, or searching any other R41D
draft, any pre-existing `research/R41D/` file, another worktree, or an R41D
entry in `research/section4/STATEMENTS.md`.  Its mathematical inputs were the
paper passages named above, the task card, the listed registered contracts,
`PLAN.md` section 9's force-subclass note, and the permitted R43 file-shape
template.
-/

noncomputable section

namespace BlowupDensity.R41D.DraftB

open Set
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-! ## 0. The three manuscript ambient force classes -/

/-- The permitted value of the relative ambient force class.

`forceClassR` is `F_R` from `02-preliminaries.tex:16-25` and the ambient class
of Theorem 4.1 (`04-whole-space.tex:8`).  `forceClassCompact` and
`forceClassRapid` are `F_c` and `F_rd` from `04-whole-space.tex:183-192`, for
which `:194-195` says that the same thresholds remain valid.  Keeping `Y`
explicit ensures that `breakdownSetIn Y` and the reference-force quantifier use
one and the same relative class. -/
def IsR41DForceClass (Y : Set SpaceTimeField) : Prop :=
  Y = forceClassR ∨ Y = forceClassCompact ∨ Y = forceClassRapid

/-! ## 1. The subcritical density contract -/

/-- **Theorem 4.1(i), subcritical direction**, parameterized by its manuscript
ambient force class (`paper/sections/04-whole-space.tex:7-13,183-195`).

The two fields spell out the two values of `q` separately so the stated
thresholds `1/2` and `-1/2` (`04-whole-space.tex:13`) and the task-card
quantifier order are visible in the type.  The structure carries no proof
machinery as hypotheses: R42 is a proof dependency, documented above and in the
field docstrings, not an extra rider on the manuscript theorem. -/
structure RDensityAPI where
  /-- **The `L^1_t H^s_x` branch** (`04-whole-space.tex:8-10,13,176-177`).

  For every allowed relative class `Y`, every fixed `nu,T > 0`, and every
  `s < 1/2`, the binders are literally `forall a in X_R`, `forall g in Y`,
  `forall r > 0`, `exists f`.  The witness condition
  `f in breakdownSetIn Y nu a T` uses `Data.breakdownSetIn` from
  `Contracts.V1.Data`: it expands to `f in Y` and
  `Data.maximalLifespanR nu a f <= ENNReal.ofReal T`.  The distance is
  `Data.forceSobolevENormL1 s (f - g)`, the registered spelling of
  `L^1(0,infinity;H^s(R^3))`.

  In the first case of `:176-177`, the implementation must use `f = g`.  In the
  second it consumes `InsertionFamilyAPI.force`,
  `InsertionFamilyAPI.forceConvergence` at `q = 1`,
  `InsertionFamilyAPI.forceDifference_compact`, and the inherited
  `InsertionLifespanV2API.regular`, `.referenceLifespan`, and `.lifespan` for
  that same R42 family. -/
  densityL1 :
    ∀ Y : Set SpaceTimeField, IsR41DForceClass Y →
      ∀ ν : ℝ, 0 < ν →
        ∀ T : ℝ, 0 < T →
          ∀ s : ℝ, s < 1 / 2 →
            ∀ a : SpatialField, a ∈ initialClassR →
              ∀ g : SpaceTimeField, g ∈ Y →
                ∀ r : ℝ≥0∞, 0 < r →
                  ∃ f : SpaceTimeField,
                    f ∈ breakdownSetIn Y ν a T ∧
                      forceSobolevENormL1 s (f - g) < r

  /-- **The `L^2_t H^s_x` branch** (`04-whole-space.tex:8-10,13,176-177`).

  This is the same relative-density proposition and the same visible
  `forall a, forall g, forall radius, exists f` order as `densityL1`, now for
  `s < -1/2`.  `Data.forceSobolevENormL2 s (f - g)` is the registered
  `L^2(0,infinity;H^s(R^3))` distance; `Data.breakdownSetIn Y` again uses the
  one selected force class and the canonical maximal lifespan.

  The first proof case again takes `f = g`.  The insertion case consumes the
  same R42 family, now using `InsertionFamilyAPI.forceConvergence` at `q = 2`,
  together with `InsertionFamilyAPI.force`,
  `.forceDifference_compact`, and the inherited
  `InsertionLifespanV2API.regular`, `.referenceLifespan`, and `.lifespan`.
  Thus the force is within the prescribed `L^2_t H^s_x` radius and has maximal
  lifespan exactly `T`, as `04-whole-space.tex:34,42` require. -/
  densityL2 :
    ∀ Y : Set SpaceTimeField, IsR41DForceClass Y →
      ∀ ν : ℝ, 0 < ν →
        ∀ T : ℝ, 0 < T →
          ∀ s : ℝ, s < -(1 / 2) →
            ∀ a : SpatialField, a ∈ initialClassR →
              ∀ g : SpaceTimeField, g ∈ Y →
                ∀ r : ℝ≥0∞, 0 < r →
                  ∃ f : SpaceTimeField,
                    f ∈ breakdownSetIn Y ν a T ∧
                      forceSobolevENormL2 s (f - g) < r

end BlowupDensity.R41D.DraftB
