import Contracts.V2.InsertionLifespan

/-!
# R41D reconciled specification: the density branch of Theorem 4.1

Theorem 4.1(i), `thm:Rmain`, is stated at
`paper/sections/04-whole-space.tex:7-13` and proved at `:176-179`.  The force
class replacements are `cor:Rclasses`, `:183-195`.  This is graph node `R41D`,
with proof dependency `R42`; comparison and risk decisions are recorded in
`research/R41D/COMPARISON.md` and `research/R41D/RECONCILIATION.md`.

This file reconciles the two blind drafts.  It adopts Draft B's canonical
`Data.breakdownSetIn` spelling for the relative breakdown set, and Draft A's
class-parameterized record and typed proof split.  The latter is part of the
frozen R41D interface: the task card requires the witness to be the reference
itself in the first case and an aligned R42 witness in the second.  It also
preserves the manuscript's assertion that the earlier history and energy
conclusions come from the same insertion family (`04-whole-space.tex:13,179`).

There are two fields rather than a `q`-indexed field.  Thus the sharp
specializations of `s_q = 2/q - 3/2` remain literal:

* `L^1_t H^s_x` with `s < 1/2`;
* `L^2_t H^s_x` with `s < -1/2`.

Both fields visibly use the required order

    forall a in X_R, forall g in Y, forall positive radius, exists f.

The force norms are the full-time, `ENNReal`-valued
`Contracts.V1.Data.forceSobolevENormL1` and `forceSobolevENormL2`
(`Contracts/V1/Data.lean:225-236`).  The result uses
`Data.breakdownSetIn Y nu a T` (`Data.lean:672-674`), hence the approximant is
in the same relative class and has `T_max <= T`.

## R42 object retained by the second branch

`R42InsertedWitness` existentially packages one
`Contracts.V2.InsertionLifespan.InsertionLifespanV2API`.  Its inherited
version-one fields are the same `InsertionFamilyAPI` together with
`memForce`, `regular`, `referenceLifespan`, and `lifespan`
(`Contracts/V1/InsertionLifespan.lean:108-137`).  The family itself supplies
one `force`, `initial`, `history`, `forceDifference_compact`, `energyRate`, and
`forceConvergence` (`Contracts/V1/InsertionFamily.lean:125-327`).  Version two
also retains the full-horizon `solution`, `maximal`, and `blowup_limsup`
(`Contracts/V2/InsertionLifespan.lean:117-158`).

The equalities below align that one family with the surrounding `a`, `g`, and
`T`, and select the same `epsilon` for the returned force and its norm bound.
The explicit margin clauses pin the second case of the proof at
`04-whole-space.tex:177`; the exact-lifespan clause pins the stronger R42
conclusion from `:34`, which implies membership in the theorem's breakdown set.

This is a specification only: two concrete definitions and one structure, with
no mathematical proof declarations and no abstract proposition field.
-/

noncomputable section

namespace BlowupDensity.R41D.Draft

open Set
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-! ## 0. The allowed relative force classes -/

/-- The three ambient smooth force classes for which the subcritical density
argument is frozen.

`forceClassR` is the class of Theorem 4.1 (`04-whole-space.tex:8`), while
`forceClassCompact` and `forceClassRapid` are `F_c` and `F_rd`
(`:183-195`).  A single set `Y` is threaded through the reference quantifier
and `breakdownSetIn`, so the topology and the returned witness cannot silently
use different force classes. -/
def IsR41DForceClass (Y : Set SpaceTimeField) : Prop :=
  Y = forceClassR ∨ Y = forceClassCompact ∨ Y = forceClassRapid

/-! ## 1. The nontrivial branch's aligned R42 witness -/

/-- The witness selected in the second case of the density proof
(`paper/sections/04-whole-space.tex:177`) from one registered R42 V2 family.

The selected `epsilon` lies in the family's common range `(0, epsilon_0]` and
`f` is exactly that family's force.  The family is aligned with the R41D datum
`(nu,a,g,T)`.  Its positive margin and inherited `regular` /
`referenceLifespan` fields record that the reference exists strictly beyond
`T`; `forceDifference_compact` is the class-preservation input; and `lifespan`
gives `T_max(a,f) = T`.  Because the entire V2 record is retained, its
`initial`, `history`, `energyRate`, and `forceConvergence` clauses concern this
same family and this same selected parameter (`04-whole-space.tex:13,179`). -/
def R42InsertedWitness (nu T : ℝ) (a : SpatialField)
    (g f : SpaceTimeField) : Prop :=
  ∃ (P : PacketAPI nu)
    (L : BlowupDensity.Contracts.V2.InsertionLifespan.InsertionLifespanV2API nu P)
    (epsilon : ℝ),
      L.family.a = a ∧
      L.family.g = g ∧
      L.family.T = T ∧
      epsilon ∈ Ioc (0 : ℝ) L.family.ε₀ ∧
      f = L.family.force epsilon ∧
      0 < L.family.margin ∧
      RegularThrough nu a g (T + L.family.margin) ∧
      ENNReal.ofReal (T + L.family.margin) < maximalLifespanR nu a g ∧
      MemForceCompact (fun z => f z - g z) ∧
      maximalLifespanR nu a f = ENNReal.ofReal T

/-! ## 2. The subcritical density contract -/

/-- Theorem 4.1(i), the subcritical density direction, parameterized by the
ambient relative force class.

`forceClass` restricts `Y` to `F_R`, `F_c`, or `F_rd`
(`paper/sections/04-whole-space.tex:8,183-195`).  Each conclusion is the
epsilon-ball expansion of relative density, not an opaque topology predicate,
and each carries the mandated split from `:176-177`.

All proposition fields are fully spelled in registered `Contracts` vocabulary.
In particular, no sibling proof theorem is copied as a structure field. -/
structure RDensityAPI (Y : Set SpaceTimeField) where
  /-- The selected ambient class is exactly one of the three manuscript
  classes.  Keeping this as a field makes `RDensityAPI Y` impossible to use for
  an unrelated or accidentally empty ambient set. -/
  forceClass : IsR41DForceClass Y

  /-- The `L^1_t H^s_x` branch (`04-whole-space.tex:8-13,176-177`).

  For `s < 1/2`, every `a in X_R`, reference `g in Y`, and positive radius has
  an approximant in `breakdownSetIn Y`.  The final disjunction makes the proof
  split part of the witness: if the reference already has `T_max <= T`, the
  approximant is literally `g`; otherwise `T < T_max` and the approximant is
  selected from one aligned `InsertionLifespanV2API`.  Its
  `InsertionFamilyAPI.forceConvergence` field is consumed at `q = 1`. -/
  densityL1 :
    ∀ nu : ℝ, 0 < nu →
      ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < (1 : ℝ) / 2 →
          ∀ a : SpatialField, a ∈ initialClassR →
            ∀ g : SpaceTimeField, g ∈ Y →
              ∀ radius : ℝ≥0∞, 0 < radius →
                ∃ f : SpaceTimeField,
                  f ∈ breakdownSetIn Y nu a T ∧
                  forceSobolevENormL1 s (f - g) < radius ∧
                  ((maximalLifespanR nu a g ≤ ENNReal.ofReal T ∧ f = g) ∨
                    (ENNReal.ofReal T < maximalLifespanR nu a g ∧
                      R42InsertedWitness nu T a g f))

  /-- The `L^2_t H^s_x` branch (`04-whole-space.tex:8-13,176-177`).

  This is the same class-relative result and the same
  `forall a, forall g, forall radius, exists f` order, with the sharp strict
  threshold `s < -1/2` and the full-time `forceSobolevENormL2` distance.  The
  inserted arm retains the same R42 fields as `densityL1`, now consuming
  `InsertionFamilyAPI.forceConvergence` at `q = 2`; its inherited `lifespan`
  still gives singularity exactly at `T`. -/
  densityL2 :
    ∀ nu : ℝ, 0 < nu →
      ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < -(1 : ℝ) / 2 →
          ∀ a : SpatialField, a ∈ initialClassR →
            ∀ g : SpaceTimeField, g ∈ Y →
              ∀ radius : ℝ≥0∞, 0 < radius →
                ∃ f : SpaceTimeField,
                  f ∈ breakdownSetIn Y nu a T ∧
                  forceSobolevENormL2 s (f - g) < radius ∧
                  ((maximalLifespanR nu a g ≤ ENNReal.ofReal T ∧ f = g) ∨
                    (ENNReal.ofReal T < maximalLifespanR nu a g ∧
                      R42InsertedWitness nu T a g f))

end BlowupDensity.R41D.Draft
