import Contracts.V2.InsertionLifespan

/-!
# R41D draft specification A: subcritical density branch of Theorem 4.1

Task `R41D`, Theorem 4.1(i) (`thm:Rmain`,
`paper/sections/04-whole-space.tex:7-13`) and the force-subclass extension
`cor:Rclasses` (`:182-195`).  The mathematical dependency is Theorem 4.2,
represented here by the registered records
`Contracts.V1.InsertionFamilyAPI` and
`Contracts.V2.InsertionLifespan.InsertionLifespanV2API`.

This file is a **blind specification draft only**.  It contains definitions and
one structure, proves nothing, and introduces no `axiom`, `sorry`,
`native_decide`, or abstract proposition placeholder.  Its only mathematical
sources are the cited manuscript passages and the registered contract objects.

## Exact conclusion and quantifier order

For fixed `nu > 0`, `T > 0`, and a subcritical Sobolev order, the fields below
quantify in the task-card order

    forall a in X_R, forall g in Y, forall r > 0, exists f.

Here `Y` is a parameter of the record and `forceSubclass` restricts it to
exactly `F_R`, `F_c`, or `F_rd`.  The witness belongs to the same `Y`, has
`T_max(a,f) <= T`, and lies inside the requested relative force-norm ball.
The two fields are separated so that the manuscript's thresholds are literal:
`s < 1/2` for `L1_t H^s_x`, and `s < -1/2` for `L2_t H^s_x`
(`04-whole-space.tex:8-13`).

## The proof split is part of the witness

The proof of Theorem 4.1 (`04-whole-space.tex:176-179`) specifies which witness
is used.  If `T_max(a,g) <= T`, the witness is `g` itself.  Otherwise the
reference lives past `T`; one chooses a positive margin and applies Theorem 4.2.
`R42InsertedWitness` records that the second witness comes from one registered
R42 V2 family, aligned with the same `nu`, `a`, `g`, and `T`.

The alignment exposes the precise R42 fields used by the density assembly:

* `L.regular` and `L.referenceLifespan`, after
  `L.family.scaling.correction.margin_pos`, record the positive margin beyond
  `T`;
* `L.family.forceConvergence` supplies an `eps` small enough for the prescribed
  `L^q_t H^s_x` radius;
* `L.family.forceDifference_compact` gives the compact correction used to stay
  inside `F_R`, `F_c`, or `F_rd` (`04-whole-space.tex:195,198`);
* `L.lifespan` gives `T_max(a,g_eps) = T`;
* the same family also carries `L.family.initial`, `L.family.history`, and
  `L.family.energyRate`, the strengthened assertions mentioned at
  `04-whole-space.tex:13,179`.

The final three items are not replaced by weaker local predicates: the witness
below existentially packages the registered
`InsertionLifespanV2API`, so all of those fields concern the same inserted
family and the same `eps`.

## Contract vocabulary

`Data.initialClassR` is `X_R`; `Data.forceClassR`,
`Data.forceClassCompact`, and `Data.forceClassRapid` are `F_R`, `F_c`, and
`F_rd`; `Data.maximalLifespanR` is `T^nu_{max,R}`; and
`Data.forceSobolevENormL1` / `Data.forceSobolevENormL2` are the norms inducing
the two relative topologies.  The breakdown condition is written directly as
`maximalLifespanR nu a f <= ENNReal.ofReal T`, exactly the membership condition
in `Data.breakdownSetIn Y nu a T` (`02-preliminaries.tex:38-44`).
-/

noncomputable section

namespace BlowupDensity.R41D.DraftA

open Set
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-! ## 1. The R42 witness used in the nontrivial branch -/

/-- The inserted witness used in the second case of the density proof
(`paper/sections/04-whole-space.tex:177`), expressed through the exact
registered R42 V2 object.

`L.family.a`, `L.family.g`, and `L.family.T` align the R42 family with the
datum currently quantified by R41D.  The selected `eps` is in R42's common
range `(0, eps0]`, and `f` is exactly `L.family.force eps`.

The remaining conjuncts spell out the R42 projections consumed downstream:
positive `L.family.margin` and `L.regular` give a reference beyond `T`;
`L.referenceLifespan` makes that strict at the maximal-lifespan level;
`L.family.forceDifference_compact` supplies the compact perturbation; and
`L.lifespan` gives singularity exactly at `T`.  The radius inequality is kept
in the two density fields because its time exponent and Sobolev order differ;
the `eps` satisfying it is selected using `L.family.forceConvergence`. -/
def R42InsertedWitness (ν T : ℝ) (a : SpatialField)
    (g f : SpaceTimeField) : Prop :=
  ∃ (P : PacketAPI ν)
    (L : BlowupDensity.Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P)
    (ε : ℝ),
      L.family.a = a ∧
      L.family.g = g ∧
      L.family.T = T ∧
      ε ∈ Ioc (0 : ℝ) L.family.ε₀ ∧
      f = L.family.force ε ∧
      0 < L.family.margin ∧
      RegularThrough ν a g (T + L.family.margin) ∧
      ENNReal.ofReal (T + L.family.margin) < maximalLifespanR ν a g ∧
      MemForceCompact (fun z => f z - g z) ∧
      maximalLifespanR ν a f = ENNReal.ofReal T

/-! ## 2. The subcritical density contract -/

/-- Theorem 4.1(i), the **subcritical density direction**, parameterized by the
ambient smooth force subclass `Y`.

`forceSubclass` restricts `Y` to the three manuscript choices (`F_R`, `F_c`,
`F_rd`; `04-whole-space.tex:183-195`).  Both density fields use the order
`forall a, forall g, forall radius, exists f` required by the R41D task card.
Every field is a concrete proposition over registered `Contracts` objects.
-/
structure RDensityAPI (Y : Set SpaceTimeField) where
  /-- `04-whole-space.tex:8,16,183-195`: the relative topology is taken on one
  of the three smooth force classes.  These are exactly
  `Data.forceClassR = F_R`, `Data.forceClassCompact = F_c`, and
  `Data.forceClassRapid = F_rd` from `Contracts.V1.Data`. -/
  forceSubclass :
    Y = forceClassR ∨ Y = forceClassCompact ∨ Y = forceClassRapid

  /-- Theorem 4.1(i) for `q = 1` (`04-whole-space.tex:8-13,176-177`): for
  every `a in X_R`, every reference `g in Y`, and every positive radius, if
  `s < 1/2` there is `f` in the same relative force class with breakdown by
  `T` and `L1_t H^s_x` distance below the radius.

  The last disjunction is the manuscript's prescribed split.  Its first arm
  uses `g` itself.  Its second arm packages the exact R42 family and consumes
  `InsertionFamilyAPI.forceConvergence` at `q = 1`,
  `InsertionFamilyAPI.forceDifference_compact`, and the inherited
  `InsertionLifespanAPI.regular`, `referenceLifespan`, and `lifespan` fields of
  `InsertionLifespanV2API`. -/
  subcriticalL1 :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ, s < (1 : ℝ) / 2 →
      ∀ a : SpatialField, a ∈ initialClassR →
        ∀ g : SpaceTimeField, g ∈ Y →
          ∀ r : ℝ≥0∞, 0 < r →
            ∃ f : SpaceTimeField,
              f ∈ Y ∧
              maximalLifespanR ν a f ≤ ENNReal.ofReal T ∧
              forceSobolevENormL1 s (fun z => f z - g z) < r ∧
              ((maximalLifespanR ν a g ≤ ENNReal.ofReal T ∧ f = g) ∨
                (ENNReal.ofReal T < maximalLifespanR ν a g ∧
                  R42InsertedWitness ν T a g f))

  /-- Theorem 4.1(i) for `q = 2` (`04-whole-space.tex:8-13,176-177`): the
  same relative-density statement and the same `forall a, forall g, forall
  radius` order, now under the sharp subcritical hypothesis `s < -1/2` and in
  the `L2_t H^s_x` force norm.

  In the inserted arm the selected `eps` is obtained from the **same**
  `InsertionFamilyAPI.forceConvergence` field at `q = 2`; class preservation
  again uses `forceDifference_compact`, and singularity exactly at `T` uses
  the inherited `InsertionLifespanAPI.lifespan`.  The margin clauses are
  `InsertionLifespanAPI.regular` and `referenceLifespan` on that same family.
  Thus every conclusion in this `L2` arm concerns one insertion witness.
  -/
  subcriticalL2 :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ, s < -(1 : ℝ) / 2 →
      ∀ a : SpatialField, a ∈ initialClassR →
        ∀ g : SpaceTimeField, g ∈ Y →
          ∀ r : ℝ≥0∞, 0 < r →
            ∃ f : SpaceTimeField,
              f ∈ Y ∧
              maximalLifespanR ν a f ≤ ENNReal.ofReal T ∧
              forceSobolevENormL2 s (fun z => f z - g z) < r ∧
              ((maximalLifespanR ν a g ≤ ENNReal.ofReal T ∧ f = g) ∨
                (ENNReal.ofReal T < maximalLifespanR ν a g ∧
                  R42InsertedWitness ν T a g f))

end BlowupDensity.R41D.DraftA
