import Contracts.V1.InsertionFamily

/-! Stable specification for the **two lifespan clauses of Theorem 4.2**
(`thm:Rinsert`, `paper/sections/04-whole-space.tex:31-43`) that the family
contract `R42.insertion_family` deliberately omits.

Task `collaboration/tasks/R42.md`, graph node `R42`.  This is a **new
contract id** (`R42.insertion_lifespan`), not a version 2 of
`R42.insertion_family`: that family record is proved and stays untouched
(`Contracts/V1/InsertionFamily.lean`).  This record adds only the two
maximal-lifespan clauses, packaged with the two manuscript hypotheses they
consume.

## What is fixed (the two lifespan clauses, with the paper they come from)

* `lifespan` — `T^nu_{max,R}(a, g_eps) = T` for every `eps ∈ (0, eps0]`, the
  first display of `paper/sections/04-whole-space.tex:34`
  (`research/section4/STATEMENTS.md:347`).  The inserted force has the same
  maximal `R³` lifespan `T` as the packet singular time.
* `referenceLifespan` — `T + delta < T^nu_{max,R}(a, g)`, the definite article
  of "*the* solution for `a ∈ X_R` and `g ∈ F_R`, regular through `T + delta`"
  (`paper/sections/04-whole-space.tex:32`;
  `research/section4/STATEMENTS.md:333`).

Both clauses are stated exactly as the frozen, unregistered 3-field
`Contracts.V1.InsertionLifespanAPI`
(`Contracts/V1/InsertionFamily.lean:421-436`) already states them; the two
fields `referenceLifespan` and `lifespan` are token-identical to that
structure's.  This record differs from it only by carrying, as *fields*, the
two hypotheses the proof consumes, so a downstream consumer (R47 needs
`g ∈ F_R`) can re-use them:

* `memForce : Data.MemForceR family.g` — the reference force is in `F_R`
  (`04-whole-space.tex:32`).  `Data.ClassicalSolutionR` carries no force-class
  field and `g_eps − g ∈ C_c^∞` alone cannot give it
  (`Contracts/V1/DatumLemmas.lean:378-381`), so this must be carried; it enters
  only the upper bound of `lifespan`.
* `regular : Data.RegularThrough ν family.a family.g (family.T + family.margin)`
  — the reference is regular through `T + delta`
  (`04-whole-space.tex:32`, `02-preliminaries.tex:34-36`).
  `InsertionFamilyAPI.reference` is only a solution on the half-open
  `[0, T+delta)`, which gives `≤`, not the strict `<`; `RegularThrough` supplies
  a solution past `T + delta`.  It enters only `referenceLifespan`.

## Supersedes the frozen 3-field structure — new consumers must qualify the name

This record **supersedes** the frozen 3-field
`Contracts.V1.InsertionLifespanAPI` (`Contracts/V1/InsertionFamily.lean:421-436`),
whose own docstring predates the registration of A02 and is now stale: it says
the two clauses are unproved and need "task `A02` … which has no contract yet",
but `A02.maximal_partial` and `A02.maximal_partial_v2` are registered and both
clauses are proved (`Bindings.InsertionLifespan.{referenceLifespan, lifespan_eq}`).
Being frozen, that file cannot be corrected, so the correction lives here.

The two structures share the short name `InsertionLifespanAPI`.  Under the
customary `open BlowupDensity.Contracts.V1` (which the binding and any consumer
write), a **bare** `InsertionLifespanAPI` resolves to the frozen, unregistered
3-field one.  New consumers of the registered contract must therefore write the
qualified `InsertionLifespan.InsertionLifespanAPI` (this 5-field record); the
sub-namespace follows `MaximalPartial` / `EnergyAbsorptionPartial`.

## What is derived, not carried (lane 092, `research/R42/REVIEW_BINDING.md`
findings 1, 2)

Four things that look like hypotheses are determined by the ambient contracts
and are therefore **not** fields:

* `0 < ν` = `P.viscosity_pos` (`Contracts/V1/Packet.lean:199`; `P` is a
  parameter of this structure);
* `family.a ∈ Data.initialClassR` (`X_R`), derived from `family.reference` at
  `t = 0` (`Bindings.InsertionLifespan.initialClassR_a`);
* `0 < family.T` = `CorrectionAPI.time_pos`, `0 < family.margin` =
  `CorrectionAPI.margin_pos`;
* the essential-supremum blow-up of the inserted velocity, derived from
  `family.blowup` and `family.velocity_smooth`.

The `blowup` clause is consumed inside the proof in the registered **pointwise**
`Contracts.V1.SpeedUnboundedAt` form (`family.blowup`) and re-expressed in
`speedENorm` there; this record asserts nothing new about it.

## Self-containedness

Only `Contracts.V1.InsertionFamily` is imported, hence transitively
`Contracts.V1.{Scaling, Correction, Packet, Data, Thresholds}`.  Every notion
used — `InsertionFamilyAPI`, `PacketAPI`, `Data.maximalLifespanR`,
`Data.RegularThrough`, `Data.MemForceR` — is defined in those contracts; this
file copies none of them and needs no new `rfl` bridge.  No field is a
hypothesis about an unspecified proposition, and no field is `True`,
`∃ x, True` or any similar placeholder. -/

noncomputable section

namespace BlowupDensity.Contracts.V1.InsertionLifespan

open Set
open BlowupDensity.Contracts.V1
open scoped ENNReal

/-- The two lifespan clauses of Theorem 4.2 (`thm:Rinsert`,
`paper/sections/04-whole-space.tex:31-43`) for one inserted `eps`-family,
packaged with the two manuscript hypotheses (`g ∈ F_R`, regular through
`T + delta`) they consume.

The lifespan clauses of `research/section4/STATEMENTS.md:333,347` that
`InsertionFamilyAPI` omits, now provable through the registered
`A02.maximal_partial` and `D01.datum_lemmas` interfaces (see
`verification/Bindings/InsertionLifespan.lean`). -/
structure InsertionLifespanAPI (ν : ℝ) (P : PacketAPI ν) where
  /-- The inserted family whose lifespan the two clauses below describe;
  the registered `R42.insertion_family` record
  (`Contracts/V1/InsertionFamily.lean`). -/
  family : InsertionFamilyAPI ν P
  /-- `g ∈ F_R`: the reference force is in the whole-space force class of
  `paper/sections/04-whole-space.tex:32`.  Not a consequence of the family
  record (`Contracts/V1/DatumLemmas.lean:378-381`); enters only the upper bound
  of `lifespan`. -/
  memForce : Data.MemForceR family.g
  /-- "*The* solution ... regular through `T + delta`",
  `paper/sections/04-whole-space.tex:32`, `02-preliminaries.tex:34-36`:
  `Data.RegularThrough ν a g (T + delta)`, a classical solution on some
  `[0, T + delta + delta')`.  Strictly stronger than
  `InsertionFamilyAPI.reference` (only `[0, T+delta)`), which is why it is needed
  for the strict inequality in `referenceLifespan`. -/
  regular : Data.RegularThrough ν family.a family.g (family.T + family.margin)
  /-- "*The* solution for `a` in `X_R` and `g` in `F_R`, regular through
  `T + delta`", `paper/sections/04-whole-space.tex:32`; the field
  `referenceLifespan` of `research/section4/STATEMENTS.md:333`.  Token-identical
  to the frozen `Contracts.V1.InsertionLifespanAPI.referenceLifespan`. -/
  referenceLifespan :
    ENNReal.ofReal (family.T + family.margin) <
      Data.maximalLifespanR ν family.a family.g
  /-- `T^nu_{max,R}(a, g_eps) = T`, the first display of
  `paper/sections/04-whole-space.tex:34` (`research/section4/STATEMENTS.md:347`).
  Token-identical to the frozen `Contracts.V1.InsertionLifespanAPI.lifespan`. -/
  lifespan : ∀ ε ∈ Ioc (0 : ℝ) family.ε₀,
    Data.maximalLifespanR ν family.a (family.force ε) =
      ENNReal.ofReal family.T

/-! ## The existential form consumed downstream -/

/-- What `R41D`, `R46` and `R47` receive from R42's lifespan clauses, in the
shape of `insertionFamilyStatement` (`Contracts/V1/InsertionFamily.lean:381`):
given an inserted family `F` with reference force in `F_R` and reference regular
through `T + delta`, the two lifespan clauses hold for that very family, i.e.
there is an `InsertionLifespanAPI` whose `family` is `F`.

`A.family = F` is an equation, not an existential: the clauses are about the
**given** family, not a substituted one (lane-092 review finding 5).  The two
hypotheses `Data.MemForceR F.g` and `Data.RegularThrough ν F.a F.g (F.T +
F.margin)` mirror `insertionFamilyStatement`'s explicit hypotheses; `0 < ν` and
`F.a ∈ Data.initialClassR` are derived inside the binding, not assumed.

Introducing this definition asserts nothing. -/
def insertionLifespanStatement : Prop :=
  ∀ (ν : ℝ) (P : PacketAPI ν) (F : InsertionFamilyAPI ν P),
    Data.MemForceR F.g →
    Data.RegularThrough ν F.a F.g (F.T + F.margin) →
      ∃ A : InsertionLifespanAPI ν P, A.family = F

end BlowupDensity.Contracts.V1.InsertionLifespan
