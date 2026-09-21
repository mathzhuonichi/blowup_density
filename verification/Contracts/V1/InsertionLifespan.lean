import Contracts.V1.InsertionFamily

/-! Lifespan data used by the whole-space gluing theorem.

The reference force belongs to the prescribed force class and is regular
through the end of the reference interval. The record stores the resulting
strict reference-lifespan bound and the exact lifespan of each inserted
solution. The current full-horizon record extends this structure. -/

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
  `referenceLifespan` of `research/section4/STATEMENTS.md:333`. -/
  referenceLifespan :
    ENNReal.ofReal (family.T + family.margin) <
      Data.maximalLifespanR ν family.a family.g
  /-- `T^nu_{max,R}(a, g_eps) = T`, the first display of
  `paper/sections/04-whole-space.tex:34` (`research/section4/STATEMENTS.md:347`).
 -/
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
