import Contracts.V2.InsertionLifespan
import Bindings.InsertionLifespan

/-! The implementation layer for the version-two lifespan contract
`R42.insertion_lifespan_v2`.

`Contracts.V2.InsertionLifespan.InsertionLifespanV2API` extends
`Contracts.V1.InsertionLifespan.InsertionLifespanAPI` by the three exports the
version-one review named as owed (`research/R42/REVIEW_CONTRACT.md:443-452`).  All
three are already proved in `Bindings/InsertionLifespan.lean` (lane 098):

* `solution` is `Bindings.InsertionLifespan.sol_fullHorizon`
  (`Bindings/InsertionLifespan.lean:319`) verbatim;
* `maximal` is `Bindings.InsertionLifespan.isMaximalSolution_of_inserted`
  (`Bindings/InsertionLifespan.lean:349`) verbatim;
* `blowup_limsup` is the one line the version-one binding runs *inside*
  `lifespan_upper` (`Bindings/InsertionLifespan.lean:215-217`) — the tree lemma
  `NSFormalization.Section4.R42.limsupLeft_speedENorm_eq_top` applied to
  `family.blowup` and the slice continuity from `family.velocity_smooth` — lifted
  here to a standalone theorem `blowup_essSup` so the field can name it.

So this file has two jobs.

* `blowup_essSup` states the essential-supremum blow-up as a standalone theorem
  (version one kept it as a `have` inside `lifespan_upper`).
* `insertionLifespanV2API` inhabits the version-two record.  It reuses the frozen
  version-one witness `insertionLifespanAPI F hg hreg` with `{ … with … }` and
  fills the three new fields with the three theorems above.  It takes the **same
  two hypotheses** `hg`/`hreg` as version one and no more; `sol_fullHorizon` and
  `blowup_essSup` need neither hypothesis, and `isMaximalSolution_of_inserted`
  needs only `hg` (through `lifespan_eq`), so no new hypothesis is introduced.

The two restated blow-up operators `limsupLeft`/`speedENorm` bridge to the
`Section4/A02` copies by `rfl` (`Bindings/MaximalPartial.lean:57,61`), which is why
`blowup_essSup` closes by the same direct term the version-one `lifespan_upper`
uses; no new bridge is owed.  The full-horizon `Data.ClassicalSolutionR` and the
`IsMaximalSolution` predicate go through the field-by-field conversions already in
`Bindings.InsertionLifespan`.

Every declaration carries the `BlowupDensity.Bindings.InsertionLifespan` namespace,
reopened from the version-one binding; `sol_fullHorizon`,
`isMaximalSolution_of_inserted`, `insertionLifespanAPI` are visible there directly. -/

noncomputable section

namespace BlowupDensity.Bindings.InsertionLifespan

open Set
open BlowupDensity.Contracts.V1
open scoped ENNReal

variable {ν : ℝ} {P : PacketAPI ν} (F : InsertionFamilyAPI ν P) {ε : ℝ}

/-! ## 1. `blowup_essSup` — the displayed essential-supremum blow-up

The second display of Theorem 4.2, `limsup_{t↑T}‖u_ε(t)‖_∞ = ∞`
(`04-whole-space.tex:35`), stated in the frozen `Contracts.V1.MaximalPartial`
vocabulary.  Version one produces exactly this term as `have hblow` inside
`lifespan_upper` (`Bindings/InsertionLifespan.lean:215-217`); here it is a
standalone theorem so `blowup_limsup` can name it.  The pointwise `family.blowup`
and the slice continuity from `family.velocity_smooth` feed lane 080's
`limsupLeft_speedENorm_eq_top`; its `A02.limsupLeft`/`A02.speedENorm` conclusion is
definitionally the contract's `MaximalPartial.limsupLeft`/`speedENorm`
(`Bindings/MaximalPartial.lean:57,61`, both `rfl`). -/
theorem blowup_essSup (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
    Contracts.V1.MaximalPartial.limsupLeft F.T
        (fun t => Contracts.V1.MaximalPartial.speedENorm
          (fun x : Space => F.velocity ε (t, x))) = ⊤ :=
  NSFormalization.Section4.R42.limsupLeft_speedENorm_eq_top (F.blowup ε hε)
    (NSFormalization.Section4.R42.continuous_slice_of_velocity_smooth
      (F.velocity_smooth ε hε))

/-! ## 2. `insertionLifespanV2API` — the registered version-2 inhabitant

Reuses the frozen version-one witness `insertionLifespanAPI F hg hreg`
(`Bindings/InsertionLifespan.lean:271`) through `{ … with … }` — so every
version-one field, including `memForce`/`regular` and the two lifespan clauses, is
inherited unchanged — and fills the three new fields with `sol_fullHorizon`,
`isMaximalSolution_of_inserted` and `blowup_essSup`.  The hypothesis list is
exactly version one's `hg`/`hreg`. -/
def insertionLifespanV2API (hg : Data.MemForceR F.g)
    (hreg : Data.RegularThrough ν F.a F.g (F.T + F.margin)) :
    Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P :=
  { insertionLifespanAPI F hg hreg with
    solution := fun _ε hε => sol_fullHorizon F hε
    maximal := fun _ε hε => isMaximalSolution_of_inserted F hg hε
    blowup_limsup := fun _ε hε => blowup_essSup F hε }

/-- Regression guard (lane-092 review finding 5): the five clauses of the
version-2 record are about the **given** family `F`, not a substituted one. -/
theorem insertionLifespanV2API_family (hg : Data.MemForceR F.g)
    (hreg : Data.RegularThrough ν F.a F.g (F.T + F.margin)) :
    (insertionLifespanV2API F hg hreg).family = F := rfl

end BlowupDensity.Bindings.InsertionLifespan
