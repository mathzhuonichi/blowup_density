# Review — lane 092 (R42): Bindings assembly of the two lifespan clauses

Reviewer run: worktree `.claude/worktrees/092-R42-lifespan-binding`, commit `8823bcd`.
Files reviewed: `verification/Bindings/InsertionLifespan.lean`,
`research/R42/ATTEMPTS_BINDING.md`, `research/R42/axioms_binding.lean`.

## Verdict: **ACCEPT-WITH-NOTES**

The Lean is correct, silent, standard-3-axioms, and every gate is green.  Both
clauses of Theorem 4.2's lifespan are genuinely proved from the registered
contracts, the reuse discipline is exemplary, and the `sol_on_shorter` /
`lifespan_upper` / `referenceLifespan` routes are the right ones.

The **deliverable of this lane is the hypothesis list**, and that list is wrong in
one factual claim and over-sized by two entries.  Findings 1 and 2 are *blocking
for the V2 lane*, not for merging this file: the record says `hν` and `ha` cannot
be supplied by the ambient contracts, and both in fact can — I proved both in Lean
(commands below).  The V2 structure must be designed knowing this, or it will
carry two fields that its own parameters already determine.

Because the two surplus hypotheses are *also* the manuscript's own hypotheses
(`04-whole-space.tex:32` reads "for `a ∈ X_R` … and `ν > 0`"), keeping them is
statement-faithful, merely non-minimal — that is why this is ACCEPT-WITH-NOTES and
not REJECT.  Nothing here is unsound and nothing weakens the theorem.

---

## Findings

### 1. (MAJOR, record is factually false) `hν : 0 < ν` is `P.viscosity_pos`
**Location** `verification/Bindings/InsertionLifespan.lean:62-65, 162, 178, 198`;
`research/R42/ATTEMPTS_BINDING.md` hypothesis table, row `hν`
("structural; not a field").

`Contracts/V1/Packet.lean:199` is `viscosity_pos : 0 < ν`, a **field of
`PacketAPI ν`**.  `P : PacketAPI ν` is a parameter of `InsertionFamilyAPI ν P`
*and* of `InsertionLifespanAPI ν P`, so it is in scope at every use site.  The
module's own `variable` line already binds it.  Verified:

```lean
variable {ν : ℝ} {P : PacketAPI ν} (F : InsertionFamilyAPI ν P)
example : 0 < ν := P.viscosity_pos   -- compiles, exit 0
```

"structural; not a field" is simply not true, and it is the justification the V2
lane will read.

**Fix** replace the four occurrences of `hν` with `P.viscosity_pos` in
`lifespan_upper`/`lifespan_eq`/`insertionLifespan` (one token each), and correct
both the module docstring (`:62-65`) and the ATTEMPTS table.

### 2. (MAJOR, over-sized list) `ha : F.a ∈ Data.initialClassR` is derivable from `F.reference` in 12 lines, with a lemma already in the import closure
**Location** `InsertionLifespan.lean:66, 162, 178, 198`; `ATTEMPTS_BINDING.md`
row `ha` ("derivable in principle … but that is a separate M-item").

It is an **S-item, not an M-item**, and the route needs no new machinery.
`Data.initialClassR = {a | MemHInfty a ∧ IsSolenoidal a}` (`Data.lean:509`) and all
three conjuncts come off `F.reference` at `t = 0`:

* `ContDiff ℝ ∞ F.a` — `NSFormalization.Section4.D01.contDiff_slice`
  (`Section4/D01/DatumToJets.lean:366`) applied to `F.reference.velocity_smooth` at
  `t = 0 ∈ Ico 0 (T+δ)` (`F.reference.horizon_pos`), then `funext F.reference.initial`.
  **This lemma is already in this module's import closure** —
  `Bindings.DatumLemmas` (line 5) imports `NSFormalization.Section4.D01.DatumToJets`.
  (`LIFESPAN_SPLIT.md` item 4a proposed `NavierStokes.SpatialCurl.contDiff_spatialSlice`
  instead; `D01.contDiff_slice` is the in-closure one and is exactly this shape.)
* the datum at every order — `F.reference.sobolev m` at `t = 0`, witness `G 0`.
* `IsSolenoidal` — `F.reference.divergence 0 …`, plus `← funext F.reference.initial`
  under `simpa only [spatialDivergence, spatialDerivative]` (the divergence depends
  on `u` only through `fun y => u (0, y)`, which *is* `F.a`).

Verified, whole structure built from **two** hypotheses instead of four:

```lean
def insertionLifespan_twoHyp (hg : Data.MemForceR F.g)
    (hreg : Data.RegularThrough ν F.a F.g (F.T + F.margin)) :
    InsertionLifespanAPI ν P :=
  insertionLifespan F P.viscosity_pos (by refine ⟨⟨?_, ?_⟩, ?_⟩ ; …) hg hreg
```
`lake env lean /tmp/r42rev092/PP.lean` → exit 0, no errors, no warnings.

**Fix** add the derivation as a public lemma of this module
(`initialClassR_a : F.a ∈ Data.initialClassR`) and drop `ha` from the three
signatures; correct the ATTEMPTS row and `LIFESPAN_SPLIT.md`'s "S/M" for 4a to S.

### 3. (MINOR) unused import `NSFormalization.Section4.R42.Lifespan`
**Location** `InsertionLifespan.lean:8`.

Nothing from lane 072's `Lifespan.lean` is used: `memForceR_force` goes through the
registered `datumLemmas.memForceR_of_compact_difference` rather than
`R42.memForceR_insertedForce`, and `referenceLifespan` goes through
`maximalPartial.regularThrough_iff` rather than
`R42.lt_maximalLifespanR_of_regularThrough` (both choices are *correct*, see
Consistency below).  Verified: deleting line 8 leaves the file compiling silently
(`lake env lean /tmp/r42rev092/NoLifespanImport.lean`, exit 0, no output).

**Fix** delete line 8, or — better — say in the docstring that lane 072's two
`Lifespan.lean` lemmas were deliberately bypassed and why (the ATTEMPTS bridge
table item 5 already explains the `referenceLifespan` half; the `memForceR`
half is not explained anywhere).

### 4. (MINOR) the module leaves CI coverage the moment it is merged
**Location** `verification/lakefile.toml` (`defaultTargets = ["Tests", "Contracts"]`).

`Bindings/InsertionLifespan.lean` is the **only** `Bindings/*` module that no
`Tests/*` module imports (`ScalingNorms`/`ScalingEnergy` are reached through
`Bindings.Scaling`).  On *this* PR the CI step "Compile changed modules outside the
registered test closure" (`experiments/build_changed_lean.py`) does build it, but
after merge it is no longer "changed", so no CI job will ever rebuild it and it can
rot silently against `Bindings.MaximalPartial` / `Section4/R42/*` drift until the
V2 lane registers it.

**Fix** none required in this lane if the V2 lane follows immediately; otherwise
note it in `NEXT_SESSION.md` so the gap is deliberate and bounded.

### 5. (MINOR) no recorded `rfl` guard that `family` is `F`
**Location** `InsertionLifespan.lean:198-204`.

`insertionLifespan` does set `family := F`, so the two clauses *are* about the
given family and not a substituted one — I checked
`(insertionLifespan F hν ha hg hreg).family = F := rfl`, which holds.  But the
def's **type** records nothing, exactly the gap `Tests/InsertionFamily.lean` closes
for `insertionFamilyStatement` with its `⟨…, rfl, rfl⟩`.  One `example … := rfl`
in this module would pin it as a regression guard, for free.

### 6. (NOTE, no action) `hg` and `hreg` are genuinely necessary, and correctly stated
* `hg : Data.MemForceR F.g` — `Data.ClassicalSolutionR` has **no** force-class
  field, and `Contracts/V1/DatumLemmas.lean:378-381` says so in as many words
  ("`g ∈ F_R` is **not** a consequence of `Data.ClassicalSolutionR` … R42 must
  carry it as a hypothesis").  It enters only `lifespan_upper`, through
  `memForceR_force` into `lifespan_le_of_unbounded`'s `MemForceR f` slot.  It is
  the manuscript's `g ∈ F_R` (`04-whole-space.tex:32`).
* `hreg : Data.RegularThrough ν F.a F.g (F.T + F.margin)` — this is the right
  strength and the worker's explanation is right.  `Data.maximalLifespanR` is
  `⨆ S, ⨆ _ : Nonempty (ClassicalSolutionR ν a f S), ofReal S` (`Data.lean:657`), so
  `F.reference : ClassicalSolutionR … (T+δ)` (the **half-open** `[0,T+δ)`) gives only
  `ofReal (T+δ) ≤ maximalLifespanR` by `le_iSup₂` — the strict `<` needs a solution
  on some `S > T+δ`, which is exactly what `RegularThrough ν a g (T+δ)`
  (`Data.lean:664`: `∃ δ' > 0, Nonempty (ClassicalSolutionR ν a g (T+δ+δ'))`)
  supplies.  It is at least as strong as `STATEMENTS.md:332`'s closed
  `Icc 0 (T+δ)` and matches `02-preliminaries.tex:34`'s "extends smoothly to
  `[0,T+δ]`", i.e. the nested-margin reading `STATEMENTS.md` §2(v) O2 recommends.
  It enters only `referenceLifespan`.
* Both are in the contract's `Data` vocabulary, so a V2 structure carries them as
  fields with **no** bridge — as are `hν` and `ha`.  That part of the record is right.

### 7. (NOTE, no action) `lifespan_upper`'s blow-up really comes from `F.blowup`
`InsertionLifespan.lean:166-170` feeds `F.blowup ε hε` (the contract's **pointwise**
`Contracts.V1.SpeedUnboundedAt`, `InsertionFamily.lean` `blowup`) and
`continuous_slice_of_velocity_smooth (F.velocity_smooth ε hε)` into lane 080's
`limsupLeft_speedENorm_eq_top` (`Section4/R42/BlowupEssSup.lean:100`), whose only
two hypotheses are exactly those.  The `A02.limsupLeft`/`A02.speedENorm` conclusion
meets the contract shape through the two `rfl` bridges at
`Bindings/MaximalPartial.lean:57,61`, and `SpeedUnboundedAt` through
`Bindings/Scaling.lean:50`.  **No extra blow-up hypothesis anywhere.**  Also non-vacuous:
`lifespan_lower` forces `ofReal T ≤ maximalLifespanR` with `T > 0`, so the equality
is not the empty-supremum `0`.

---

## Check 2(a) — statement fidelity, `pp.fullNames`

Contract (`Contracts/V1/InsertionFamily.lean:421-436`), printed:

```
InsertionLifespanAPI.referenceLifespan (self) :
  ENNReal.ofReal (self.family.T + self.family.margin) <
    Data.maximalLifespanR ν self.family.a self.family.g
InsertionLifespanAPI.lifespan (self) :
  ∀ ε ∈ Set.Ioc 0 self.family.ε₀,
    Data.maximalLifespanR ν self.family.a (self.family.force ε) = ENNReal.ofReal self.family.T
```

Binding, printed:

```
Bindings.InsertionLifespan.referenceLifespan (F) :
  Data.RegularThrough ν F.a F.g (F.T + F.margin) →
    ENNReal.ofReal (F.T + F.margin) < Data.maximalLifespanR ν F.a F.g
Bindings.InsertionLifespan.lifespan_eq (F) {ε} :
  0 < ν → F.a ∈ Data.initialClassR → Data.MemForceR F.g →
    ε ∈ Set.Ioc 0 F.ε₀ → Data.maximalLifespanR ν F.a (F.force ε) = ENNReal.ofReal F.T
```

**Token-identical** under `self.family ↦ F`, conclusion for conclusion, with the
four hypotheses as the only difference.  Confirmed mechanically by the anonymous
constructor test in `/tmp/r42rev092/PP.lean` (the contract's two field types,
written out by hand, are inhabited by the two binding theorems — exit 0).

---

## Commands and results

| command (worktree; `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`; lake from `verification/`) | result |
|---|---|
| `bash scripts/lean-install.sh` | exit 0 (idempotent) |
| `lake build Bindings.InsertionLifespan` | `Build completed successfully (9969 jobs).` — matches ATTEMPTS' claim exactly; only pre-existing `Source/`,`Paper3/` linter warnings |
| `lake env lean Bindings/InsertionLifespan.lean` | **silent**, exit 0 |
| `lake env lean ../research/R42/axioms_binding.lean` | exit 0; 7 declarations, each `[propext, Classical.choice, Quot.sound]` |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats\|Formal\.' Bindings/InsertionLifespan.lean` | no match (exit 1) |
| `make check` | exit 0; architecture OK, `test_contract_policy.py` 13/13, `check_work_queue.py` "30 work items … consistent" |
| `make test` | exit 0; every registered contract "checked; standard logical axioms only" — **green** |
| `git show --stat HEAD` | 3 files, +332; `contracts.json` / `work_items.json` / `TASKS.md` untouched (correct — no registration in this lane) |
| `lake env lean /tmp/r42rev092/Scratch.lean` (findings 1,2) | exit 0, **no output** — `0 < ν := P.viscosity_pos` and `ha` both proved |
| `lake env lean /tmp/r42rev092/PP.lean` (fidelity + 2-hyp build) | exit 0, no errors, no warnings |
| `lake env lean /tmp/r42rev092/NoLifespanImport.lean` (finding 3) | exit 0, silent — import unused |
| `lake env lean /tmp/r42rev092/NoShow.lean` (ATTEMPTS bridge item 2) | **fails as claimed**: `rewrite failed … target is F.velocity ε (t,x) = (uniqueness_toA02 F.reference).velocity (t,x)` — the three `show`s **are** load-bearing |

## Check 3 — consistency

Clean.  The module uses the registered `maximalPartial` (`lifespan_ge_of_forall_shorter`,
`lifespan_le_of_unbounded`, `regularThrough_iff`) and `datumLemmas`
(`memForceR_of_compact_difference`), and the **existing** structure conversions
`uniqueness_toA02` / `maximalPartial_ofA02` (`Bindings/MaximalPartial.lean:73`) —
no new conversion, no new restated definition, no `Formal.*` import, nothing
re-derived.  Choosing `maximalPartial.regularThrough_iff` over lane 072's
`lt_maximalLifespanR_of_regularThrough` is **sound and strictly better**: 072's lemma
is literally `(A02.regularThrough_iff …).mp h` in `A02` vocabulary
(`Section4/R42/Lifespan.lean:219-223`), so routing through it would force composing
`maximalPartial_regularThrough_iff` *and* `maximalPartial_maximalLifespanR_eq` to get
back to `Data`; the registered field is already in `Data`.  ATTEMPTS bridge item 5
describes this correctly.

## Check 4 — honesty of ATTEMPTS

Honest, with the two exceptions in findings 1 and 2.  Everything else I opened
checks out: the three cited declarations
(`classicalSolutionR_of_inserted` `SolutionOnShorter.lean:74`,
`limsupLeft_speedENorm_eq_top` `BlowupEssSup.lean:100`,
`continuous_slice_of_velocity_smooth` `BlowupEssSup.lean:141`) have exactly the
hypotheses claimed; `0 < T` / `0 < margin` are `CorrectionAPI.time_pos`
(`Correction.lean:202`) and `margin_pos` (`:207`) as claimed; the single recorded
iteration (the `Variable name ε is not explicitly referenced` linter on the
`lifespan := fun ε hε` field binder) **reproduced verbatim** in my own scratch when I
wrote that binder without the underscore; and the "the `show` is load-bearing"
warning to future simplifiers is correct, as the `NoShow` run above shows.  The
command table's numbers (9969 jobs, 13/13 policy tests, 30 work items) all match
what I got.

---

## Proposed V2 contract shape (for the next lane)

Register `R42.insertion_lifespan`, version 1 of a **new** id (not a V2 of
`R42.insertion_family` — the family contract is proved and must stay untouched):

```lean
-- verification/Contracts/V2/InsertionLifespan.lean   (or V1/, it is a new id)
structure InsertionLifespanAPI (ν : ℝ) (P : PacketAPI ν) where
  family     : InsertionFamilyAPI ν P
  memForce   : Data.MemForceR family.g                                  -- g ∈ F_R, 04:32
  regular    : Data.RegularThrough ν family.a family.g
                 (family.T + family.margin)                             -- "regular through T+δ", 04:32
  referenceLifespan : ENNReal.ofReal (family.T + family.margin)
                        < Data.maximalLifespanR ν family.a family.g     -- 04:32
  lifespan   : ∀ ε ∈ Ioc (0:ℝ) family.ε₀,
                 Data.maximalLifespanR ν family.a (family.force ε)
                   = ENNReal.ofReal family.T                            -- 04:34

/-- What R41D/R46/R47 consume, in the shape of `insertionFamilyStatement`. -/
def insertionLifespanStatement : Prop :=
  ∀ (ν : ℝ) (P : PacketAPI ν) (F : InsertionFamilyAPI ν P),
    Data.MemForceR F.g →
    Data.RegularThrough ν F.a F.g (F.T + F.margin) →
      ∃ A : InsertionLifespanAPI ν P, A.family = F
```

**Two carried hypotheses, not four.**  `hν` comes from `P.viscosity_pos` (finding 1)
and `ha` from `family.reference` (finding 2); putting either in the structure adds a
field the parameters already determine.  Keep `memForce` and `regular` as *fields*
rather than as arguments of the statement only, so that a consumer holding an
`InsertionLifespanAPI` can re-use them (R47 needs `g ∈ F_R`); the `Prop`-level
`insertionLifespanStatement` then takes them as hypotheses, mirroring
`insertionFamilyStatement`'s `R`/`hv`/`hp`.

Registered contracts it carries: `R42.insertion_family` (through the `family`
field — no new copy of anything), and transitively `I01.packet`, `I02.correction`,
`I03.scaling`.  The *binding* additionally consumes `A02.maximal_partial` and
`D01.datum_lemmas`, but the contract states nothing from them, so the registry
`scope` should say: "the two lifespan clauses of Theorem 4.2 for the registered
inserted family, under the manuscript's `g ∈ F_R` and regular-through-`T+δ`
hypotheses; `a ∈ X_R` and `ν > 0` are derived, not assumed; the blow-up clause is
consumed in the registered pointwise `SpeedUnboundedAt` form and re-expressed in
`speedENorm` inside the proof."

`Tests/InsertionLifespan.lean` should check, on the model of
`Tests/InsertionFamily.lean`:

1. `theorem checkedInsertionLifespan : Contracts.V2.insertionLifespanStatement :=
   fun _ν _P F hg hreg => ⟨Bindings.insertionLifespan F hg hreg, rfl⟩` — the final
   `rfl` is the anti-substitution guard of finding 5: the clauses are about the
   **given** family;
2. `run_cmd TestSupport.checkAxioms ``checkedInsertionLifespan` — the standard
   3-axiom audit;
3. one `example` per clause writing the two conclusions out **by hand** from the
   manuscript (`ofReal (T+δ) < maximalLifespanR ν a g`, and
   `maximalLifespanR ν a (force ε) = ofReal T` for `ε ∈ Ioc 0 ε₀`) and discharging
   them from the record, so a later edit to the structure cannot silently weaken
   either display;
4. and — because this is what the lane learned — one `example : 0 < ν := P.viscosity_pos`
   and one `example (A : InsertionLifespanAPI ν P) : A.family.a ∈ Data.initialClassR`,
   pinning that the two dropped hypotheses stay derivable.

Registering it also closes finding 4: the module enters the `Tests` closure and CI
rebuilds it on every run.
