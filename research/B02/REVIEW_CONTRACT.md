# B02 contract registration (lane 099) — contract review

Reviewer: opus, 2026-09-13.  Branch `erenup/099-B02-partial-contract` at `d463d4c`
(merge-base with `origin/erenup/integration` = `6306264`).  CONTRACT lane: strict
statement fidelity, all gates run by the reviewer in the lane worktree.

## Verdict: **ACCEPT-WITH-NOTES**

All 16 propositional fields and the 9 restated spec-local `def`s are **token-for-token
identical** to `research/B02/Spec.lean` (mechanically diffed, not eyeballed — see §3).
The excluded/included partition is exactly right, both of `REVIEW_REMAINING.md` §5's
hard requirements are met, every gate is green, and no frozen file is touched.
The four notes below are documentation/registry wording only; **none blocks the merge
and none requires a change to a Lean statement**.  Note 2 is the only one I would
actually spend a commit on, and only because `Contracts/V1` freezes on merge.

---

## 1. Findings

### F1 — (minor, registry wording) `homogeneousDatumSub` is a second frozen copy of an already-registered statement
*Location: `verification/Contracts/V1/HomogeneousPartial.lean:336-342`, vs
`verification/Contracts/V1/DatumLemmas.lean:458-465` (`D01.datum_lemmas`, already
registered and frozen).*

`D01.datum_lemmas`'s `isHomogeneousSliceDatum_sub` is the **same proposition** as
this contract's `homogeneousDatumSub`: same four hypotheses, same conclusion, same
order of binders.  The only textual difference is that `DatumLemmas` writes
`Integrable (fun x => ψ x * ((z x i : ℝ) : ℂ))` and `HomogeneousPartial` writes the
same with an explicit `volume`; `Integrable`'s measure is an autoparam that
elaborates to `volume`, so the two elaborate to the identical term.  The B02
implementation side confirms the relation: `Section4/B02/LebesgueDatum.lean:446`
`isHomogeneousSliceDatum_sub_of_integrable` is a **one-line re-export** of
`Section4/D01/HomogeneousWitness.lean:585 isHomogeneousSliceDatum_sub`, which is
what `D01.datum_lemmas` already binds.

This is **not** a defect: `research/B02/Spec.lean:490` lists the field as a `B02`
obligation, and `REVIEW_REMAINING.md` §5's first hard requirement presupposes
registering it.  It is redundancy, and the project now has two V1-frozen copies of
one statement to keep in sync.

*Fix (optional, registry-only, no Lean change):* one sentence in the
`contracts.json` `scope` saying that `homogeneousDatumSub` is the same proposition
as `D01.datum_lemmas`'s `isHomogeneousSliceDatum_sub`, re-exported into the `B02`
shape so a `B02` consumer need not also depend on `D01.datum_lemmas`.

A weaker version of the same observation applies to `lebesgueHomogeneousDatum`
vs `DatumLemmas.lean:425-430 compact_exists_homogeneousDatum`, but there the two
are genuinely **different** statements (B02: `L¹ ∩ L²` fields, `SplitRange s`;
D01: `C_c^∞` fields, `-3/2 < s` only), so neither implies the other and no note is
needed beyond F2.

### F2 — (minor, prose, worth fixing before the freeze) the `lebesgueHomogeneousDatum` docstring describes the wrong hypothesis
*Location: `Contracts/V1/HomogeneousPartial.lean:298-299` ("applied to a smooth
compactly supported real vector field"), and the same phrasing in the
`contracts.json` scope ("a smooth compact field has an order-s homogeneous datum").*

The Lean statement's hypothesis is `MemLp k 1 volume → MemLp k 2 volume` together
with `SplitRange s` — **not** compact support.  `Spec.lean:452-453` opens with the
same sentence but closes the docstring with the clarifier the contract drops:
"Hypothesis `L¹ ∩ L²` rather than compact support, for the reason recorded in
`lowHighSplit`."  The distinction is load-bearing for exactly the reason
`lowHighSplit`'s own docstring gives: the field it is applied to at
`04-whole-space.tex:249` is `(1−χ_R)h_n`, which is Schwartz with **unbounded**
support.  The statement is correct and token-identical to the spec; only a reader
of the contract in isolation could be misled.

*Fix:* restore the Spec's closing sentence to the field docstring, and change
"a smooth compact field" to "an `L¹ ∩ L²` field" in the `scope`.  Since
`Contracts/V1` freezes on merge, this is the last cheap moment.

### F3 — (nit, verified correct as written) the conformance list names 7 of the 8 `axioms_*.lean` files
*Location: `Bindings/HomogeneousPartial.lean:24` and the `contracts.json` scope,
both listing `axioms_{u1,u2_sl3,u34,u6,u7,u8,remaining}`.*

`research/B02/axioms_u2.lean` is omitted.  I checked: its own header says unit 2
was incomplete when it was written ("SL3 reality + SL4 … remain … so there is no
spec-field `example` yet"); it audits sub-lemma axioms only and carries **no**
spec-field conformance `example`.  `axioms_u2_sl3.lean` is the file that carries
the `annularSchwartz` spec-field example.  The omission is therefore correct, not
an oversight.  **No action.**

### F4 — (nit, informational) the stage-1 chaining step is not a contract field
*Location: `Section4/B02/Cutoff.lean:376`.*

`annularRestriction` concludes `IsAnnularRestriction δ R A Z`; `annularSmoothing`
consumes `IsAnnularSupported δ R Z`.  The implication that links them exists only
as a `have hZsupp : IsAnnularSupported δ R0 Z := by …` **inside** the proof of
`spatialApproxHomogeneous_of` — there is no named theorem, so nothing could have
been registered.  `Spec.lean:186-188` already notes the implication holds for every
`A`.  Harmless for `R46`, which consumes the combined `spatialApproxHomogeneous`
and never runs stage 1 by hand; recorded so a future consumer who wants the two
stage-1 fields separately knows it must reprove the link.  **No action.**

### F5 — (nit, informational) `REVIEW_REMAINING.md` N1's suggestion was not taken, harmlessly
N1 suggested the contract lane bind `temporalApprox` straight at
`Section4.B01.temporalApprox` and keep the `B02` copy as documentation.  The lane
binds `Section4.B02.temporalApprox` instead (`Bindings/HomogeneousPartial.lean:125`).
Since `Remaining.lean:101-109` is literally `theorem temporalApprox … :=
NSFormalization.Section4.B01.temporalApprox`, the two choices produce the **same
proof term**; nothing is weakened.  The restated type in `Remaining.lean` remains
the hand-synced copy N1 flagged, which is a `formalization/` concern, not this
lane's.  **No action.**

---

## 2. Gates (all run by the reviewer, in
`/data_8T/ping/blowup_density/.claude/worktrees/099-B02-partial-contract`, after
`bash scripts/lean-install.sh` → exit 0, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`)

| command | result |
|---|---|
| `cd verification && lake build Tests.HomogeneousPartial` | `Build completed successfully (9898 jobs).` |
| ↳ axiom line | `Tests/HomogeneousPartial.lean:15:0: Contract BlowupDensity.Tests.checkedHomogeneousPartial: checked; standard logical axioms only` |
| `make check` | 13/13 contract-policy tests OK; `30 work items: ownership, contract registration and task cards consistent.`; `registered_contracts: 18` |
| `make test` | every registered contract (18) `checked; standard logical axioms only`, including `checkedHomogeneousPartial` |
| `make test-mutations` | `implementation_refactor: accepted`; `admitted_proof: rejected as required`; `extra_axiom: rejected as required`; `weakened_hypothesis: rejected as required`; `Mutation suite passed.` |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | exit 0, `registered_contracts: 18`, `base_compatibility_checked: true` |
| `bash scripts/gates.sh Tests.HomogeneousPartial` | `== gates OK` |

Structural checks:

* **Contract import policy.** `Contracts/V1/HomogeneousPartial.lean:1-2` imports
  exactly `Contracts.V1.Data` and `Contracts.V1.BochnerPartial` — nothing else.
  Transitive closure of `Contracts.V1.HomogeneousPartial` = `{Data, BochnerPartial,
  itself}` ∪ Mathlib.
* **No `Formal.*` in the Tests closure.** I walked the transitive `import` graph of
  `Tests.HomogeneousPartial` over `verification/`, `formalization/` and
  `vendor/NavierStokesAndEuler/`: 1411 modules, **zero** whose root segment is
  `Formal`; the only unresolved roots are `Mathlib` and `Lean`.  The `Section4`
  modules in the closure are exactly `B02.{Annular,AnnularReal,AnnularSchwartz,
  Cutoff,LebesgueDatum,LowFrequency,LowHigh,Remaining}` plus
  `B01.{Compact,Separated,Temporal}`.  `warningAsError` is respected — the Tests
  build emits no warning of its own (the deprecation warnings in the log are from
  `NSFormalization.Paper3.*`, a different Lake lib).
* **Frozen files untouched.**
  `git diff origin/erenup/integration --stat -- verification/Contracts/V1 verification/Tests`
  → only `Contracts/V1/HomogeneousPartial.lean` (+391) and
  `Tests/HomogeneousPartial.lean` (+17), both new.  Same against the merge-base.
* **No `sorry` / `admit` / `axiom` / `native_decide`** in any of the three new files.
* **Registry merge.** `contracts.json` on integration has 17 entries; this branch
  appends `B02.homogeneous_partial` as the 18th.  Pure append → trivial three-way
  merge.  `work_items.json` records the registration exactly as 091/096 did
  (`"contracts": ["B02.homogeneous_partial"]`), with `TASKS.md` / `tasks/B02.md`
  regenerated by `tasks.py render` and nothing hand-edited.
* **Tests module shape** is character-for-character the shape of
  `Tests/BochnerPartial.lean` (import triple, `noncomputable section`, the `def
  checked… : …API := Bindings.…`, `run_cmd TestSupport.checkAxioms`).

---

## 3. Statement fidelity — field by field

Method: I extracted every field body from `research/B02/Spec.lean`'s
`HomogeneousApproxAPI` and from `Contracts/V1/HomogeneousPartial.lean`'s
`HomogeneousApproxPartialAPI` programmatically (docstrings and comments stripped),
normalised whitespace and the single namespace rewrite
`BlowupDensity.Contracts.V1.BochnerPartial.separatedPath → separatedPath`, and
compared the token streams.  **All 17 fields (16 propositional + the data field `χ`)
compare identical; `annularPathApprox`, `separatedAssembly`, `approxCompactHomogeneous`
are the only spec fields absent; no field appears in the contract that is not in the
spec.**  Every `Spec.lean:NNN` line reference in the contract was checked against the
file and is exact.

| # | field | vs `Spec.lean` | discharged by (`NSFormalization.Section4.B02.…`) | could a wrong implementation satisfy it? |
|---|---|---|---|---|
| — | `χ : Space → ℝ` | `:278` identical (data field) | `NavierStokesR3.ComparisonCutoffs.baseCutoff` | it is data, pinned by the four `chi_*` fields below and *used* by `cutoffLebesgue`; not free |
| 1 | `chi_smooth` | `:280` identical | `chi_smooth` (Remaining) | no — `ContDiff ℝ ∞ χ` on the same `χ` the structure carries |
| 2 | `chi_one` | `:282` identical | `chi_one` (Remaining) | no — forces `χ ≡ 1` on the closed unit ball, so `χ ≢ 0` |
| 3 | `chi_vanishes` | `:285` identical | `chi_vanishes` (Remaining) | no — forces `χ = 0` for `‖x‖ ≥ 2`, so `χ ≢ 1`; this is what stops `cutoffLebesgue` from being vacuous |
| 4 | `chi_range` | `:287` identical | `chi_range` (Remaining) | no |
| 5 | `annularRestriction` | `:302` identical | `annularRestriction` (Annular:240) | no — `IsAnnularRestriction` pins `Ẑ` a.e. to the indicator of `Â`; `0 < δ < R` and `‖Z − A‖ₑ < η` for **every** `η > 0` |
| 6 | `annularSmoothing` | `:314` identical | `annularSmoothing` (Annular:337) | no — hypothesis `IsAnnularSupported` is inhabited (stage 1 produces it, `Cutoff.lean:376`), conclusion demands a genuine `C_c^∞(R³∖{0})` datum with `0 < δ' < δ < R < R'` |
| 7 | `annularSchwartz` | `:362` identical | `annularSchwartz` (AnnularReal:205) | no — hypothesis inhabited by field 6; and `IsHomogeneousSliceDatum` is not trivially satisfiable, since `D01`'s `isHomogeneousSliceDatum_unique` pins the datum of a slice at every real `s` |
| 8 | `lowFrequencyIntegrable` | `:370` identical | `lowFrequencyIntegrable` (LowFrequency:56) | no — a concrete `IntegrableOn` |
| 9 | `lowFrequencyIntegral` | `:378` identical | `lowFrequencyIntegral` (LowFrequency:67) | no — a numeric equality `= 4π`, so the Bochner integral cannot be the totalised `0` |
| 10 | `fourierSupBound` | `:397` identical | `fourierSupBound` (LowFrequency:124) | no — hypothesis `MemLp k 1` makes `∫‖k‖` honest rather than totalised; the constant is exactly `(2π)^{-3/2}` of `01-introduction.tex:91` (verified against the source line), and the **vector** form avoids the spurious factor 3 |
| 11 | `lowHighSplit` | `:421` identical | `lowHighSplit` (LowHigh:200), `SplitRange` unpacked as `hs.1`/`hs.2` | no — LHS is `Data.homogeneousFourierENorm` (the literal Fourier integral, `Data.lean:410`), RHS constant is `lowHighConstant s` written out; `MemLp` hypotheses keep both `eLpNorm`s finite; the high-frequency coefficient is `1`, as in the display at `:246-247` |
| 12 | `lebesgueHomogeneousDatum` | `:454` identical | `lebesgueHomogeneousDatum` (LebesgueDatum:405), `SplitRange` unpacked | no — the second clause quantifies over **every** datum `G`, which is strictly stronger than an existence claim and is what replaces a uniqueness lemma downstream.  See F2 on the docstring |
| 13 | `homogeneousDatumSub` | `:490` identical (**integrability-carrying form**) | `isHomogeneousSliceDatum_sub_of_integrable` (LebesgueDatum:446) | no; and the hypothesis-free form — which is **false** — appears nowhere in the contract (grepped: the contract's only occurrence of the unhypothesised shape is inside the ⚠ prose).  See §4 |
| 14 | `cutoffLebesgue` | `:513` identical | `cutoffLebesgue` (Cutoff:225) | no — the implementation's statement is literally `scaledCutoff baseCutoff …`, i.e. it is tied to the structure's own `χ`.  A junk `χ ≡ 1` would make this field trivial but is excluded by `chi_vanishes`; a junk `χ ≡ 0` is excluded by `chi_one` |
| 15 | `spatialApproxHomogeneous` | `:539` identical | `spatialApproxHomogeneous` (AnnularReal:225, unconditional) | no — this is the strongest field: physical `C_c^∞(R³;R³)` density in `Ḣ^s` measured by the datum norm, for arbitrary `A` and arbitrary `η > 0` |
| 16 | `temporalApprox` | `:563` identical after the one namespace normalisation | `temporalApprox` (Remaining:101) `= Section4.B01.temporalApprox` | no — token-identical to the already-registered `Contracts/V1/BochnerPartial.lean:132-138` field |

### The nine restated spec-local `def`s

All nine bodies are **character-identical** to `Spec.lean:155-237` (mechanically
diffed).  Each has exactly **one** definition in the tree — I grepped
`formalization/` for `^def <name>` and every name resolves to a single site
(`Annular.lean:60,63,67,75,81`, `Cutoff.lean:53,57,273,276`) — so there is no second
copy for a bridge to point at by accident.

| def | contract | impl | bridge | used in the discharging theorem's statement? |
|---|---|---|---|---|
| `frequencyAnnulus` | `:145` | `Annular.lean:60` | `homogeneousPartial_frequencyAnnulus_eq` | yes (through `IsAnnularRestriction`/`IsAnnularSupported`) |
| `closedFrequencyAnnulus` | `:150` | `Annular.lean:63` | `…_closedFrequencyAnnulus_eq` | yes (through `IsAnnularDatum`) |
| `IsAnnularDatum` | `:155` | `Annular.lean:67` | `…_isAnnularDatum_eq` | yes — `annularSmoothing`'s conclusion, `annularSchwartz`'s hypothesis |
| `IsAnnularRestriction` | `:163` | `Annular.lean:75` | `…_isAnnularRestriction_eq` | yes — `annularRestriction`'s conclusion |
| `IsAnnularSupported` | `:170` | `Annular.lean:81` | `…_isAnnularSupported_eq` | yes — `annularSmoothing`'s hypothesis |
| `scaledCutoff` | `:178` | `Cutoff.lean:53` | `…_scaledCutoff_eq` | yes — `cutoffLebesgue` |
| `schwartzVector` | `:184` | `Cutoff.lean:57` | `…_schwartzVector_eq` | yes — `annularSchwartz`, `cutoffLebesgue` |
| `lowHighConstant` | `:191` | `Cutoff.lean:276` | `…_lowHighConstant_eq` | yes — `lowHighSplit` (unfolded to its body there; defeq) |
| `SplitRange` | `:197` | `Cutoff.lean:273` | `…_splitRange_eq` | yes — `spatialApproxHomogeneous`; `lowHighSplit`/`lebesgueHomogeneousDatum` take the two halves |

Not restated, correctly reused rather than copied: `SpatialField`,
`IsHomogeneousSliceDatum`, `IsHomogeneousPath`, `homogeneousFourierENorm`,
`MemBochnerDatum`, `bochnerDatumENorm`, `MemForceCompact`, `forceClassCompact`,
`forceTimeMeasure` from `Contracts.V1.Data`; `separatedPath` from
`Contracts.V1.BochnerPartial`.  **Nothing already in `Data.lean` or
`BochnerPartial.lean` is restated a second time.**

### `temporalApprox` and the shared `separatedPath`

`Contracts/V1/BochnerPartial.lean:85-87`'s `separatedPath` is character-identical to
`Spec.lean:217-219`'s, so using it in field 16 is reuse, not a variant.  The
implementation chain is `Bindings.homogeneousPartial.temporalApprox :=
Section4.B02.temporalApprox`, and `Remaining.lean:109` gives
`Section4.B02.temporalApprox := Section4.B01.temporalApprox` — the same proof term
`B01` is bound to.  The `rfl` bridge `Contracts.V1.BochnerPartial.separatedPath =
Section4.B01.separatedPath` already exists at `Bindings/BochnerPartial.lean:52-54`;
re-bridging it here would have been a duplicate, and the field assignment
typechecking *is* the defeq check.  `χ := NavierStokesR3.ComparisonCutoffs.baseCutoff`
is the same vendor object `Bindings/BochnerPartial.lean:66` binds, so a joint
`B01`+`B02` consumer sees **one** cutoff, as `REVIEW_REMAINING.md` §5 asked.

### The three "minor mismatches resolved by defeq" (`ATTEMPTS_CONTRACT.md` §Mismatches)

All three are real and all three are harmless.

1. `schwartzVector`'s return type: contract `SpatialField`, module `Space → Space`.
   `Data.lean:99` is `abbrev SpatialField := Space → Space`, so they are the same
   term after unfolding; the `rfl` bridge is genuine.
2. **`SplitRange` packing does not weaken the field.**  The contract field's
   hypothesis is `SplitRange s`, exactly what `Spec.lean:421,454,539` writes.  The
   *implementation* theorems take the two halves separately, and the binding
   supplies `hs.1 : -3/2 < s` and `hs.2 : s ≤ 0` from the packed conjunction.  The
   direction is "contract hypothesis → implementation hypotheses", i.e. the contract
   assumes *more* than either half alone and the implementation is applied to it —
   the field is therefore no weaker than the spec's, and cannot be, since the two
   statements are token-identical.  (`SplitRange s` unfolds to
   `-3 / 2 < s ∧ s ≤ 0`, matching `lowHighSplit`'s `hs`/`hs0` exactly.)
   `lebesgueHomogeneousDatum`'s `s` is implicit in the module, hence the `_s` binder;
   no information is lost.
3. `temporalApprox`'s `separatedPath` namespace: covered above.

### Paper cross-check (`paper/sections/04-whole-space.tex:218-260`)

Every line reference in the contract is exact: `:218-229` is `prop:Renergy`; `:235`
is the long line carrying "choose `χ ∈ C_c^∞` equal to one on the unit ball and zero
outside the ball of radius two, with `0 ≤ χ ≤ 1`, and let `χ_R(x) = χ(x/R)`"; `:241`
carries stages 1-2 and the announcement of the split; the align block is `:242-248`
with `\label{eq:Rnegative-cutoff}` on `:247`; `:249` carries "The integral at the
origin is finite in dimension three", "(1−χ_R)h_n → 0 in both L¹ and L²", the
diagonal choice and "take real parts of each component"; `:251-260` is the Bochner
paragraph.  (`Spec.lean:196`'s scaledCutoff docstring cites `:248` for the cutoff's
reuse; the contract's `:249` is the corrected reference.)  The manuscript's unnamed
`C` is `(2π)^{-3}`, the square of the `(2π)^{-3/2}` of `01-introduction.tex:91` —
verified against that line — and `C' = C·∫_{|ξ|<1}|ξ|^{2s}` is `lowHighConstant s`,
which is what `lowHighSplit` uses.  `Data.lean` references `:99` (`SpatialField`),
`:298` (`IsSliceDistribution`), `:324` (`IsHomogeneousDatum`), `:367`
(`IsHomogeneousSliceDatum`), `:410` (`homogeneousFourierENorm`) all check out.

---

## 4. Scope honesty

**The 16 / 3 partition is exact.**  `HomogeneousApproxAPI` has 20 fields: 1 data
(`χ`) + 19 proof obligations.  The contract registers `χ` + 16; the three omitted are
`annularPathApprox` (`:337`), `separatedAssembly` (`:582`),
`approxCompactHomogeneous` (`:607`).  16 + 3 = 19. ✓

*Nothing unproved is included:* every one of the 16 is assigned a real theorem and
the whole thing typechecks with only `propext`, `Classical.choice`, `Quot.sound`.

*Nothing proved is omitted:* I grepped `formalization/NSFormalization/Section4/B02/`
for the three excluded names.  The **only** occurrences are four prose lines in
`Remaining.lean:33-36`; there is no theorem, no `example`, no `def` for any of them,
and `IsHomogeneousPath` / `CompletedDenseHomogeneous` occur nowhere in the eight
modules.  So the three genuinely have nothing to register.  The table cross-checks
row for row against `REMAINING_SPLIT.md` (11 already-discharged + 5 `S` rows = 16;
3 `M` rows = the exclusions).

The `contracts.json` `scope` names all 16 fields with their discharging theorem and
module, the three exclusions with the specific missing lemma for each, the
`homogeneousDatumSub` caveat with the counterexample, the shared `baseCutoff`, and
the two things assigned to `B01` (`forceClassCompact ⊆ forceClassR`, the completion
identification).  See F1 and F2 for the two wording improvements.

**`REVIEW_REMAINING.md` §5's two hard requirements are both met.**

1. *Register `homogeneousDatumSub` only in the integrability-carrying form and copy
   the ⚠ refutation note into the contract docstring.*  Done.  The field at
   `:336-342` is `Spec.lean:490-496` verbatim, with both integrability side
   conditions.  The hypothesis-free shape appears nowhere as a field — the contract's
   only rendering of it is inside the ⚠ prose that explains why it is false.  The
   counterexample note is copied into **both** the module docstring (`:53-74`) and
   the field docstring (`:317-328`), including the `f = Σ_n 2^{-n}|x−q_n|^{-3}·
   1_{0<|x−q_n|<2^{-n}}` construction and the `Data.lean:298` totalising-convention
   explanation.
2. *State in the module docstring which three obligations are deliberately absent.*
   Done, `:76-106`, one paragraph each, naming the blocker for each
   (`separatedAssembly`: no scalar-`smul`/finite-`sum` additivity combinator for
   `IsHomogeneousSliceDatum`, only `isHomogeneousSliceDatum_sub`;
   `annularPathApprox`: not a manuscript step, feeds nothing, needs measurable-in-`t`
   selection + path DCT; `approxCompactHomogeneous`: depends on `separatedAssembly`,
   and `B01`'s `approxCompact` is monolithic), plus the explicit "No field is a
   hypothesis about an unspecified proposition, and no field is `True`, `∃ x, True`
   or any similar placeholder."

---

## 5. What `B02` still owes `R46` after this contract

`R46` needs the **conclusion** — `Data.CompletedDenseHomogeneous 2 (-1)
forceClassCompact` — and, for the two-radius argument of `04-whole-space.tex:262`,
the inspectable separated-sum shape `SeparatedCompactHomogeneousDense`
(`Spec.lean:640-664`).  This contract delivers neither.  What it delivers is the
whole **spatial** half plus the Bochner step: after `B02.homogeneous_partial`, `R46`
can already get a `C_c^∞(R³;R³)` field `η`-close to any datum in `Ḣ^s`
(`spatialApproxHomogeneous`, the only spatial input the conclusion uses), and
finite separated sums `Σ_j φ_j(t) h_j(x)` `η`-close to any datum path
(`temporalApprox`).  Three things are still missing and they compose in one chain:

1. **`separatedAssembly`** — the only `M` row on the critical path.  Its
   realization-dependent conjunct is the homogeneous twin of
   `Section4/B01/Separated.lean:182 isSobolevPath_separated`, and it needs a
   scalar-`smul` / finite-`sum` additivity combinator for `IsHomogeneousSliceDatum`
   that does not exist in the tree — only the difference lemma
   (`HomogeneousWitness.lean:585`).  Without it, the separated sum `temporalApprox`
   produces cannot be certified a member of `F_c` carrying an `IsHomogeneousPath`.
2. **The realization-independent triangle-inequality glue** that
   `REVIEW_REMAINING.md` §4 names but `REMAINING_SPLIT.md` does not: bounding
   `bochnerDatumENorm q s (separatedPath φ A' − separatedPath φ A)` by the weighted
   sum of fibre errors.  `B01` never needed it, so nothing exists.  It mentions
   neither realization and should be proved once next to `separatedPath`.
3. **`approxCompactHomogeneous`** — assembled from 1, 2, `temporalApprox` and
   `spatialApproxHomogeneous`.  It cannot reuse or parametrize `B01`'s
   `approxCompact`, which applies the source density theorem directly and has no
   homogeneous analogue.

`annularPathApprox` is not on that chain; it is not a step of the manuscript's own
proof and feeds nothing, and the contract is right to record it as such.  Separately,
`R46` will consume `B01.bochner_partial`'s `compactSubsetForceR` and `completion*`
fields for the realization-independent half, and `B01` and `B02` now agree on the
cutoff (`baseCutoff`) and on `separatedPath`, so the two contracts compose without a
translation layer.
