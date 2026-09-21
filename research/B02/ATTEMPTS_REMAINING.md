# B02 remaining-fields attempts (lane 097)

Non-generated record.  Goal: prepare the `B02` contract by (1) tabling the 8
`HomogeneousApproxAPI` fields the seven merged modules do not discharge
(`research/B02/REMAINING_SPLIT.md`) and (2) proving every `S`-size row in a new
module.  Per the task, `M` items are documented, not forced.

## Deliverables

* `formalization/NSFormalization/Section4/B02/Remaining.lean` — namespace
  `NSFormalization.Section4.B02`, five public theorems:
  * `chi_smooth`, `chi_one`, `chi_vanishes`, `chi_range` — the four `χ` fields on
    `χ := NavierStokesR3.ComparisonCutoffs.baseCutoff`, each the vendor estimate
    verbatim (the identical binding `Bindings/BochnerPartial.lean:66-71` uses).
  * `temporalApprox` — `:= NSFormalization.Section4.B01.temporalApprox` (the `B02`
    field is token-identical to the registered `B01` field).
* `research/B02/axioms_remaining.lean` — conformance `example`s inhabiting the
  spec-field types verbatim (in the `Contracts.V1.Data` vocabulary for
  `temporalApprox`, with `χ := baseCutoff` for the four cutoff fields) + a
  `#print axioms` for each of the five theorems.

## Route (the `S` rows)

* `chi_*`: `04-whole-space.tex:235`'s `χ` is `B01`'s cutoff verbatim
  (`research/B02/Spec.lean` module docstring: "Identical to `B01`'s five
  fields").  `B01` binds `χ := baseCutoff`; the four properties are
  `baseCutoff_smooth`, `baseCutoff_eq_one`, `baseCutoff_eq_zero`,
  `baseCutoff_nonneg`/`baseCutoff_le_one` (`ComparisonCutoffs.lean:40-50`).
  `χ x ∈ Icc 0 1` is defeq to `0 ≤ χ x ∧ χ x ≤ 1`, so the anonymous constructor
  closes it, exactly as `Bindings/BochnerPartial.lean:70-71`.
* `temporalApprox`: diffed the `B02` spec field (`Spec.lean:563-573`) against the
  registered `B01` field (`Contracts/V1/BochnerPartial.lean:132-138`); identical
  save the `separatedPath` namespace, and the two `separatedPath` `def`s are
  literally `fun t => ∑ j, φ j t • A j` (defeq).  The Bochner step lives on the
  datum carrier `RealVectorSobolev s`, shared by both realizations
  (`Data.lean:367-378`); `NSFormalization.Section4.B01.temporalApprox`
  (`Section4/B01/Temporal.lean:170`) discharges it directly.

## Attempts / findings that shaped the `S`/`M` split (the negative record)

1. **Is `separatedAssembly` a direct reuse of `B01`'s?  No.**  `B01`'s
   `separatedAssembly` (`Section4/B01/Separated.lean:220`) concludes
   `IsSobolevPath`; `B02`'s field (`Spec.lean:582`) needs `IsHomogeneousPath`,
   and its per-profile hypothesis is `IsHomogeneousSliceDatum` instead of
   `IsSobolevDatum`.  Two of the three conjuncts (`MemForceCompact`,
   `AEStronglyMeasurable`) are realization-independent and reuse `B01` verbatim,
   but the middle conjunct needs a new homogeneous datum-path additivity lemma.
   → **M**, not proved.  Precise lemma, route and size in `REMAINING_SPLIT.md`
   row 6.  Attempting it in this lane would require building `smul`/finite-`sum`
   combinators for `IsHomogeneousSliceDatum` (only the `_sub` "difference of two"
   forms exist, `HomogeneousWitness.lean:534-594`) with the integrability side
   conditions the totalization convention forces (`REVIEW_U6.md` §4) — new work,
   deliberately not forced.
2. **Can `approxCompactHomogeneous` reuse `B01`'s `approxCompact` gluing?  No.**
   Read `Section4/B01/Compact.lean:155-180`: `B01`'s `approxCompact` is
   **monolithic** — it applies the source density theorem
   `Paper3.exists_angular_real_vector_positive_physical_approx` (which emits an
   `IsSobolevPath` directly) and does **not** glue
   `temporalApprox` + `spatialApprox` + `separatedAssembly`.  There is no
   homogeneous analogue of that source theorem, so the field must be assembled
   fresh through the `SeparatedCompactHomogeneousDense` route (`Spec.lean:640-664`),
   which also depends on `separatedAssembly` (row 6).  → **M-L**, not proved;
   `REMAINING_SPLIT.md` row 8.  (The task brief's "glued exactly as `B01`'s
   `approxCompact` glues its inputs" does not match the code: `B01`'s proof is not
   that glue.)
3. **`annularPathApprox`** (`Spec.lean:337`): the path-level annular truncation.
   Not in the seven modules; needs a measurable-in-`t` selection of the fibre
   truncation `annularTruncLp δ R (b t)` (`Annular.lean:205`) and a path-level
   dominated-convergence argument over `(δ,R)`.  → **M**; `REMAINING_SPLIT.md`
   row 7.
4. **`homogeneousDatumSub`** — recorded for the contract lane, already discharged
   before this lane: the hypothesis-free form is **false** (`REVIEW_U6.md` §4);
   the contract must register the integrability-carrying form
   (`isHomogeneousSliceDatum_sub_of_integrable`, `LebesgueDatum.lean:446`), never
   the historical shape at the D01 docstring's stale `Spec.lean:470` ref.

No approach that was tried failed to compile; the only "failures" are the three
`M` classifications above, each a scope decision (a new lemma is required) rather
than a broken proof.

## Final list — the 8 fields, proved vs unproved (exact input for the B02 contract lane)

Proved this lane (`S`, in `Section4/B02/Remaining.lean`, axioms
`[propext, Classical.choice, Quot.sound]`):

| field | Spec:line | theorem | binding target for the contract |
|---|---|---|---|
| `chi_smooth` | :280 | `NSFormalization.Section4.B02.chi_smooth` | `χ := NavierStokesR3.ComparisonCutoffs.baseCutoff` |
| `chi_one` | :282 | `…B02.chi_one` | (same `χ`) |
| `chi_vanishes` | :285 | `…B02.chi_vanishes` | (same `χ`) |
| `chi_range` | :287 | `…B02.chi_range` | (same `χ`) |
| `temporalApprox` | :563 | `…B02.temporalApprox` (`= …B01.temporalApprox`) | `NSFormalization.Section4.B01.temporalApprox` |

Not proved (`M`, documented in `REMAINING_SPLIT.md`, blocked on a new lemma):

| field | Spec:line | size | needs |
|---|---|---|---|
| `separatedAssembly` | :582 | M | `isHomogeneousPath_separated` (homogeneous datum-path additivity over a finite separated sum) |
| `annularPathApprox` | :337 | M | path-level annular truncation (measurable selection + DCT) |
| `approxCompactHomogeneous` | :607 | M-L | `SeparatedCompactHomogeneousDense` glue; depends on `separatedAssembly` |

The 11 fields the seven merged modules already discharge are listed in
`REMAINING_SPLIT.md` (top table); together with the 5 above the contract's proved
set is 16 of the 19 `HomogeneousApproxAPI` fields, the 3 `M` fields being the
open ones.

## Commands run (all `lake` from `WT/verification`, one process at a time)

| command | result |
|---|---|
| `lake build NSFormalization.Section4.B01.Temporal NSFormalization.Section4.B02.AnnularReal` | `Build completed successfully (9889 jobs)`; only dependency `Paper3.*` warnings |
| `lake build NSFormalization.Section4.B02.Remaining` | `✔ Built …B02.Remaining (3.3s)`, `Build completed successfully (9883 jobs)`; no warnings on `Remaining.lean` lines |
| `lake env lean ../formalization/NSFormalization/Section4/B02/Remaining.lean` | silent, exit 0 |
| `lake env lean ../research/B02/axioms_remaining.lean` | 5 decls, each `[propext, Classical.choice, Quot.sound]`, exit 0 |
| `make check` (from WT root) | see report |
