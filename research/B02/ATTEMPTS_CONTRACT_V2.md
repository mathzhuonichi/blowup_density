# B02 `homogeneous_partial_v2` — attempts, decisions, negative examples (lane 116)

Registers `B02.homogeneous_partial_v2`: `Contracts/V2/HomogeneousPartial.lean`
extends the frozen `HomogeneousApproxPartialAPI` (V1, untouched) by the two
post-freeze `Section4/B02` theorems — `separatedAssembly` (lane 103) and
`approxCompactHomogeneous` (lane 110). Plus `Bindings/HomogeneousPartialV2.lean`,
`Tests/HomogeneousPartialV2.lean`, the `contracts.json` entry, the
`work_items.json` line, and the conformance file `axioms_contract_v2.lean`.

## Decisions

1. **`separatedAssembly` registered on `-3/2 < s`, not the spec's `∀ (s : ℝ)` and
   not the narrower `SplitRange s`.** The proving theorem
   `NSFormalization.Section4.B02.separatedAssembly` (`SeparatedAssembly.lean:211`)
   carries the extra hypothesis `hs : -3/2 < s` (needed by the uniqueness route
   through `D01`'s compact-datum constructor `homogeneousVectorDatum`, finite only
   at `s > -3/2`). The verbatim `∀ s` form of `Spec.lean:593` is unproved and
   near-vacuous for `s ≤ -3/2` (`REVIEW_APPROX_COMPACT.md` finding 5-A; lane 103's
   recommendation, `REMAINING_SPLIT.md` row 6). `-3/2 < s` is the honest hypothesis
   the theorem actually proves; `SplitRange s = -3/2 < s ∧ s ≤ 0` would gratuitously
   add `s ≤ 0`, which the theorem does not need. `approxCompactHomogeneous` feeds it
   only `SplitRange.1 = -3/2 < s`, so no consumer is weakened. Every other token
   matches `Spec.lean:593`.

2. **`approxCompactHomogeneous` registered verbatim as `Spec.lean:618`.** The
   contract type is `CompletedDenseHomogeneous q s forceClassCompact` for
   `1 ≤ q`, `q ≠ ⊤`, `SplitRange s` — token-for-token `Spec.lean:618`. The proving
   theorem (`ApproxCompact.lean:229`) is *definitionally equal* to it — kernel
   `rfl`-checked in `research/B02/axioms_approx_compact.lean` (lane 110), modulo the
   three benign differences the `CompletedDenseHomogeneous` abbrev (`Data.lean:752`)
   and the sanctioned `SplitRange`/`forceClassCompact` restatements introduce — so
   the binding assigns it directly.

3. **`annularPathApprox` stays excluded**, asserted nowhere. No proof exists in the
   tree, it is off the manuscript's own chain (the paper does the Bochner reduction
   first, `04-whole-space.tex:251`), it feeds nothing, and
   `approxCompactHomogeneous` does not route through it. Stated in the module
   docstring and in the contract scope.

4. **No new restated object → no new `rfl` bridge is strictly required.** Both new
   fields are stated entirely in vocabulary V1 and its imports already fix:
   `SplitRange` (`Contracts.V1.HomogeneousPartial`), the shared `separatedField` /
   `separatedPath` (`Contracts.V1.BochnerPartial`), and
   `CompletedDenseHomogeneous`/`forceClassCompact`/`MemForceCompact`/
   `IsHomogeneousPath`/`forceTimeMeasure` (`Contracts.V1.Data`). The relevant `rfl`
   bridges already live in `Bindings/BochnerPartial.lean:47-54` and
   `Bindings/HomogeneousPartial.lean:97-99`; I re-recorded three of them
   (`separatedField`, `separatedPath`, `SplitRange`) in
   `Bindings/HomogeneousPartialV2.lean` for self-documentation.

5. **Binding is a direct assignment, no transport** (contrast `MaximalPartialV2`,
   which needs an `Iff` transport because `ClassicalSolutionR` is a `structure` with
   two separately-declared copies). Here the contract states both new fields in the
   shared `Data`/`BochnerPartial` vocabulary, which is defeq to the `formalization/`
   vocabulary the theorems produce, so `homogeneousPartialV2 = { homogeneousPartial
   with separatedAssembly := …, approxCompactHomogeneous := … }` typechecks with the
   two theorems applied verbatim. `separatedAssembly`'s explicit field-`J` is bound
   `_J` and inferred from `φ`, exactly as `Bindings/BochnerPartial.lean:74`.

6. **`HomogeneousApproxPartialV2API` is a `Type`** (it inherits the data field `χ`),
   so `homogeneousPartialV2` and `checkedHomogeneousPartialV2` are `def`s (as V1's
   `homogeneousPartial`/`checkedHomogeneousPartial` are), not `theorem`s — unlike the
   purely-propositional `MaximalPartialV2API`.

## Anything not matched token-for-token

* `separatedAssembly`: the hypothesis is `-3/2 < s`, where `Spec.lean:593` writes
  `∀ (s : ℝ)`. This is a deliberate, honest narrowing (decision 1); every other
  token matches. The general `∀ s` form is not proved anywhere.
* `approxCompactHomogeneous`: the *contract* type is token-identical to
  `Spec.lean:618` (both use `CompletedDenseHomogeneous`, `SplitRange`,
  `forceClassCompact`). The defeq that must be checked is between the contract field
  and the *proving theorem*, whose `formalization/` vocabulary
  (`CompletedDenseVia`/`IsHomogeneousPath`/`SplitRange`/`forceClassCompact`) differs
  by three tokens; `rfl` closes it (lane 110's conformance).

## Negative examples (pasted error text)

### N1 — `ENNReal.two_ne_top` does not exist
The Tests/conformance `example`s instantiate `approxCompactHomogeneous` at `q = 2`,
needing `(2 : ℝ≥0∞) ≠ ⊤`. First attempt used `ENNReal.two_ne_top`:

```
../research/B02/probes/v2_test_examples.lean:17:28: error(lean.unknownIdentifier): Unknown constant `ENNReal.two_ne_top`
../research/B02/probes/v2_test_examples.lean:27:68: error(lean.unknownIdentifier): Unknown constant `ENNReal.two_ne_top`
```

`exact?` on `(2 : ℝ≥0∞) ≠ ⊤` returns `Ne.symm ENNReal.top_ne_ofNat`. Adopted the
robust `by simp`, which closes it. `1 ≤ (2 : ℝ≥0∞)` is `one_le_two`, and
`SplitRange (-1)` is `⟨by norm_num, by norm_num⟩` (the anonymous constructor
unfolds the `def` to `-3/2 < -1 ∧ -1 ≤ 0`).

### N2 — conformance file needed `open BlowupDensity`
`research/B02/axioms_contract_v2.lean` sits at top level (no enclosing
`namespace BlowupDensity`). Referencing `Contracts.V2.HomogeneousPartial.…`,
`Contracts.V1.HomogeneousPartial.SplitRange`,
`Contracts.V1.BochnerPartial.separatedField` failed:

```
../research/B02/axioms_contract_v2.lean:38:10: error(lean.unknownIdentifier): Unknown identifier `Contracts.V2.HomogeneousPartial.HomogeneousApproxPartialV2API`
../research/B02/axioms_contract_v2.lean:53:21: error(lean.unknownIdentifier): Unknown identifier `Contracts.V1.BochnerPartial.separatedField`
../research/B02/axioms_contract_v2.lean:63:4: error(lean.unknownIdentifier): Unknown identifier `Contracts.V1.HomogeneousPartial.SplitRange`
```

Those declarations live under the `BlowupDensity.` prefix. Adding `open BlowupDensity`
(the `#print axioms` lines, which used the full `BlowupDensity.Bindings.…` path,
were fine either way) fixed it; EXIT=0, all four declarations
`[propext, Classical.choice, Quot.sound]`. Inside the contract/binding/test files
this is not an issue — they open `namespace BlowupDensity.…`, so
`Contracts.V1.…` resolves via the `BlowupDensity` parent.

## Environment note

At session start this worktree (`165c19a`) was **behind** `origin/erenup/integration`
(`94bec50`) by lanes 111 (D01 SL8 prep) and 114 (`R42.insertion_lifespan_v2`, the
20th contract). The base-compatibility gate
(`check_contracts.py --base-ref origin/erenup/integration`) would have reported
`R42.insertion_lifespan_v2` and its V2 files as "removed". `HEAD` was an ancestor of
the base, so a `git merge --ff-only origin/erenup/integration` (no commit, no
conflict with the new untracked files; sanctioned by CLAUDE.md for a behind
worktree) brought the worktree to base. Rebuilt `Tests.HomogeneousPartialV2`
afterward — still green.

## Commands run (from the worktree, after `. scripts/lean-env.sh`; lake from `verification/`)

| command | result |
|---|---|
| `LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.B02.{ApproxCompact,SeparatedAssembly}` | EXIT=0, 9892 jobs |
| `LEAN_NUM_THREADS=6 lake build Bindings.HomogeneousPartialV2` | EXIT=0, contract+binding built, no warnings on the new files |
| `LEAN_NUM_THREADS=6 lake env lean ../research/B02/probes/v2_test_examples.lean` | EXIT=0, 0 bytes (both example shapes + numeric side goals typecheck) |
| `LEAN_NUM_THREADS=6 lake build Tests.HomogeneousPartialV2` | EXIT=0, "checked; standard logical axioms only" |
| `LEAN_NUM_THREADS=6 lake env lean ../research/B02/axioms_contract_v2.lean` | EXIT=0, 4 decls each `[propext, Classical.choice, Quot.sound]`, 4 `example`s typecheck |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | EXIT=0, `registered_contracts = 21` (base 20 + 1), `base_compatibility_checked = true` |
| `make check` | EXIT=0, 13 policy tests OK, "30 work items … consistent" |
| `make test` | (see report) |
| `make test-mutations` | (see report) |
