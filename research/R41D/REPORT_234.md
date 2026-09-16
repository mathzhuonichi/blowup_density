# Lane 234 report — R41D small gaps G2--G5

## 1. Result

All four gaps are closed without weakening their requested statements.

- G2: `memForceR_of_memForceRapid` and the set-level
  `forceClassRapid_subset_forceClassR`.
- G3: `memForceRapid_of_compact_difference`.
- G4: `initialClassSchwartz_subset_initialClassR`.
- G5: `forceSobolevENorm_zero` for every `q`, the requested
  `forceSobolevENorm_zero_of_one_or_two`, and `sub_self_force`.

The preliminary later-lane search found no pre-existing proof of G2--G5.  The
contract and local definitions agree literally, and no satisfiability
discrepancy was found, so `COMPARISON_SMALL_GAPS.md` was not needed.

## 2. Proof and audit summary

G2 is the substantive result.  Rapid future-time normal slices are packaged as
Schwartz maps and then as smooth all-jet `L²` fields.  Dominated convergence
gives continuous spatial-jet paths, while normal differentiation gives smooth
order-`m` Sobolev datum paths.  Rapid decay separates into an `L²_x` spatial
majorant and one scalar time majorant lying in both `L¹` and `L²`; the finite
jet estimate for the angular datum then supplies both time-integrability
clauses required by `MemForceR`.

G3 follows from compact-support rapid decay and rapid-class addition.  G4 uses
the three complex Schwartz components and the canonical spatial angular datum.
G5 uses the zero datum path as an explicit competitor in the defining infimum.

The conformance audit includes `rfl` bridges for all relevant local/contract
definitions and contract-vocabulary versions of G2--G5.  Each of the seven
local results and seven contract-facing results prints exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Zero witnesses instantiate the interfaces non-vacuously.  There are no uses
of `sorry`, `admit`, `axiom`, or `native_decide`.

## 3. Verification

The following gates pass under Lean 4.34.0-rc2 with `LEAN_NUM_THREADS=6`:

- `lake build NSFormalization.Section4.R41.ClassFacts` — success.  Lake replays
  warnings stored in pre-existing dependency traces; the new target itself has
  no warning.
- `lake env lean ../formalization/NSFormalization/Section4/R41/ClassFacts.lean`
  — success with exactly zero output.
- `lake env lean ../research/R41D/axioms_class_facts.lean` — success; fourteen
  expected axiom reports, all exactly the approved three axioms and no warning.
- `make check` — success.
- `git diff --check` — success.

## 4. Commit and files

Committed on branch `erenup/234-R41D-small-gaps` with subject:
`Close R41D small class and norm gaps`.

Files delivered:

- `formalization/NSFormalization/Section4/R41/ClassFacts.lean`
- `research/R41D/axioms_class_facts.lean`
- `research/R41D/ATTEMPTS_SMALL_GAPS.md`
- `research/R41D/COMPARISON.md`
- `research/R41D/REPORT_234.md`

## Lead correction (review 234, 2026-09-17)

G5 (`forceSobolevENorm q s 0 = 0`) already existed on integration as lane 235's lemma in `verification/Bindings/DensityFromInsertion.lean:16-27`; only G2–G4 were genuinely absent. `ClassFacts.lean`'s G5 proof stands as the `formalization/`-side (local-vocabulary) version.
