# Lane 467 — T24b U-CAN and Ub1–Ub3

## 1. Statements

U-CAN is complete: canonical `MultipleRegionsAPI` has all 30 Spec fields,
`Type`-valued over raw packet fields, with the complete raw-clause
`multipleRegionsStatement`. The probe checks both fieldwise conversions,
all 30 projection types, four vocabulary equalities, and transport of the
raw universal statement to the packet-indexed Spec statement.

Ub1 constructs placements at every prescribed centre/radius and common
horizon T, the full T15 scaling records, and admissible ε with ε² < T.
The compact carrier is lane 459's `K ∪ Prod.snd '' tsupport f`; with its
positive norm bound R, the threshold is
`min (min (1/2) (T/4)) (regionRadius j / (2*(R+1)))`.
Ub2 selects each T15 classical solution with both field pins.
Ub3 proves velocity zero on `Q ∖ B_j` for t in `[0,T)` and force zero
there at every real time. No T18 dependency, named analytic input,
admission, extra axiom, or heartbeat override is introduced.

## 2. Files

- `formalization/NSFormalization/Section3/T24/Multiple.lean`: canonical
  vocabulary, 30-field record, universal statement.
- `formalization/NSFormalization/Section3/T24/MultipleComponents.lean`:
  raw-field-indexed `RegionsData` and all eleven Ub1–Ub3 definitions/theorems.
- `research/T24/probes/multiple_api_on_canonical.lean`: Spec conformance
  and construction of the raw hypotheses from any `PacketImportAPI`.
- `research/T24/axioms_ub1_ub3.lean`: 19 canonical audit entries, each
  exactly `[propext, Classical.choice, Quot.sound]`; nine named probe
  declarations were separately audited with the same result.
- `research/T24/ATTEMPTS_UB1_UB3.md`: exact development errors, their fixes,
  and the derivative/disjointness handoff for Ub4/Ub6.
- `research/T24/T24_SPLIT.md`: U-CAN/Ub1/Ub2/Ub3 completion lines and ledger.

No existing Lean module was edited. The pre-existing untracked lane brief
was left untouched and is not part of this commit.

## 3. Gaps and error text

No residual for U-CAN or Ub1–Ub3. Ub4–Ub7 remain outside this lane;
no inhabitant of the complete API or proof of its existence statement is
claimed. No new contract is registered before that assembly.

Resolved errors include `Application type mismatch` from grouped structure
fields, `linarith failed to find a contradiction` without explicit scale
positivity, `Tactic rewrite failed: Did not find an occurrence` for the
definitionally equal horizon, spatial versus spacetime `tsupport`, and
`Ambiguous term Space` in the probe. Full exact diagnostics are in ATTEMPTS.
The initial unindexed data sort printed `does not depend on any axioms`;
indexing it by the actual raw packet parameters makes both the type and
constructor satisfy the requested exact three-axiom audit.

## 4. Commands and results

All Lean commands used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and
Lake from `verification/` only.

- `lake build NSFormalization.Section3.T15.Assembly NSFormalization.Section3.T15.Solution NSFormalization.Section3.T15.SingleCopy`
  — success, required closure built first.
- `lake build NSFormalization.Section3.T24.Multiple` — success, 0 errors.
- `lake build NSFormalization.Section3.T24.MultipleComponents Bindings.Scaling3`
  — success, 0 errors; final indexed-carrier rebuild also passed.
- `lake env lean` on both new canonical modules and the conformance probe
  — exit 0, zero output.
- `lake env lean ../research/T24/axioms_ub1_ub3.lean` — exit 0,
  all 19 entries exactly the standard three axioms.
- Separate audit of all nine named probe declarations — exit 0,
  exactly the standard three axioms.
- `make check` — passed; policy tests and 45 work-item consistency checks passed.
- `make test` — passed; registered contract checks passed.
- `make test-mutations` — passed; implementation refactor accepted,
  admission/extra-axiom/weakened-hypothesis mutations rejected.
- Forbidden-token scan of delivered implementation/probe and `git diff --check`
  — clean. Existing dependency warnings were replayed by Lake; direct
  elaboration of the new modules and probe emitted none.
