# Lane 448 — T21 proof split report

## 1. What the split decides

The split assigns N0–N15 and final assembly to eight S/M lane bundles, with exact Spec targets, verified reuse routes, a dependency ledger, and at most three concurrent lanes. All nine NonDensityAPI fields and five MainTheoremAPI fields remain. No new named inputs are introduced. Conditional proofs may start with threaded T19/T20 records; unconditional statements and registration wait for inhabited upstream APIs in T19 → T20 → T21 order.

Two source checks sharpen the older reconciliation: N12 already has a proof (`formalization/NSFormalization/Section3/T20/CriticalEnergy.lean:402`), and lane 428's `critLower` is a usable CLM construction pattern but targets homogeneous mean-zero data (`formalization/NSFormalization/Section3/T20/YBound.lean:56,86,96`). N3 needs the general inhomogeneous weight ratio. N6 is a separate shared triangle-inequality obligation for T18 U11 lane 445 and T21 ball openness; the first landed supplier is reused.

## 2. Files

- `research/T21/T21_SPLIT.md`: complete planning deliverable, including all sixteen proof units and assembly/Nonempty/statements/contracts/bindings/tests unit.
- `research/T21/REPORT_448.md`: this four-part report and handoff.

No Lean source, existing module, contract, test, registry, or shared status file was changed. Resume from this report and the split; upstream scheduling remains with the lead. Skeleton committed first as `3b8c909f`, followed by separate ground-rule, unit, ledger, wave, risk, and citation-audit commits. No push, merge, or rebase.

## 3. Open questions

Owner convention ruling on Prop versus Type remains open; the approved Prop-valued Spec governs meanwhile. The lead retained both ballRelativelyOpen and zeroInitialNonDensity, so neither is dropped. Lead must select the N6 supplier with lane 445 and finalize registration module/ID names. T20 U12/U13 and T19 density/registration are external closure gates, not newly hidden premises. The existing maximalLifespanT_eq theorem stays in Bindings; the Spec's use of it moves to the final binding layer.

No proof implementation or Lean compilation is claimed by this planning delivery. Bounded no-hit searches, their exact commands, and the distinction between specialized existing lemmas and new targets are recorded in split §4.

## 4. Commands and results

- Read `CLAUDE.md`, status/plan entry points, T21 Spec/reconciliation, T18/T20 house splits, T19 Spec/bookkeeping, canonical T20 fields, registered torus definitions and lifespan bridge, Section4/R41 and D01 lowering, and Paper1 comparison proofs with `sed -n` and declaration searches. Paper ranges were read explicitly with `sed -n '1,16p' paper/sections/03-torus.tex` and `sed -n '506,525p' paper/sections/03-torus.tex`.
- `grep -rn` searches verified critLower, torusMultiplierCLM, the contraction bound, zero initial class, zero norm, and threshold reuse. Exact negative searches and their limited meaning are preserved in split §4; a broad registry search found a T20 mention in T11's scope, so it is not reported as a no-hit result.
- Inline Python audit: all 17 Lean quotation blocks occur verbatim in `research/T21/Spec.lean`; N0–N15 each have exactly one unit heading; only the requested model names appear. Passed.
- `. scripts/lean-env.sh` then `make check`: exit 0; 46 registered contracts checked, 13 contract-policy tests passed, and 45 work items consistent. The architecture summary also reported `source_hashes_match: false` and existing copied-source admission inventory; this is not a clean Lean proof audit and no Lean source was changed to address that pre-existing inventory.
- `git diff --check`: passed. No lake invocation: Markdown-only planning changes do not require Lean build/test/mutation runs. Future proof/registration gates are specified in split unit A.
- Incremental `git add` / `git commit` performed on `erenup/448-T21-SPLIT-plan`; final status checked after committing the report.
