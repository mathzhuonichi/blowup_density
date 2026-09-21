# Lane 171-SPEC-r41d-draft-a report

## What is stated

Draft A states the subcritical density direction of Theorem 4.1 for each of the
three relative force classes `F_R`, `F_c`, and `F_rd`.  It has separate fields
for the exact thresholds `s<1/2` in `L¹_tH^s_x` and `s<-1/2` in
`L²_tH^s_x`, with quantifiers ordered `∀ a ∀ g ∀ radius ∃ f`.  The returned
force stays in the selected class and satisfies `T_max(a,f)≤T`.  The witness
also records the manuscript's proof split: it is literally `g` when
`T_max(a,g)≤T`, and otherwise comes from one aligned R42 V2 insertion family
with a positive margin, compact force correction, and lifespan exactly `T`.

I complied with the blind-draft rule.  I did not read, open, grep, or search for
another R41D draft; did not inspect any pre-existing `research/R41D/` material;
did not inspect another worktree; and did not read R41D material in
`research/section4/STATEMENTS.md`.  The only files under `research/R41D/` that
I inspected are the files created in this lane.

## Files

- `research/R41D/DraftA.lean` — statement-only Lean draft with the concrete
  R42 insertion witness and `RDensityAPI`.
- `research/R41D/COMPARISON_A.md` — paper-clause/Lean-field table, contract
  vocabulary choices, judgment calls, and exact upstream gaps.
- `research/R41D/REPORT_171-SPEC-r41d-draft-a.md` — this four-part handoff.

## Gaps

The listed contracts do not expose a direct theorem taking an arbitrary
long-lived `(a,g)` reference to an aligned R42 V2 family; the two existing R42
existential statements begin from preassembled scaling/family objects.  The
assembly also needs an A02 bridge selecting a positive regularity margin from
`T<T_max`, compact-perturbation closure for all three force classes (including
`F_c,F_rd⊆F_R` for R42's reference hypothesis), the inclusion
`initialClassSchwartz⊆initialClassR`, and the zero-force-difference norm lemma
used by the `f=g` branch.  `COMPARISON_A.md` gives the exact Lean shapes and
owners.

## Commands

- `sed -n` was run on every cited manuscript range, including
  `04-whole-space.tex:1-30,176-205` and `02-preliminaries.tex:1-110`; the exact
  numbered theorem/definition ranges were rechecked with `nl -ba | sed -n`.
- `. scripts/lean-env.sh && cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R41D/DraftA.lean` — 0 errors, 0 output.
- `git diff --check -- research/R41D/DraftA.lean research/R41D/COMPARISON_A.md research/R41D/REPORT_171-SPEC-r41d-draft-a.md` — clean, 0 output.
- `. scripts/lean-env.sh && make check` — exit 0; contract-policy tests (13/13)
  and work-queue consistency passed.  The existing plan diagnostic reported
  `source_hashes_match: false` but did not fail the gate; this lane changes no
  copied source or registered contract.
