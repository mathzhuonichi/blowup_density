# Lane 174-SPEC-r41d-compare report

## 1. What was reconciled

The two blind R41D drafts are reconciled into the frozen subcritical density
specification for Theorem 4.1(i), including the `F_R`, `F_c`, and `F_rd`
relative classes.  The final shape uses Draft B's canonical
`breakdownSetIn` membership, but Draft A's class-parameterized API and typed
two-case witness: `f=g` when `T_max(a,g)<=T`; otherwise one aligned R42 V2
family supplies a positive margin, a compact force difference, the selected
small parameter, exact lifespan `T`, and the same-family history/energy data.
The two strict thresholds and the order `forall a forall g forall radius
exists f` are literal in the type.

## 2. Lean files now present

- `research/R41D/COMPARISON.md` — paper/Draft A/Draft B clause table, registered
  object audit, fidelity rulings, and merged G-table.
- `research/R41D/RECONCILIATION.md` — winning shape per clause and false/weak/
  vacuous-statement risk audit, including `top` norms, empty/zero lifespan,
  and `Ico`/`Icc` window choices.
- `research/R41D/Spec.lean` — two concrete definitions and one fully expanded
  `RDensityAPI`; zero elaboration errors.
- `research/R41D/REPORT_174.md` — this handoff.

`DraftA.lean` and `DraftB.lean` are untouched and still elaborate.

## 3. Gaps

Five proof-interface gaps remain; none blocks stating or elaborating the
specification: an end-to-end aligned R42 V2 assembly from the strict-lifespan
case; `F_rd subset F_R`; preservation of `F_rd` under the compact inserted
difference; `S_sigma subset X_R`; and the zero-force
`forceSobolevENorm = 0` lemma needed by the `f=g` branch.  The comparison also
records that positive-margin selection, `F_R` compact-difference closure,
`F_c subset F_R`, and compact additivity are already registered and are not
open gaps.

## 4. Commands and results

- `sed -n '7,30p' paper/sections/04-whole-space.tex`,
  `sed -n '176,195p' ...`, and `sed -n '30,62p' ...`, plus numbered `nl -ba |
  sed -n` checks — every cited manuscript line was read directly.
- `. scripts/lean-env.sh && cd verification && LEAN_NUM_THREADS=6 lake env lean
  ../research/R41D/{DraftA,DraftB,Spec}.lean` (run as three explicit Lean
  invocations) — exit 0, zero Lean output.
- `. scripts/lean-env.sh && LEAN_NUM_THREADS=6 make check` from the worktree
  root — exit 0; 13/13 contract-policy tests and the 30-item work queue passed.
  The pre-existing diagnostics `source_hashes_match: false` and the copied
  `Paper1/BoundaryCorollary.lean` admission token were reported but are not
  failures and are untouched by this lane.
- `git diff --check` on the four lane-174 deliverables — clean.

One earlier command sourced `scripts/lean-env.sh` after changing the command's
working directory to `verification/`; it failed before Lean started with
“no such file or directory”.  It was immediately replaced by the successful
root-sourced commands above, and changed no files.
