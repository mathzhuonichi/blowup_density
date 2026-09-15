# Lane 172-SPEC-r41d-draft-b report

## 1. What is stated

`RDensityAPI` states the subcritical direction of Theorem 4.1 for the three
manuscript ambient force classes `F_R`, `F_c`, and `F_rd`. It has separate
fully expanded fields for the two exact thresholds:

- `densityL1`: relative density in `L^1(0,infinity;H^s(R^3))` for `s < 1/2`;
- `densityL2`: relative density in `L^2(0,infinity;H^s(R^3))` for `s < -1/2`.

Both types visibly use the required order `forall a forall g forall positive
radius exists f`. The witness lies in `breakdownSetIn Y`, so it belongs to the
same selected relative ambient class and has maximal lifespan at most `T`.
The docstrings pin the proof split from manuscript lines 176-177: use `g`
itself when it already breaks down by `T`; otherwise choose positive reference
lifespan beyond `T` and use one R42 inserted family, with its convergence,
compact-difference, and exact-lifespan projections explicitly named.

I complied with the blindness rule. I did not read, open, grep, or search for
another R41D draft, another pre-existing `research/R41D/` file, another
worktree, or an R41D entry in `research/section4/STATEMENTS.md`. The only files
under `research/R41D/` that I accessed are the deliverables created in this
lane.

## 2. Files

- `research/R41D/DraftB.lean`: one selector `def` and the one statement
  `structure RDensityAPI`; no proof declarations or mathematical proof terms.
- `research/R41D/COMPARISON_B.md`: paper-clause/Lean-field table, every
  contract-vocabulary choice, exact R42 projections consumed, and the upstream
  gap table.
- `research/R41D/REPORT_172-SPEC-r41d-draft-b.md`: this four-part handoff.

No existing source, contract, test, task-card, plan, or paper file was changed.

## 3. Gaps

The statement itself needs no new topology, norm, breakdown-set, or lifespan
definition. The proof-facing gaps found in registered contracts are:

1. An end-to-end R42 adapter from arbitrary `(nu,T,a,g)` plus
   `RegularThrough nu a g T` to a correctly identified
   `InsertionLifespanV2API` family with `family.a=a`, `family.g=g`, and
   `family.T=T` (owner: R42 assembly).
2. `MemForceRapid f -> MemForceR f` / `forceClassRapid subset forceClassR`
   (owner: D01 force-class layer, consumed by R45).
3. Rapid-class preservation in the exact R42 shape:
   `MemForceRapid g -> MemForceCompact (f-g) -> MemForceRapid f`
   (owner: R45).
4. `initialClassSchwartz subset initialClassR`, needed for the highlighted
   `S_sigma` specialization of the rapid formulation (owner: D01 initial-data
   layer, consumed by R45).

The base `F_R` compact-difference closure is already registered as
`DatumLemmasAPI.memForceR_of_compact_difference`. The `F_c` instance is an
elementary local consequence of registered compact additivity and
`f = g + (f-g)`; it is not a mathematical upstream blocker.

## 4. Commands and results

- `sed -n ...` / `nl -ba ... | sed -n ...` on every cited manuscript range:
  completed. The permitted task card, contracts, plan subsection, and R43
  template were also read.
- `. scripts/lean-env.sh && cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R41D/DraftB.lean`:
  exit 0, zero Lean output and zero elaboration errors.
- `rg -n '^(def|structure|axiom|theorem|lemma|example) ' research/R41D/DraftB.lean`:
  found exactly the local `def IsR41DForceClass` and
  `structure RDensityAPI`.
- `. scripts/lean-env.sh && make check`: exit 0. The checker printed its known
  copied-source inventory (including `source_hashes_match: false` and admission
  tokens in copied sources) but all enforced checks completed successfully;
  contract-policy tests reported 13/13 passing and the work queue was
  consistent.
- An initial environment command run from inside `verification/` failed before
  Lean started because `scripts/lean-env.sh` was addressed relative to the
  wrong directory. It was immediately replaced by the successful root-sourced
  command above; no files were affected.
