# Lane 242 report

## 1. Which theorem was specified

Draft A specifies Proposition 4.6 (`prop:Renergy`),
`paper/sections/04-whole-space.tex:218-229`: density of finite-lifespan smooth
compact forces in the two inhomogeneous completed Bochner families and in the
homogeneous energy-force completion, together with same-family strong closure
of the inserted velocity trajectories and force differences.

## 2. What Lean now contains

`research/R46/DraftA.lean` contains the statement-only structure `REnergyAPI`
with three clause fields:

- completed `L^q_tH^s_x` density for `q∈{1,2}` and `s<s_q`;
- completed `L²_tḢ⁻¹_x` density with the homogeneous realization;
- an existential Theorem 4.2 insertion family satisfying the energy limit and
  the literal summed three-norm force limit simultaneously.

The only local definition is the concrete `StrongTrajectoryClosure` predicate,
marked “needs registration”. `research/R46/COMPARISON_A.md` records the
paper-to-Lean mapping, completion/path choices, and ambiguities.

## 3. What remains missing

This lane provides no proof, binding, or registered contract, as requested.
The combined closure predicate still needs registration if this draft is
selected. The registered `InsertionFamilyAPI` intentionally does not include
Theorem 4.2's maximal-lifespan equality; Draft A does not duplicate that
presupposed theorem clause in Proposition 4.6's closure field. No background
homogeneous-force membership is assumed.

## 4. Commands run and results

- `cd verification && lake env lean ../research/R46/DraftA.lean` — passed with
  no output (run twice, before and after documentation).
- `git diff --check` — passed with no output.
- `rg -n '\\b(sorry|admit|axiom)\\b' research/R46/DraftA.lean` — no matches.
- `make check` — passed (architecture, contract-policy, policy-test, and work
  queue checks completed successfully).
- `make test` — passed; only pre-existing dependency linter warnings were
  replayed.
- `make test-mutations` — passed all four mutation cases.
- The three deliverables are committed together on branch
  `erenup/242-SPEC-r46-draft-a`; nothing was pushed, merged, or rebased.
