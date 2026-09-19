# Lane 449-T23-SPLIT-plan — T23 proof-lane split (`cor:boundary`, interior no-slip insertion): `research/T23/T23_SPLIT.md`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **planning** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/449-T23-SPLIT-plan` (git branch `erenup/449-T23-SPLIT-plan`, based on `origin/erenup/integration-section3`). Read `CLAUDE.md`, the reconciled
statement `research/T23/Spec.lean` (`CutoffData :130`, `BoundedDomainNormAPI :278` (copied — T22 is now registered as `T04.bounded_domain_norm`, `Contracts/V1/BoundedDomainNorm.lean`, so the copy
is replaced by the registered contract at proof time), `DomainPlacementData :374`, `ClassicalSolutionOmega :542`, `BoundaryInsertionAPI :690` (the 48+16+10-field family per `RECONCILIATION.md`),
`boundaryInsertionStatement :1037`), `research/T23/RECONCILIATION.md` (§0 lead approval, §1 agreement, §2 rulings, "False clauses / traps", §3 decisions binding for the finalization lane, §4 next),
`research/T23/COMPARISON.md`, the paper `paper/sections/03-torus.tex:632-667` (`cor:boundary` and its proof), the suppliers it consumes: whole-space scaling/correction (registered `I02`/`I03`
contracts, `Contracts/V1/{Correction,Scaling}.lean` — read what is registered), the T22 norm layer (`Section3/T22/*`, `T04.bounded_domain_norm`), the T18 insertion layer (`Section3/T18/*`: U1–U6, U8
landed; U7 lane 435, U9–U11 lanes 443/445 in flight; U12 assembly next — the T18 canonical `InsertionData` conventions in `research/T18/REPORT_422.md`), the T11 canonical local theory
(`Section3/T11/*`), and the house-style split documents `research/T18/T18_SPLIT.md` and `research/T20/T20_SPLIT.md` (format, peeling rule, waves, risks).

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- This is a **planning** lane: no Lean proofs, no placeholder fields, no edits to existing modules. Every claim "X is in the tree" must be verified by `grep -rn`/`sed -n` and cited with file:line; every claim "X is missing" must show the grep that returned nothing. Read the paper lines you cite with `sed -n`.

## Deliverable
`research/T23/T23_SPLIT.md`: the T23 proof-lane split in house style (model legend **codex-sol = bookkeeping/transport, codex-astra = analytic core**; no Opus): §0 ground rules (peeling rule; which
objects are threaded (whole-space Scaling/Correction records, the T22 registered contract, the T18 canonical layer if reusable — say exactly which T18 theorems transfer to `Ω` and which need
re-proof because `ClassicalSolutionOmega` is a different structure), which are registered); §1 units of S/M/L size covering **every** field of the three structures and the statement: the cube-free
`DomainPlacementData` construction and the interior ball geometry, the un-periodized `scaledPacket` on `Ω` (whole-space fields restricted), the no-slip boundary retention (`u_ε = v` near `∂Ω`:
support localisation from the whole-space `I02` support fields + placement), the domain-vs-zero-extension norm comparison (T22 `zeroExtensionComparison`/`orderZero` applied to the difference), the
no-slip uniqueness / lifespan-exactly-`T` clause (which whole-space or domain uniqueness result supplies it — grep `Section4`, `Paper1`, `vendor` for domain/no-slip uniqueness and say honestly if
it is missing: then it is an L unit with an exact statement), the closeness rates (`eq:Eclose`-type on `Ω`), the assembly + statement + contract/bindings/tests unit (gated on T18 U12 and the
owner questions in `RECONCILIATION.md` §3); each unit with exact targets (Spec lines), verified routes (file:line), size, model, deps; §2 dependency ledger; §3 waves (what can start now vs. gated
on T18 U12); §4 risks (the "any interior ball" encodings rejected as false in the reconciliation; the structure-exception conversions; which owner questions block registration). Commit on your
branch. Report in four parts; write it to `research/T23/REPORT_449.md`.
