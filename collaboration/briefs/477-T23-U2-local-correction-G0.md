# Lane 477-T23-U2-local-correction-G0 — T23 U2: the G0 counterexample + repaired statement, and the local correction supplier (cutoff data + cross-transport identities)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/477-T23-U2-local-correction-G0` (git branch `erenup/477-T23-U2-local-correction-G0`, = `origin/erenup/integration-section3`). Lane 476 works in parallel on U1 (`Section3/T23/Placement.lean`); do not create that file — if you need placement fields, thread them as hypotheses.
Read `CLAUDE.md`, **`research/T23/T23_SPLIT.md`** (§0 — statement gate G0, supplier audit, "consume versus thread", exact T18 transfer boundary; §1 U2 verbatim: the seven `CutoffData` fields `Spec:135-170`, API `crossTransport_background_advects_packet:879`, `crossTransport_packet_advects_background:888`, the I02/I03 bridge and the
radial-potential-with-cutoff route; §4 risks 1, 4, 7, 8), **`research/T23/SPEC_ISSUES.md` §G0** (lead ruling: (a) formalise the counterexample against the literal `boundaryInsertionStatement` (`Spec.lean:1037-1050`) — e.g. `not_boundaryInsertionStatement` or the exact false instance at `D.ε₀ = 0`; (b) state the repaired
`boundaryInsertionStatement'` which produces the cutoff **existentially** from the consumed correction, mirroring `Section3/T17/Assembly.lean: correctionStatementAmended` (hypothesis block spelled out, `0 < r`, ball inclusions); record both in `research/T23/SPEC_ISSUES.md` §G0 addendum with the exact Lean text), the whole-space suppliers
`verification/Contracts/V1/Correction.lean` (`I02.correction`: `correction_support:359`, `correction_support_ball:364`, `correction_cancels_germ:385`, `force_support:433`, `force_support_ball:444`, `force_formula:415`; `reference_divergence_free:230` is global — the local bridge is the point of U2), `Section3/T16/LocalPotential.lean` (the torus local potential: `localPotentialData`,
`localPotentialAPI` — its radial potential + cutoff construction is the model), `Section3/T17/SlabBridge2.lean` (how a time cutoff + window agreement transferred global-hypothesis lemmas to a local reference — the same trick likely applies spatially here), `Section3/T18/CrossTransport.lean:46` (open-neighbourhood cancellation argument), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure you need first.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only under `formalization/NSFormalization/Section3/T23/` and `research/T23/`. **Never import `Paper1/BoundaryCorollary.lean` or any module that imports it** (sorry-bearing); re-implement the elementary geometry you need.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.
- **Incremental output**: commit a first module skeleton within 15 minutes and commit after each closed lemma, so a session death keeps partial work.

## Goal
1. `Section3/T23/StatementRepair.lean`: the literal Spec statement copied canonically, its refutation (kernel-checked counterexample), and the repaired statement `boundaryInsertionStatement'` (definition only; its proof is U9's job).
2. `Section3/T23/LocalCorrection.lean`: the canonical raw-field `CutoffData` (seven fields, token-for-token from `Spec:135-170`) and a **constructor** producing, for a reference `v` smooth and divergence-free on the interior cylinder `Ioo 0 (T+δ) ×ˢ ball x₀ r` with `closure (ball x₀ r) ⊆ Ω`, one positive threshold and one `D` whose fields are *proved* (smoothness, curl/divergence,
   cancellation, support, force estimates) — via the radial potential in a slightly larger interior ball times a fixed compact spatial cutoff equal to one near the construction ball (so global hypotheses of the whole-space suppliers hold for the cut-off field, and window agreement transfers the conclusions back), plus the two cross-transport identities in the API's exact form over the
   un-periodised packet (`Ico` at `t = 0` via the packet's inactive past). Deliver each closed obligation as its own named theorem + probe; if the local bridge does not close in time, deliver the counterexample/repair (1) and the closed sub-lemmas with the exact residual.
Deliverables: the modules, `research/T23/probes/{g0_counterexample,local_correction_closes}.lean`, `research/T23/axioms_u2.lean`, `research/T23/ATTEMPTS_U2.md`, the SPEC_ISSUES addendum, U2 status line in `T23_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T23.StatementRepair NSFormalization.Section3.T23.LocalCorrection` (0 errors), `lake env lean` on each (0 output), the probes, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (statements / files / gaps with error text / commands and results). Also write it to `research/T23/REPORT_477.md`.
