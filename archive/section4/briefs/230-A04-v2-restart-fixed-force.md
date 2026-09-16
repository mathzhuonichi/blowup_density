# Lane 230-A04-v2-restart-fixed-force — register A04 V2: the continuation API with `Restart` re-cut to the fixed-force, H⁷-uniform-over-restart-times shape the tree proves (owner-approved wording required before launch)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/230-A04-v2-restart-fixed-force` (git branch `erenup/230-A04-v2-restart-fixed-force`, based on `origin/erenup/integration`). Read `CLAUDE.md`
(contract import rules; frozen V1/Tests; `ensure_ascii=False`; the `ClassicalSolutionR` structure exception and the `maximalPartial_maximalLifespanR_eq` bridge), `collaboration/HANDOFF.md`
§0 and §2 P9b, the top 40 lines of `logs/LESSONS.md`, the A04 V1 trio (`verification/Contracts/V1/*` for A04 — grep `A04` in `verification/contracts.json` to find the registered names/files),
`research/A04/Spec.lean` (`Restart`, `HigherOrderBound`, `restartBeyond`, `extendsBeyond`, `lifespanInfiniteOfLocallyFinite`), `research/A04/COMPARISON.md`, `research/A04/REPORT_215.md` §3,
`REPORT_217.md`, `REVIEW_215-*.md`, `REVIEW_217-*.md`, the landed modules `Section4/A04/RestartFixedForce.lean` (`RestartFixedForce ν f S`, `restartFixedForce_of_memForceR`,
`higherOrderBound_of_gronwall`, `restartBeyond_fixed`, …) and `Section4/A04/ShiftedExtension.lean` (`shiftedLocalExtension`, `restartBeyond_of_memForceR'`, `extendsBeyond_of_memForceR'`,
`lifespanInfiniteOfLocallyFinite_of_memForceR'`), the paper `appendix-a-local-theory.tex:140-157` and `04-whole-space.tex:113-121`, and the most recent registration lanes as templates
(226: `Contracts/V1/CriticalRegularity.lean` + bindings/tests; 181: V2-extends-V1 pattern `GradientL6V2API extends GradientL6API`).

## The owner-approved V2 wording (fill in verbatim from the owner's decision before launch)
`Restart` V2 := `RestartFixedForce`: `∀ ν > 0, ∀ f ∈ F_R, ∀ S ≥ 0, ∀ K ≠ ⊤, ∃ δ > 0, ∀ t₀ ∈ Icc 0 S, ∀ a' ∈ X_R, sobolevENorm 7 a' ≤ K → δ ≤ localHorizon' ν a' (timeShift t₀ f)` — force and
horizon `S` fixed before `δ`; datum bound in `H⁷`. The V1 `Restart` (H¹ bound, uniform over all forces and restart times) stays as a separately named **open** field of the V1 structure
(not claimed); V2 must not silently replace V1: `A04V2API extends A04API`-style is impossible if V1's field is unproved — instead register `ContinuationV2API` with the V2 `restart` field and the
three continuation theorems (`restartBeyond`, `extendsBeyond`, `lifespanInfiniteOfLocallyFinite`) in the shapes lane 217 proved (`…_of_memForceR'`), and a docstring stating exactly which
V1 field is not implied and why (H¹ vs H⁷; cross-force uniformity), citing `REPORT_215.md` §3.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/placeholder `Prop` fields; do not modify existing `Contracts/V*` or `Tests/*`; additions only in `contracts.json`/`work_items.json`.
- **Statement fidelity rule 2:** every field of the V2 structure must be a statement the owner approved (above) or a verbatim copy of a V1/spec field; no other re-cuts.

## Deliverables
1. `verification/Contracts/V2/Continuation.lean` (`ContinuationV2API`: `restart` (V2 wording), `higherOrderBound` (V1 wording, proved by 215), `restartBeyond`, `extendsBeyond`,
   `lifespanInfiniteOfLocallyFinite` in 217's shapes) importing only `Contracts.V1.Data` (+ whitelist).
2. `verification/Bindings/ContinuationV2.lean` (witness from 215/217; `rfl` bridges for the classes/norms; the maximal-lifespan bridge for lifespan statements; `localHorizon'` restated or
   referenced through the whitelist — say which and cite `check_contracts.py`'s `CONTRACT_CANONICAL_MODULES`).
3. `verification/Tests/ContinuationV2.lean` (`checkedContinuationV2`, `TestSupport.checkAxioms`, conformance `example`s against `Spec.lean` and the approved wording).
4. Registry entry `A04.continuation_v2` (`version: 2`, `parent_task: A04`, honest scope: fixed-force H⁷ restart; V1 `Restart` not implied), `work_items.json` + `tasks.py render`.
5. Records `research/A04/ATTEMPTS_V2_CONTRACT.md`, conformance `research/A04/axioms_v2_contract.lean`, update `research/A04/COMPARISON.md`.

## Gates (paste outputs)
`scripts/gates.sh`; `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` (exit 0, `registered_contracts: 31` (or the current count + 1), `base_compatibility_checked: true`);
the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Also write it to `research/A04/REPORT_230.md`.

## Anti-reward-hacking requirements (lead, 2026-09-17, per the user's decision: "按最专业的来；short path 要避免 reward hacking")
1. The V2 structure must NOT contain the paper's H¹ sentence as a proved field, and must not contain placeholder `Prop` fields. Instead the contract file adds
   `def ManuscriptHorizonLowerBoundH1 : Prop := <the paper's H¹ statement verbatim from research/A01/Spec.lean:338-344 (A01) / research/A04/Spec.lean Restart (A04)>` with the docstring
   "the manuscript's sentence; NOT implied by this API; open", and the registry scope says so. Nothing may suggest the H¹ statement is proved.
2. Every docstring of a narrowed field states the exact difference from the paper: fixed force (the force is quantified before ∃ δ) vs uniform in the force; H⁷ datum bound vs H¹;
   uniformity over restart times t₀ ∈ [0,S] (A04).
3. Non-vacuity: `example`s instantiating the V2 fields at a **nonzero** force (grep the tree for a nonzero `MemForceR` witness, e.g. the compact bump used in `research/R43/axioms_force_path.lean`)
   and at a nonzero datum, showing the hypotheses are satisfiable and the conclusion is not vacuous (δ is a genuine positive real).
4. `research/<ID>/COMPARISON.md` gets a section "Paper vs V2": table with columns paper sentence | V1 field (H¹) | V2 field (H⁷, fixed force) | why V2 suffices downstream (cite
   `research/A04/REPORT_215.md` §3: the consumers restartBeyond/extendsBeyond/lifespanInfiniteOfLocallyFinite (217) and A02's exists_maximal (213) restart the same force with
   Grönwall-bounded H⁷ data; cross-force uniformity is never used) | what the H¹ version would need (forced H¹ quantitative local theory on the mild stack).
5. The report's §3 must say plainly which paper sentence is NOT proved. The reviewer will check the V2 statement against the paper adversarially.
