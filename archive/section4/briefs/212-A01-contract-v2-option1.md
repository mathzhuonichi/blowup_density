# Lane 212-A01-contract-v2 — register the A01 local theory as a V2 contract (OPTION 1: fixed-force H⁷ narrowing of `horizon_lower_bound`, owner-approved)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/212-A01-contract-v2` (git branch `erenup/212-A01-contract-v2`, based on `origin/erenup/integration`, which contains lane 211's
`Section4/A01/LocalTheoryBundle.lean` (`LocalCarrier`, `localCarrier`, `localHorizon'`, `manuscriptLocalRegularity_localCarrier`, `horizon_lower_bound_H7_fixedForce`,
`ManuscriptHorizonLowerBoundH1` (def only), the API-shape probe `research/A01/probes/local_theory_api_shape.lean`), lanes 208/209/210, and the registered A01 V1
`verification/Contracts/V1/…` (`A01.regularity_partial` — find its file, Bindings and Tests, and the registry entry `A01.*` in `verification/contracts.json`)). Read `CLAUDE.md`
(contract import rules, `rfl` bridges, the `ClassicalSolutionR` structure exception: bind through the field-wise conversion of `Section4/A02/Restrict.lean` §0; `ensure_ascii=False`;
frozen V1 files), `collaboration/HANDOFF.md` §0, **`research/A01/Spec.lean`** (`LocalTheoryAPI` `:255-345`, `ManuscriptLocalRegularity` `:167-230`), `research/A01/REPORT_211.md`,
`REPORT_210.md` §3, `NEXT_SESSION.md` (entry "spec 问题" and the owner's decision recorded below), and the top 40 lines of `logs/LESSONS.md`.

**Owner decision (recorded by the lead):** the V2 field `horizon_lower_bound` is the fixed-force H⁷ version — `∀ ν > 0, ∀ f, MemForceR f → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ > 0,
∀ a, a ∈ initialClassR → sobolevENorm 7 a ≤ K → δ ≤ horizon ν a f` — with a docstring recording the narrowing relative to the manuscript's H¹ wording (Appendix A:147-150,
Tao H¹ theory) and the reason (A04's restart, the only consumer, restarts the same force with Grönwall-bounded high norms; `research/A01/REVIEW.md` M5). The H¹ wording is
kept as a separately named, unregistered `Prop` in the contract file's docstring/`example` (not a field).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/placeholder `Prop` fields; do not modify existing `Contracts/V*` or `Tests/*`. `Contracts/*` import only `Mathlib`/`Contracts.*` (+ the whitelist
  in `experiments/check_contracts.py`); restated definitions bridged by `rfl` in `Bindings/`; `ClassicalSolutionR` via the field-wise conversion + round-trip lemmas.

## Deliverables
1. `verification/Contracts/V2/LocalTheory.lean`: `structure LocalTheoryAPI` with fields `horizon`, `solution`, `regularity : ManuscriptLocalRegularity …` (restate
   `ManuscriptLocalRegularity` **token-for-token from `Spec.lean:167-230`** with its definitions restated + bridged), and `horizon_lower_bound` in the owner-approved form above;
   docstrings cite the paper lines and record the narrowing. If the V1 `A01.regularity_partial` API can be `extends`-ed, do so; else a fresh structure with the accessor lemmas of
   `Spec.lean` §4.
2. `verification/Bindings/LocalTheoryV2.lean`: instance from lane 211's `localCarrier` / `localHorizon'` / `manuscriptLocalRegularity_localCarrier` / `horizon_lower_bound_H7_fixedForce`,
   with the `rfl` bridges for every restated definition and the `ClassicalSolutionR` conversion; `regularityPartial_of_v2 := …` if V1 extends.
3. `verification/Tests/LocalTheoryV2.lean` (`checkedLocalTheoryV2`, `run_cmd TestSupport.checkAxioms`, conformance `example`s restating fields against `Spec.lean`).
4. Registry entry `A01.local_theory_v2` (`version: 2`, `parent_task: A01`, honest scope: existential positive horizon selected uniformly; H⁷ fixed-force uniformity; H¹ wording
   open), `ensure_ascii=False, indent=2`, additions only; `work_items.json` + `python3 experiments/tasks.py render`; V2-specific mutation cases (`extra_axiom`, `weakened_hypothesis`).
5. Records `research/A01/ATTEMPTS_CONTRACT_V2.md`, `research/A01/COMPARISON.md` update (registered V2), conformance `research/A01/axioms_contract_v2.lean`.

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root; `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` (exit 0, `registered_contracts: 30`,
`base_compatibility_checked: true`); the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Also write it to `research/A01/REPORT_212.md`.

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
