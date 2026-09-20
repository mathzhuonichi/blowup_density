# Lane 164-D01-g1-homogeneous-norm — D01 gap G1: the datum-form homogeneous norm `dotHomogeneousENorm`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/164-D01-g1-homogeneous-norm` (git branch
`erenup/164-D01-g1-homogeneous-norm`, based on `origin/erenup/integration`). Read `CLAUDE.md`
(especially the contract import rule and the `Contracts/V1` freeze), `collaboration/HANDOFF.md` §0
(rules) and §2 P4, and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree. Never touch `/data_8T/ping/blowup_density` (root checkout) or any
  other worktree. Never `git push`, never merge, never rebase. Committing on your own branch is allowed.
- Lean setup: `. scripts/lean-env.sh` in every shell; `lake` ONLY from `verification/`
  (`cd verification && LEAN_NUM_THREADS=6 lake build …`); drafts via `lake env lean ../research/D01/<file>.lean`.
- No `sorry`, `admit`, `axiom`, `native_decide`, no placeholder `Prop` fields. Do not edit
  `verification/Contracts/V1/*`, `Contracts/V2/*`, existing `Tests/*`, or existing formalization
  modules; new files only. `verification/Contracts/*` may import only `Mathlib`/`Lean`/`Init`/`Contracts.*`
  (+ the whitelist in `experiments/check_contracts.py`); definitions used in a contract must be
  restated verbatim there and bridged by `rfl` theorems in `verification/Bindings/`.
- Before claiming a lemma is "not in the tree", `grep -rn` all of
  `formalization/NSFormalization/Section4/{D01,A03,A04,B02,A05}`. Before citing a paper line, `sed -n` it.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
Gap **G1** of `research/R43/COMPARISON.md` §4 (blocks *stating* Propositions 4.3/4.4): the
datum-form spatial homogeneous norm `‖z‖_{Ḣ^s}` on a physical field `z : SpatialField`, in the shape
the R43 spec uses locally (`research/R43/Spec.lean`, its `def dotHomogeneousENorm`; also see
`research/R44/Spec.lean` and `research/A05/Spec.lean:366`): roughly
`def dotHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ := ⨅ G : {G : RealVectorSobolev s // IsHomogeneousSlice … z G}, ‖G‖ₑ`
— read the actual local definitions in those three spec files and reconcile them (they were
written independently; record every difference). **Do not use** `Contracts.V1.Data.dotHHalfENorm` /
`dotHThreeHalvesENorm` (pointwise Fourier integrals, junk `0` off `L¹ ∩ L²`; see
`PLAN.md` §9 "D01 定义缺口（037 发现）").

Reuse first: `Section4/B02/*` (`homogeneous_partial` v1/v2 contracts already carry a homogeneous
datum object and `IsHomogeneousSlice`-style predicates — `verification/Contracts/V2/HomogeneousPartial.lean`),
`Section4/D01/HalfOrder.lean`, `SmoothDatum.lean` (`sobolevENorm` is the inhomogeneous analogue:
copy its infimum-over-data shape), `Paper1/SchwartzCriticalEmbedding.lean:57,171` (what the
Riesz-potential embedding consumes as its right-hand side — the definition must feed it).

## Deliverables
1. New module `formalization/NSFormalization/Section4/D01/HomogeneousNorm.lean`
   (namespace `NSFormalization.Section4.D01`): `dotHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞`
   plus the basic lemmas a consumer needs: monotonicity in the datum (`le_of_isHomogeneousSlice`),
   `dotHomogeneousENorm_zero`, the relation to the inhomogeneous `sobolevENorm` when both are
   finite (`dotHomogeneousENorm s z ≤ sobolevENorm s z` for `0 ≤ s`, if the tree's datum objects
   make this a short lemma), and `≠ ⊤` for a field that has a homogeneous datum.
2. Contract-side restatement ready for registration: `verification/Contracts/V2/Data.lean` (or a
   new `Contracts/V2/HomogeneousNorm.lean` importing only `Contracts.V1.Data`/Mathlib) restating the
   definition verbatim, `verification/Bindings/HomogeneousNorm.lean` with the `rfl` bridge
   `theorem dotHomogeneousENorm_eq : Contracts….dotHomogeneousENorm = D01.dotHomogeneousENorm := rfl`,
   a `Tests/HomogeneousNorm.lean` with `run_cmd TestSupport.checkAxioms`, and the `contracts.json`
   entry (id `D01.homogeneous_norm`, `version: 1`, `parent_task: D01`, write the JSON with
   `ensure_ascii=False, indent=2`, additions only). Run `python3 experiments/tasks.py render` after
   editing `collaboration/work_items.json` if the tooling requires it (`make check` will tell you).
3. Records: `research/D01/ATTEMPTS_G1.md` (the three spec-local definitions side by side, what was
   reconciled, why `dotHHalfENorm` is unusable); `research/D01/axioms_g1.lean`.

## Gates (run all, paste outputs)
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.D01.HomogeneousNorm`
(silent); `lake env lean` on the module (0 output); `scripts/gates.sh NSFormalization.Section4.D01.HomogeneousNorm`
from the worktree root (runs `make check`, `make test`, `make test-mutations`);
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration` (exit 0,
`registered_contracts: 27`, `base_compatibility_checked: true`); the axioms file.

## Report
Commit on your branch and end with a four-part report: 1. what is defined/proved (exact statements);
2. what is in Lean now (files, registry entry); 3. gaps; 4. commands and results.
Also write it to `research/D01/REPORT_164.md`.
