# Lane 165-A05-critical-l3 — A05: the critical embedding `‖u‖₃ ≤ C·‖u‖_{Ḣ^{1/2}}` (HANDOFF P3)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/165-A05-critical-l3` (git branch
`erenup/165-A05-critical-l3`, based on `origin/erenup/integration`). Read `CLAUDE.md`,
`collaboration/HANDOFF.md` §0 (rules) and §2 P3, and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree. Never touch `/data_8T/ping/blowup_density` (root checkout) or any
  other worktree. Never `git push`, never merge, never rebase. Committing on your own branch is allowed.
- Lean: `. scripts/lean-env.sh` in every shell; `lake` ONLY from `verification/`
  (`cd verification && LEAN_NUM_THREADS=6 lake build …`); drafts via `lake env lean ../research/A05/<file>.lean`.
- No `sorry`, `admit`, `axiom`, `native_decide`; `set_option maxHeartbeats N in` only per declaration,
  `N ≤ 400000`, commented. Do not edit existing modules, `Contracts/V1`, or existing `Tests/*`; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of
  `formalization/NSFormalization/{Section4,Paper1,Source}`. Before citing a paper line, `sed -n` it.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
`research/A05/Spec.lean:366` `velocityCriticalL3`: `‖u‖_{L³} ≤ C(1/2) · ‖u‖_{Ḣ^{1/2}}` for the fields
Proposition 4.3/4.4 use (`04-whole-space.tex:105-112`, the Sobolev embedding `Ḣ^{1/2}(ℝ³) ↪ L³`).
What the tree has: the Riesz-potential route `Paper1/SchwartzCriticalEmbedding.lean:57,171` (right-hand
side is a homogeneous *datum* norm) and the full-order `Source/FractionalRealization.lean:96,78`.
What is missing is the **carrier translation** from those objects to the spec's vocabulary:
`research/A05/COMPARISON.md:205-216` lists units U1–U7 (U9 is done and registered as `A05.gradient_l6`).

Note on the norm: the spec's `Ḣ^{1/2}` norm is the datum-form `dotHomogeneousENorm` (a parallel lane
164 is landing `Section4/D01/HomogeneousNorm.lean`; it is NOT in your worktree). Use the local
definition in `research/R43/Spec.lean` (copy it into your module under a clearly named local `def`
with a docstring saying it will be replaced by D01's) so your theorem is stated against the datum
form, not against `Contracts.V1.Data.dotHHalfENorm` (a pointwise Fourier integral that is junk `0`
off `L¹ ∩ L²` — never use it).

## Deliverables
1. New module `formalization/NSFormalization/Section4/A05/CriticalL3.lean`
   (namespace `NSFormalization.Section4.A05`): the units U1 → U7 as separate lemmas (name each `uN_…`
   with the unit's row cited in its docstring), ending in
   `velocityCriticalL3 : ∀ z : SpatialField, <the spec's hypotheses> → eLpNorm z 3 volume ≤ ENNReal.ofReal (C_half) * dotHomogeneousENorm (1/2) z`
   with an explicit constant (or `∃ C, 0 < C ∧ …` if the constant is not explicit in the tree; say which).
   If a unit does not close, deliver the ones that do and state the exact residual with error text.
2. Records: `research/A05/ATTEMPTS_CRITICAL_L3.md` (route, per-unit status, failed approaches with
   error text); conformance `research/A05/axioms_critical_l3.lean`; update
   `research/A05/COMPARISON.md`'s U-table status column (append a lane-165 note, do not rewrite history).
3. Do NOT register a contract in this lane (A05 V2 registration is a follow-up once D01's norm lands).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A05.CriticalL3` (silent),
`lake env lean` on the module (0 output), `lake env lean ../research/A05/axioms_critical_l3.lean`,
`make check` from the worktree root.

## Report
Commit on your branch and end with a four-part report: 1. theorems proved (names, exact statements,
constants); 2. what is in Lean now; 3. gaps (per unit); 4. commands and results.
Also write it to `research/A05/REPORT_165.md`.
