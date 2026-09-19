# Lane 476-T23-U1-domain-placement — T23 U1: cube-free placement and interior geometry (the 16 `DomainPlacementData` fields + `interiorBall_in_domain`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/476-T23-U1-domain-placement` (git branch `erenup/476-T23-U1-domain-placement`, = `origin/erenup/integration-section3`).
Read `CLAUDE.md`, **`research/T23/T23_SPLIT.md`** (lane 449: §0 ground rules/supplier audit — esp. the *unsafe imports* paragraph; §1 U1 verbatim: fields `Spec:378-449`, API `interiorBall_in_domain:720`, the `Kstar`/radius/threshold construction route; §2 ledger; §4 risk 2 "any interior ball must remain literal"),
`research/T23/SPEC_ISSUES.md` (lead ruling G0; U1 is independent of it), `research/T23/Spec.lean:370-460` (`DomainPlacementData`) and `:700-730`, `research/T23/RECONCILIATION.md` §3 (cube-free placement is the approved direction), the analogous T15 construction `Section3/T15/Assembly.lean` (`placementData`, `placementCarrier`, `placementRadius`,
`placementThreshold`, `placement_chart_in_cube` — copy the pattern, replace the cube by the prescribed interior ball `closure B ⊆ Ω`), `verification/Bindings/CorrectionV2.lean:537 isCompact_carrierStar`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure you need first.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only under `formalization/NSFormalization/Section3/T23/` and `research/T23/`. **Never import `Paper1/BoundaryCorollary.lean` or any module that imports it** (sorry-bearing); re-implement the elementary geometry you need.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.
- **Incremental output**: commit a first module skeleton within 15 minutes and commit after each closed lemma, so a session death keeps partial work.

## Goal
New module `formalization/NSFormalization/Section3/T23/Placement.lean` (namespace `NSFormalization.Section3.T23`): the canonical raw-field `DomainPlacementData` record restated token-for-token from `Spec.lean:370-450` (over raw packet fields `u p f K` as T15/T18 do; docstrings cite `03-torus.tex` lines), a **constructor**
`domainPlacementData` for any raw packet (compact carrier, compact force support), any domain `Ω`, any prescribed interior ball (`chartCenter`, `chartRadius > 0`, `closure (ball chartCenter chartRadius) ⊆ Ω`), any `x₀` in that ball and any horizon `T > 0` — with `(domainPlacementData …).T = T` and `.chartCenter = chartCenter` etc. by `rfl` — and the theorem
`interiorBall_in_domain` in the API's exact form. Then a non-vacuity probe with a translated example (a ball not containing the origin, e.g. centre `(5,5,5)`, radius `1`, inside `Ω := ball (5,5,5) 2`). Deliverables: the module, `research/T23/probes/placement_closes.lean` (each field by `exact`), `research/T23/axioms_u1.lean`, `research/T23/ATTEMPTS_U1.md`, U1 status line in `T23_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T23.Placement` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (statements / files / gaps with error text / commands and results). Also write it to `research/T23/REPORT_476.md`.
