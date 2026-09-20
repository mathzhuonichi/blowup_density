# Lane 478-T23-U7-noslip-uniqueness — T23 U7: velocity uniqueness for no-slip classical solutions on a bounded box / smooth domain

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/478-T23-U7-noslip-uniqueness` (git branch `erenup/478-T23-U7-noslip-uniqueness`, = `origin/erenup/integration-section3`). Lanes 476/477 work in parallel on U1/U2 (placement, local correction) — independent of you.
Read `CLAUDE.md`, **`research/T23/T23_SPLIT.md`** (§0; §1 U7 verbatim — the exact theorem target over `ClassicalSolutionOmega`, `IsBoundedBoxOrSmoothDomain`, `initialClassOmega`, `forceClassOmega`; §2 negative-search evidence (no domain uniqueness supplier exists; T11 `velocity_unique` is periodic only); §4 risks 3, 5, 6 — velocity-only uniqueness, no
pressure equality, no connectedness assumption), `research/T23/Spec.lean` (the domain record `ClassicalSolutionOmega` and the domain classes/encoding: regular-level smooth domains + boxes, no-slip boundary condition, normalized pressure — read the exact fields: smoothness on the closed slab, `div = 0`, momentum, boundary values), `research/T23/RECONCILIATION.md` §3 (domain encoding
decisions), the periodic template `Section3/T11/Uniqueness.lean` (`velocity_unique`: difference energy identity + Grönwall — the argument to adapt; the boundary term is what changes), `Section3/T11/EnergyIdentity.lean` (energy identity machinery: integration by parts on the torus), Mathlib's divergence theorem material (`MeasureTheory.integral_divergence_of_hasFDerivWithinAt_off_countable`,
`integral_eq_of_hasDerivWithinAt_off_countable` on boxes; for smooth-level domains check what the encoding gives you — if the smooth-domain branch needs a divergence theorem Mathlib lacks, close the box branch fully and record the smooth-domain residual exactly), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure you need first.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only under `formalization/NSFormalization/Section3/T23/` and `research/T23/`. **Never import `Paper1/BoundaryCorollary.lean` or any module that imports it** (sorry-bearing); re-implement the elementary geometry you need.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.
- **Incremental output**: commit a first module skeleton within 15 minutes and commit after each closed lemma, so a session death keeps partial work.

## Goal
New module `Section3/T23/NoSlipUniqueness.lean` (namespace `NSFormalization.Section3.T23`): the canonical `ClassicalSolutionOmega` (token-for-token from the Spec, raw fields; if U9 later needs a different placement, the lead reconciles) and the theorem `noSlip_uniqueness` in the exact form quoted in `T23_SPLIT.md` U7. Route: for `S < min T₁ T₂`, `w := u₁ − u₂` on `[0,S] × Ω`, `E(t) := ∫_Ω |w(t)|²`,
`E' = −2ν∫|∇w|² − 2∫ (w·∇)u₂ · w` (pressure and boundary terms vanish by `div w = 0` and no-slip `w = 0` on `∂Ω`), `|∫ (w·∇)u₂·w| ≤ ‖∇u₂‖_∞ E` (`u₂` smooth on the compact slab), Grönwall ⇒ `E ≡ 0` ⇒ `w = 0` by continuity. Peel: (i) the boundary integration-by-parts identity for the box case (named lemma, own probe); (ii) the smooth-level domain case (own lemma; if Mathlib lacks the tool,
state the exact residual); (iii) the energy inequality; (iv) Grönwall + continuity. Deliverables: the module, `research/T23/probes/noslip_uniqueness_closes.lean`, `research/T23/axioms_u7.lean`, `research/T23/ATTEMPTS_U7.md`, U7 status line in `T23_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T23.NoSlipUniqueness` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (statements / files / gaps with error text / commands and results). Also write it to `research/T23/REPORT_478.md`.
