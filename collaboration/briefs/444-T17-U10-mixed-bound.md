# Lane 444-T17-U10-mixed-bound — T17 U10: mixed-norm bound of the periodized correction force + honest `L^p` slices

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound` (git branch `erenup/444-T17-U10-mixed-bound`, = lane 439's branch + `origin/erenup/integration-section3`: lane 439's
`Section3/T15/Mixed.lean` (§1 `torusChart`, `map_torusChart`, `eLpNorm_torusLift_eq_restrict`/`_eq_volume` — exponent-generic Haar↔Lebesgue; §2 `mixedLebesgueENorm_eq`; §3 `torusSlicePath`;
§4 `mixedLebesgueENormT_eq` — the torus mixed norm of a periodized compactly-supported field equals the whole-space mixed norm of the copy), `Section3/T17/{Transport,ForceSupport,Energy}.lean`
(lane 425's `force_support`/`source_force_tsupport`, lane 434's slice = `periodize` single copy technique and cube-centred witness), the registered `I02` force mixed bound (`Contracts/V1/Correction.lean:502`
`force_mixed_bound`, from `Paper1/CorrectionMixedNorms.lean:123 physical_force_mixed_bound`, both `∞` endpoints via `toReal ⊤ = 0`; honest `L^p` slices from `physical_force_spatial_memLp:164`)).
Read `CLAUDE.md`, **`research/T17/T17_SPLIT.md` §0 and unit U10** (`:214-222`), the canonical fields `force_spatial_memLp`, `mixedConst`, `mixedConst_nonneg`, `force_mixed_bound` in
`Section3/T17/Correction.lean` (Spec form `research/T17/Spec.lean:920-940`), `research/T17/REPORT_{425,434}.md`, `research/T15/REPORT_439.md` §1 (the "chart lands in the closed cube ⇒ pointwise
equality" observation), `research/T17/SPEC_ISSUES.md` (G1), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure you need first (`lake build <module>`), never assume `.olean`s exist.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
New module `formalization/NSFormalization/Section3/T17/Mixed.lean` (namespace `NSFormalization.Section3.T17`): `def mixedConst : ℝ≥0∞ → ℝ≥0∞ → ℝ` (explicit from the Paper1/I02 constant; `mixedConst_nonneg`
on `1 ≤ p, q`), `force_spatial_memLp` (`∀ p [Fact (1≤p)], ∀ ε ∈ Ioc 0 D.ε₀, ∀ t, MemLp (torusLift (slice of correctionForce)) p periodicTorusMeasure`) and `force_mixed_bound`
(`mixedLebesgueENormT q p (correctionForce ν v D ε) ≤ ofReal (mixedConst p q · ε^{alpha p q + 1})`), types literally the canonical fields at the concrete `correctionData` (probe by `exact`; premise
block as lanes 425/434 incl. G1 `hv`; `alpha` = the canonical copy of `Contracts.V1.alpha` with its drift `example`). Route: `force_eq` writes the periodized force as the lattice lift of the single-copy
force supported in the cube (lane 425), so each slice is `periodize` of a compactly supported smooth slice; lane 439's `mixedLebesgueENormT_eq` (or its ingredients) turns the torus mixed norm into the
whole-space `mixedLebesgueENorm` of the single copy; then the registered/Paper1 Euclidean bound gives `≤ C ε^{α+1}`; slices via lane 439's exponent-generic Haar↔Lebesgue identity + continuity/compact
support. Deliverables: the module, `research/T17/probes/mixed_closes.lean` (fields by `exact`; non-vacuity at lane 434's cube-centred witness), `research/T17/axioms_u10.lean`, `research/T17/ATTEMPTS_U10.md`,
U10 status line in `T17_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.Mixed` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements and constant / files / gaps with error text / commands and results). Also write it to `research/T17/REPORT_444.md`.
