# Lane 256-R46-sobolev-density — Proposition 4.6, first clause: `completedSobolevDensity` of `research/R46/Spec.lean` — smooth compact forces with `T_max(a,f) ≤ T` are dense in the full completed space `L^q(0,∞;H^s)` for `q ∈ {1,2}`, `s < s_q`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/256-R46-sobolev-density` (git branch `erenup/256-R46-sobolev-density`, based on `origin/erenup/integration`, which contains the reconciled
`research/R46/Spec.lean` (`REnergyAPI.completedSobolevDensity : ∀ a ∈ initialClassR, ∀ ν > 0, ∀ T > 0, ∀ q, (q = 1 ∨ q = 2) → ∀ s, s < criticalOrder q.toReal → CompletedDense q s (breakdownSetIn forceClassCompact ν a T)`
— copy it token for token), `research/R46/COMPARISON.md`, `RECONCILIATION.md` §3, lane 252's `verification/Bindings/CompactClassDensity.lean` (`density_compact`: relative density of the compact
breakdown set in `F_c` for the `forceSobolevENorm q s (f − g) < r` metric), the registered B01 contract `verification/Contracts/V1/BochnerPartial.lean` (`BochnerPartialAPI.approxCompact`
`:159-164` — read its exact statement: approximation of any `MemBochnerDatum q s b` by a smooth compactly supported force with an `IsSobolevPath` realization; `compactSubsetForceR`; the
`bochnerSpace`/`completion*` fields; find its binding `verification/Bindings/BochnerPartial*.lean` and the witness name), `Contracts/V1/Data.lean:732-750` (`CompletedDenseVia`, `CompletedDense`:
`∀ b, MemBochnerDatum q s b → ∀ r > 0, ∃ f ∈ S, ∃ D, IsSobolevPath s f D ∧ AEStronglyMeasurable D forceTimeMeasure ∧ bochnerDatumENorm q s (D − b) < r`), `:174` (`IsSobolevPath`),
`:225-236` (`forceSobolevENorm` = infimum over measurable `IsSobolevPath` paths of `bochnerDatumENorm`), the path algebra in the tree (`grep -rn "IsSobolevPath" verification/Contracts/V1/*.lean
formalization/NSFormalization/Section4/D01/*.lean | grep -i "add\|sub\|neg"` — additivity of realizations, needed to combine the path of `g` with a path of `f − g`), `CLAUDE.md`,
`collaboration/HANDOFF.md` §0, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; heartbeats ≤ 400000 per declaration, commented. No edits to existing modules/Bindings/Tests; new files only. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (`ν = T = 1`, `a = 0`, `q = 1`, `s = 0`, target `b = 0`).
- **Statement fidelity:** the theorem is the Spec field verbatim. **Satisfiability rule:** if one step resists (most likely the path additivity or the infimum-to-path extraction), isolate ONE
  named hypothesis with the exact statement.

## Goal (in `verification/Bindings/CompletedSobolevDensity.lean`, namespace `BlowupDensity.Bindings`)
`completedSobolevDensity : <Spec field>`. Route: given `b` and `r`: (1) B01 `approxCompact` gives `g ∈ forceClassCompact` with a measurable path `D_g` and `bochnerDatumENorm q s (D_g − b) < r/2`;
(2) `g ∈ F_c ⊆ F_R` (`compactSubsetForceR` or 252's lemma); 252's `density_compact` gives `f ∈ breakdownSetIn F_c ν a T` with `forceSobolevENorm q s (f − g) < r/2`; (3) unfold the infimum:
a measurable path `E` of `f − g` with `bochnerDatumENorm q s E < r/2`; (4) `D := D_g + E` is a measurable `IsSobolevPath s f` path (additivity) and `bochnerDatumENorm q s (D − b) ≤ ‖E‖ + ‖D_g − b‖ < r`
(triangle inequality in the Bochner datum norm — grep the tree for `bochnerDatumENorm_add_le`/`triangle`). Audit `research/R46/axioms_sobolev_density.lean`; records `research/R46/ATTEMPTS_SOBOLEV_DENSITY.md`;
update `research/R46/COMPARISON.md` (field status).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build Bindings.CompletedSobolevDensity` (silent), `lake env lean Bindings/CompletedSobolevDensity.lean` (0 output), the audit, `make check`, `make test`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R46/REPORT_256.md`.
