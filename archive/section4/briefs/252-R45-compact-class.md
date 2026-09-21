# Lane 252-R45-compact-class — Corollary 4.5 (cor:Rclasses) for the compactly supported class `Y = F_c`: the `density` and `zeroIff` fields of `research/R45/Spec.lean` at `Y = forceClassCompact`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/252-R45-compact-class` (git branch `erenup/252-R45-compact-class`, based on `origin/erenup/integration`, which contains the reconciled
`research/R45/Spec.lean` (`RClassesAPI`: `density`, `zeroIff`, `schwartzDensity`, `regularReference` — parametric `Y` with `Y = forceClassCompact ∨ Y = forceClassRapid`; **this lane does the
`Y = forceClassCompact` instances of `density` and the `→`/`←` of `zeroIff`**; the rapid instances wait for lane 234's class facts), `research/R45/COMPARISON.md` (§ proof dependencies),
lane 235's `verification/Bindings/DensityFromInsertion.lean` (`breakdownDenseR_of_subcritical` for `Y = F_R` — **the template**; its proof: two cases on `T_max(a,g) ≤ T`, else lane 233's record
`insertionLifespanV2_of_data` + `forceConvergence` + `lifespan` + `memForceR_force`), lane 233's `Bindings/InsertionFromData.lean` (+ its import caveat: not with `Bindings.Packet`),
lane 249's `Bindings/MainThresholds.lean` (how the `→` of the zero-datum `iff` is derived from lane 232's `not_breakdownDenseR_zero_of_q` for `F_R`), the registered R42 record
`Contracts/V1/InsertionFamily.lean` (`forceDifference_compact : ∀ ε, MemForceCompact (fun z => force ε z − g z)` — the fact that makes `g_ε ∈ F_c` when `g ∈ F_c`),
`Section4/R42/Lifespan.lean:199` `memForceR_insertedForce (hg : MemForceR g) … : MemForceR gε` (F_R is closed under compact perturbations — apply it with `g = 0` to get `F_c ⊆ F_R`),
`Contracts/V1/Data.lean:544-570` (`MemForceR`, `MemForceCompact`, `forceClassCompact`, `breakdownSetIn`), `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P10, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; heartbeats ≤ 400000 per declaration, commented. No edits to existing modules/Bindings/Tests; new files only. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`; non-vacuity `example`s (`ν = T = 1`, `a = 0`, `g = 0`, `q = 1`, `s = 0`).
- **Statement fidelity:** the theorems must be the `Spec.lean` fields specialized to `Y = forceClassCompact` (binder shapes identical), so that a later registration can combine them with the
  rapid instances by `Or.elim`.
- **Satisfiability rule:** if a class fact resists (e.g. `F_c ⊆ F_R`), isolate it as ONE named hypothesis with the exact statement and say which lane owes it (234).

## Goal (in `verification/Bindings/CompactClassDensity.lean`, namespace `BlowupDensity.Bindings`)
1. `memForceCompact_add_memForceCompact` / closure: `MemForceCompact g → MemForceCompact (fun z => f z − g z) → MemForceCompact f` (sum of two compactly supported smooth forces), and
   `memForceR_of_memForceCompact : MemForceCompact f → MemForceR f` (via `memForceR_insertedForce` at `g = 0`, or directly).
2. `density_compact : ∀ ν T, 0 < ν → 0 < T → ∀ q, (q = 1 ∨ q = 2) → ∀ s, s < criticalOrder q.toReal → ∀ a ∈ initialClassR, RelativelyDense q s forceClassCompact (breakdownSetIn forceClassCompact ν a T)`
   (235's two-case proof with `Y = F_c`: in the second case the inserted force is in `F_c` by item 1 and `forceDifference_compact`; `T_max(a, g_ε) = T` from the record).
3. `zeroIff_compact`: `←` = item 2 at `a = 0`; `→`: from `RelativelyDense … F_c (breakdownSetIn F_c ν 0 T)` and `s ≥ criticalOrder`, derive a contradiction with lane 232/249's `F_R` non-density:
   `breakdownSetIn F_c ν 0 T ⊆ breakdownSetRZero ν T` (item 1) and `0 ∈ F_c`, so the `F_c`-relative ball around `0` of radius `ρ` would contain a breakdown force of `F_R`-norm `< ρ`.
4. Audit `research/R45/axioms_compact_class.lean`; records `research/R45/ATTEMPTS_COMPACT.md`; update `research/R45/COMPARISON.md` (which instances are proved).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build Bindings.CompactClassDensity` (silent), `lake env lean Bindings/CompactClassDensity.lean` (0 output), the audit, `make check`, `make test`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R45/REPORT_252.md`.
