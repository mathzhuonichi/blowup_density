# Lane 235-R41D-density — Theorem 4.1's density branch for `Y = F_R`: for `q ∈ {1,2}`, `s < s_q`, every `a ∈ X_R`, the breakdown set `B^R_{ν,a,T}` is relatively dense in `F_R` (thm:Rmain (i) and the "if" half of (ii))

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/235-R41D-density` (git branch `erenup/235-R41D-density`, based on lane 233's branch `erenup/233-R42-family-from-data` = `origin/erenup/integration`
+ `verification/Bindings/InsertionFromData.lean` (`insertionLifespanV2_of_data : ∀ ν, 0 < ν → ∀ T, 0 < T → ∀ a ∈ initialClassR, ∀ g, MemForceR g → ofReal T < maximalLifespanR ν a g → ∃ P L, L.family.a = a ∧ L.family.g = g ∧ L.family.T = T`,
`insertionFromData_lifespan`, `insertionFromData_forceConvergence` — read it and `research/R41D/REPORT_233.md`; note its import caveat: do not import `Bindings.Packet` together with it)).
Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P10, the top 40 lines of `logs/LESSONS.md`, the paper `04-whole-space.tex:8-12` (thm:Rmain) and `:176-181` (the proof's two-case split:
"either `T_max(a,g) ≤ T`, then `f := g ∈ B_R` and the distance is `0`; or `T_max(a,g) > T`, then Theorem 4.2 gives `g_ε ∈ F_R` with `T_max(a,g_ε) = T` and `‖g_ε − g‖_{L^qH^s} < ρ`"),
`research/section4/STATEMENTS.md:120-170` (`RMainAPI` skeleton: `densityFixedInitial`, `densityZero`, `nonDensityZero`), `research/R41D/Spec.lean` (`RDensityAPI`, `IsR41DForceClass`; for `Y = F_R`),
`research/R41D/COMPARISON.md` (§3 G1 closed by 233; G5 `forceSobolevENorm q s 0 = 0` — lane 234 (branch `erenup/234-R41D-small-gaps`, running) may prove it in `Section4/R41/ClassFacts.lean`;
if it is not on your base, prove the `q ∈ {1,2}` case locally or find it in `Contracts/V1/DatumLemmas.lean`), `verification/Contracts/V1/Data.lean:660-712` (`breakdownSetR`, `RelativelyDense`,
`BreakdownDenseR`), `Contracts/V1/InsertionFamily.lean:323-332` (`forceConvergence : ∀ q, (q = 1 ∨ q = 2) → ∀ s, s < 2/q - 3/2 → Tendsto … (𝓝 0)` — read the exact form), `:421-440` and
`Contracts/V2/InsertionLifespan.lean:117-160` (`lifespan`, `solution`, `maximal`), `Bindings/InsertionLifespan.lean` (`memForceR_force`: `g_ε ∈ F_R` from `hg`), `Contracts/V1/Thresholds.lean`
(`exponent q s = 2/q - 3/2 - s`), and lane 232's module if present (`Section4/R41/NonDensity.lean`, branch `erenup/232-R41-nondensity-both`, for the "only if" half — read-only).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; heartbeats ≤ 400000 per declaration, commented. No edits to existing modules/Bindings/Tests; new files only. Every declaration must print
  exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (`ν = T = 1`, `a = 0`, `g = 0`, `q = 1`, `s = 0`).
- **Statement fidelity:** the theorems must be in `Data.lean`'s `BreakdownDenseR` vocabulary with the threshold `2/q - 3/2` (cite `Thresholds.lean` `formula`); no re-cut.

## Goal (in `verification/Bindings/DensityFromInsertion.lean`, namespace `BlowupDensity.Bindings`)
1. `breakdownDenseR_of_subcritical : ∀ ν T : ℝ, 0 < ν → 0 < T → ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ, s < 2 / q.toReal - 3/2 → ∀ a ∈ initialClassR, BreakdownDenseR ν a T q s`
   (fix the cast of `q` consistently with `forceConvergence`'s `q` — use the same type). Proof: unfold `RelativelyDense`; given `g ∈ forceClassR`, `r > 0`: split on `maximalLifespanR ν a g ≤ ofReal T`
   (then `f := g`, `forceSobolevENorm q s (g - g) = 0 < r` via G5) vs `ofReal T < maximalLifespanR ν a g` (then `insertionLifespanV2_of_data` → `L`; `forceConvergence` gives
   `ε ∈ Ioc 0 L.family.ε₀` with `forceSobolevENorm q s (L.family.force ε - g) < r`; `L.lifespan ε hε` gives `maximalLifespanR ν a (force ε) = ofReal T ≤ ofReal T`; `memForceR_force` gives
   `force ε ∈ forceClassR`; hence `force ε ∈ breakdownSetR ν a T`).
2. `breakdownDenseR_zero_of_subcritical` (the `a = 0` instance) and, if lane 232's `not_breakdownDenseR_zero_of_q` is available on a branch you can read, the `iff` at `a = 0`:
   `BreakdownDenseR ν 0 T q s ↔ s < 2/q - 3/2` — state it only if both halves are on your base; otherwise state the "if" half and note the "only if" lives in 224/229/232.
3. Audit `research/R41D/axioms_density.lean` (all declarations standard axioms; the non-vacuity example).

## Deliverables
1. `verification/Bindings/DensityFromInsertion.lean`, the audit.
2. Records `research/R41D/ATTEMPTS_DENSITY.md`, update `research/R41D/COMPARISON.md` (which `RMainAPI`/`RDensityAPI` fields are now proved).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build Bindings.DensityFromInsertion` (silent), `lake env lean Bindings/DensityFromInsertion.lean` (0 output), the audit, `make check`, `make test`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R41D/REPORT_235.md`.
