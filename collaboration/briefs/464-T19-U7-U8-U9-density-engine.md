# Lane 464-T19-U7-U8-U9-density-engine — T19 wave 2: `fixedInitialDensity` (U7), `regularReferenceSingular` (U8), `mixedDensity` (U9) from the U0 threading exports

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/464-T19-U7-U8-U9-density-engine` (git branch `erenup/464-T19-U7-U8-U9-density-engine`, = lane 461's branch (459 + 461 on top of integration; 461 in review) + `origin/erenup/integration-section3`).
Read `CLAUDE.md`, **`research/T19/T19_SPLIT.md`** (§0; units U7, U8, U9 verbatim targets and routes; U0 status line added by lane 461), `research/T19/REPORT_461.md` + `Section3/T19/Threading.lean` (`extendByZero`, `insertionData`,
`insertion`, and the **export lemmas** `force_mem`, `lifespan`, `solution`, `blowup_limsup`, `energyRate`, `forceDifference_mixed_bound`, `forceDifference_sobolev_bound`, `forceDifference_negativeSobolev_tendsto`, guards, and
`exists_force_close` — verify every name by `grep -n` in `Threading.lean`), `Section3/T19/Density.lean` (canonical fields `PeriodicDensityAPI.fixedInitialDensity`, `.regularReferenceSingular`, `MixedRegionAPI.mixedDensity` — read the exact
statements), `Section3/T19/Bookkeeping.lean` (U1–U6: `thresholdValue`, `mixedRegionArithmetic` (`0 < alpha p q ∧ 0 < alpha p q + 1` from `3 < 3/p + 2/q`), `torusForceSobolevENorm_zero`, `torusMixedLebesgueENormT_zero`),
`verification/Contracts/V1/TorusLocalTheory.lean` (`RelativelyDenseT`, `breakdownSetT`, `RegularThroughT`, `regularThrough_iff` if present, `maximalLifespanT`), the R³ templates `verification/Bindings/DensityFromInsertion.lean:24-51
breakdownDenseR_of_subcritical`, `Bindings/MainThresholds.lean:97-136 regularReferenceApproximation`, `Bindings/CompletedClosure.lean:180 closure_relativeHomogeneous`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first
  (`lake build NSFormalization.Section3.T19.Threading NSFormalization.Section3.T19.Density`).
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
New module `formalization/NSFormalization/Section3/T19/DensityEngine.lean` (namespace `NSFormalization.Section3.T19`) with three theorems whose types are literally the canonical fields (probe each by `exact` against `Density.lean`):
1. **U7 `fixedInitialDensity`**: `∀ a ∈ initialClassT, ∀ ν > 0, ∀ T > 0, ∀ s < 1/2, RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)`. Unfold `RelativelyDenseT` (registered; read its exact quantifiers), `intro g hg r hr`;
   `by_cases hLife : maximalLifespanT ν a g ≤ ENNReal.ofReal T`: already-singular → witness `g` itself, distance `forceSobolevENormT 1 s (fun z => g z − g z)` = `forceSobolevENormT 1 s 0 = 0 < r` (`torusForceSobolevENorm_zero`; mind
   whether the registered predicate writes the difference as `f − g` or `fun z => f z − g z`); regular → `RegularThroughT ν a g T` from `lt_of_not_ge hLife` through the registered continuation/`regularThrough` bridge (grep
   `regularThrough_iff` / `RegularThroughT` in `Contracts/V1/TorusLocalTheory.lean` and `Section3/T11`), then `exists_force_close` (U0) gives `f ∈ 𝓕` with `maximalLifespanT ν a f = ofReal T` and the distance `< r`; membership in
   `breakdownSetT` is `⟨hf, le_of_eq …⟩`.
2. **U8 `regularReferenceSingular`**: no `by_cases` — the hypothesis is `RegularThroughT ν a g T`; witness from `exists_force_close` with the **exact** lifespan equality.
3. **U9 `mixedDensity`**: `∀ a ∈ 𝓧, ∀ ν > 0, ∀ T > 0, ∀ (p q) [Fact (1 ≤ p)], 1 ≤ q → 3 < 3/p.toReal + 2/q.toReal → RelativelyDenseMixedT q p forceClassT (breakdownSetT ν a T)`. Same dichotomy; already-singular via
   `torusMixedLebesgueENormT_zero`; regular: from U0's `forceDifference_mixed_bound` (`mixedLebesgueENormT q p (fun z => ins.force ε z − g z) ≤ ofReal (C · (ε^{α} + ε^{α+1}))`-shaped — read the exact constant/exponent spelling in
   `Threading.lean`/`Section3/T18/Assembly.lean`) with `mixedRegionArithmetic` giving `0 < alpha p q` and `0 < alpha p q + 1`, both powers `→ 0` along `𝓝[>] 0` (`Real.rpow` continuity / `tendsto_rpow_atTop`-type lemmas as in
   `Section3/T15/Convergence.lean`), so eventually `< r`; pick `ε ∈ Ioc 0 ε₀` (`Ioc_mem_nhdsGT`, `Filter.Eventually.exists`), witness `ins.force ε`. If U0 already exports a mixed "eventually `< r`" lemma, use it.
Deliverables: the module, `research/T19/probes/density_engine_closes.lean` (the three fields by `exact`), `research/T19/axioms_u7_u9.lean`, `research/T19/ATTEMPTS_U7_U9.md`, status lines for U7/U8/U9 in `T19_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.DensityEngine` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T19/REPORT_464.md`.
