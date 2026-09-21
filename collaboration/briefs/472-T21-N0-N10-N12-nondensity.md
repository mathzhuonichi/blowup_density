# Lane 472-T21-N0-N10-N12-nondensity — T21 bundles Z + D + F + C + B: units N0–N10 and N12 (the `NonDensityAPI` side of `cor:nondensity`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/472-T21-N0-N10-N12-nondensity` (git branch `erenup/472-T21-N0-N10-N12-nondensity`, = `origin/erenup/integration-section3` with T19 registered (`T03.density`, #435) and T20 registered (`T03.critical_regularity`, #415)).
Read `CLAUDE.md`, **`research/T21/T21_SPLIT.md`** (lane 448: §0 ground rules; §1 units N0–N10 and N12 — verbatim targets, routes, suppliers; §2 ledger; §4 risks), `research/T21/RECONCILIATION.md` §3–§4, `research/T21/Spec.lean` (`NonDensityAPI` 9 fields over `c : ℝ`,
`criticalBallT`, `breakdownSetTZero`, the four arrow-type statements), the canonical T20 record and inhabitant (`Section3/T20/CriticalRegularity.lean` `CriticalRegularityTAPI`; `Section3/T20/Assembly.lean` — the canonical inhabitant and `c = criticalSmallnessH1`),
and the **suppliers already in the tree** (verify each by `grep -n`; the split predates some of them): `Section3/T18/SobolevRate.lean:116 forceSobolevENormT_add_le` (= N6, the `L¹` force-norm triangle inequality — do not re-prove), `:139 persistenceDown_norm_le` (N1's contraction),
`Section3/T15/Convergence.lean:32 persistenceDown_norm_le_one`, `:44 forceSobolevENormT_mono_order` (= N3, force Sobolev monotonicity for any `q`, `s ≤ r`), `Section3/T19/Bookkeeping.lean:238 torusForceSobolevENorm_zero` (N5's zero norm), `:55 thresholdValue`,
`Section3/T20/CriticalEnergy.lean:402 zero_mem_initialClassT` (= N12), `Bindings/TorusLocalTheory.lean` (`maximalLifespanT_eq`, `initialClassT_eq`, the norm bridges), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first
  (`lake build NSFormalization.Section3.T20.Assembly NSFormalization.Section3.T19.Bookkeeping NSFormalization.Section3.T18.SobolevRate NSFormalization.Section3.T15.Convergence`).
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only, all under `formalization/NSFormalization/Section3/T21/` (no `verification/` files in this lane —
  the registration lane writes those; where the split says `verification/Bindings/TorusNonDensity.lean` for N0, put the canonical version in `Section3/T21/CriticalBridge.lean` over the canonical T20 record instead).
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
Canonical modules in `Section3/T21/` (namespace `NSFormalization.Section3.T21`), each theorem's type literally the `NonDensityAPI` field (probe by `exact` against `research/T21/Spec.lean`, with `c` a variable and, where the split threads `K : CriticalRegularityTAPI`, over
`K` or over the explicit hypotheses `hc : 0 < c` + `K.criticalGlobalRegularity`-shaped input — follow the split): N0 `criticalGlobalRegularity` (from the canonical T20 inhabitant's `globalRegularity` through `maximalLifespanT_eq`), N1/N2 `sliceSobolevMonotone` (reuse
`persistenceDown_norm_le`; prove only the datum transport + `le_iInf`/`iInf_le` bookkeeping), N3 `forceSobolevMonotone` (specialise `forceSobolevENormT_mono_order` at `q = 1`, `1/2 ≤ s`), N4 `(0 : SpaceTimeField) ∈ forceClassT`, N5 `zeroMemBall`, N7 `ballRelativelyOpen`
(via `forceSobolevENormT_add_le`), N8 `criticalBallDisjoint`, N9 `ballDisjoint`, N10 `nonDensity`, N12 `zeroInitialClass` (transport of `zero_mem_initialClassT`). Then `def nonDensityAPI (K : CriticalRegularityTAPI …) : NonDensityAPI K.c` (or with the exact parameters
the Spec's `nonDensityOfCritical` uses — read `Spec.lean:595`) assembling the nine fields — this is the inhabitant the registration lane will bind. Deliverables: the modules, `research/T21/probes/nondensity_closes.lean` (every field by `exact` + `nonDensityOfCritical`
instantiated), `research/T21/axioms_n0_n12.lean`, `research/T21/ATTEMPTS_N0_N12.md`, status lines in `T21_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build <each new module>` (0 errors), `lake env lean` on each (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T21/REPORT_472.md`.
