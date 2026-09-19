# Lane 451-T20-U13-assembly-registration — T20 U13: assemble `CriticalRegularityTAPI` (23 fields) and register `T03.critical_regularity`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) worker in
`/data_8T/ping/blowup_density/.claude/worktrees/451-T20-U13-assembly-registration` (branch `erenup/451-T20-U13-assembly-registration`). All twelve mathematical units are landed:
`Section3/T20/{MeanReduction (U1 reductionRegular, U2 meanBound/meanIdentity, U6 meanFreeEquation), BIntegral (U3), ConstantTransport (U4 constantTransportSkew), CriticalTrilinear (U7, C₀ := criticalTrilinearConst),
CriticalEnergy (U8), YBound (U9: criticalSmallness, yBound_of_le), H1Trilinear (U10a, C₁ := h1TrilinearConst), H1Energy (U10b: CH1 = 2, criticalSmallnessH1, criticalSmallnessH1_le_half, _lt_quarter_C₀, _lt_quarter_C₁),
Continuation (U11: Ccriterion, Ccriterion_pos), GlobalRegularity (U12)}.lean`. **U5 `constantTransportCommutesLambda` was never needed by any unit** (U8/U10b run on the Fourier side) — check whether the
canonical structure still has that field; if it does, it must be proved here (Fourier side: constant transport is the multiplier `Σⱼ mⱼ·2πikⱼ`, which commutes with the multiplier `2π|k|` — reuse lane
415's `periodicFourierCoeff_fderiv_dir` and `lambdaCoeff`) — read the field text first. Read `CLAUDE.md` (contract import rules: `Contracts/*` import only `Mathlib`/`Contracts.*` + whitelist;
restated definitions bridged by `rfl`; `ClassicalSolutionT` structure exception → fieldwise conversions as in `Bindings/TorusLocalTheory.lean`; `ensure_ascii=False, indent=2`), **`research/T20/T20_SPLIT.md`
§0 and unit U13** (`:266-272`), `Section3/T20/CriticalRegularity.lean` (structure `:139-368`, statement `:374`), `research/T20/Spec.lean` (the reconciled text the contract must match token-for-token),
every `research/T20/REPORT_{389,390,413,415,428,429,432,437,441}.md` §1 (which constant each unit fixes and which `c` it needs: install `c := criticalSmallnessH1`, `C₀ := criticalTrilinearConst`,
`C₁ := h1TrilinearConst`, `CH1 := 2`, `Ccriterion`; `yBound` via `yBound_of_le criticalSmallnessH1_le_half`), the registration precedents `Contracts/V1/TorusLocalTheory.lean`/`Bindings/TorusLocalTheory.lean`/
`Tests/TorusLocalTheory.lean` and lane 427's `Contracts/V1/MeanZeroCalculus.lean` trio, `verification/contracts.json`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`/placeholder fields; no edits to existing modules (new files plus the registry/work-items additions); every restated definition bridged by `rfl` (or fieldwise
  conversion for `ClassicalSolutionT`); every declaration prints exactly `[propext, Classical.choice, Quot.sound]`.

## Deliverables
1. `formalization/NSFormalization/Section3/T20/Assembly.lean`: `def criticalRegularityT : CriticalRegularityTAPI := { c := criticalSmallnessH1, C₀ := …, …, reductionRegular := …, …, globalRegularity := … }`
   (all 23 fields from the landed theorems), `theorem criticalRegularityStatement_holds : criticalRegularityStatement`, and a non-vacuity example at a **nonzero** compactly time-supported force in
   `forceClassT` (grep `T11/Assembly.lean:525 periodicLocalTheoryAPI_nonvacuous`'s bump; scale it so `criticalRho g < c·ν` for some `ν` — if the small-datum instance needs a local-existence solution
   that the tree cannot produce at that scale, state exactly what is missing and keep the zero-force instance).
2. `verification/Contracts/V1/CriticalRegularity.lean`: `CriticalRegularityTAPI` token-for-token from `research/T20/Spec.lean` over the registered `Contracts/V1/TorusLocalTheory.lean` vocabulary
   (restate verbatim only unregistered notions: `criticalY/Z/B/Rho`, `meanFreeVelocity/Force`, `squaredHTwoIntegralT`, `gradientSqT`, … with provenance comments), `criticalRegularityStatement`.
3. `verification/Bindings/CriticalRegularity.lean`: `rfl` bridges / fieldwise conversions, the instance from the canonical record (`maximalLifespanT` through `Bindings.TorusLocalTheory.maximalLifespanT_eq`,
   as `research/T21/RECONCILIATION.md` §0 point 2 prescribes), `criticalRegularityStatement_holds`.
4. `verification/Tests/CriticalRegularity.lean`: `checkedCriticalRegularity`, `run_cmd TestSupport.checkAxioms`, conformance `example`s for three fields against `Spec.lean`, non-vacuity.
5. Registry entry `T03.critical_regularity` (`version: 1`, `parent_task` per the T20 work item, honest `scope` incl. that `c` is `criticalSmallnessH1` and constants are closed terms), `work_items.json` +
   `python3 experiments/tasks.py render`; records `research/T20/ATTEMPTS_U13.md`, `research/T20/axioms_u13.lean`, U13 status in `T20_SPLIT.md`.

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root; `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` (exit 0, `registered_contracts` = base + 1, `base_compatibility_checked: true`);
the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T20/REPORT_451.md`.
