ACCEPT-WITH-NOTES

## what the lane claims

The report claims `restartBeyond` and the exported `glueClassicalSolutionT`, conditional only on `PeriodicQuantitativeLocalInput'`. The API target in `research/T11/probes/api_on_canonical.lean:93-116` has the required order `∃ δ` before `a,u,p`, with `S > 0`, finite `K`, the `SolvesBelowT` pair, the uniform H¹ bound on `Ico 0 S`, and agreement of both velocity and pressure. The implementation theorem is at `formalization/NSFormalization/Section3/T11/RestartBeyond.lean:397-421`; its call to `restart` is at lines 424-425 and the only named input is the exact definition in `formalization/NSFormalization/Section3/T11/LocalExistence.lean:24`.

## what is in Lean

The module contains the claimed slice, restriction, translation, uniqueness, gluing, and restart declarations. `glueClassicalSolutionT` has the stronger existential-with-agreement conclusion at `RestartBeyond.lean:241-252`. `restartBeyond` chooses `t₀ = max 0 (S-d/2)` and proves positivity and reach past `S` at `RestartBeyond.lean:426-434`, then obtains the restart datum and glues it at `RestartBeyond.lean:438-447`. The non-vacuity example is at `RestartBeyond.lean:457-471` and uses the nonzero forced witness.

No `sorry`, `admit`, `axiom`, or `native_decide` occurs in the new module. `git diff --name-only origin/erenup/integration-section3...HEAD` lists only the lane's new module and research records. The report's “not in tree” gap is not a missing-lemma claim requiring acceptance: the stated out-of-scope `ExtendsBeyondT` wiring is a scope boundary, and the Section4 search found only the unrelated R³ restartBeyond declarations.

## gaps

One exact one-line note: the report says the build is “0 warnings”; the module itself is silent, but the transitive build prints existing dependency linter warnings. This does not affect correctness. The report also calls `PeriodicQuantitativeLocalInput'` “LocalExistence.lean:24”, which is correct.

The substantive negative mutation was run in `research/T11/probes/rev332_negative.lean`, changing the output horizon from `S + δ` to `S + 2*δ`. Lean rejected it with:

```
Type mismatch: hrest a ha u p hs hb has type ∃ v : ClassicalSolutionT ν a f (S + d), ... but is expected to have type ∃ v : ClassicalSolutionT ν a f (S + 2 * δ), True
```

## commands and results

`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.RestartBeyond`: `Build completed successfully (10562 jobs)`.

`cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/RestartBeyond.lean`, the target probe, and `../research/T11/axioms_restart_beyond.lean`: all exit 0 and are silent; the axioms file checks exactly `[propext, Classical.choice, Quot.sound]` for all 12 declarations.

`make check`: exit 0; architecture, policy (13 tests), and work-queue checks pass. `../scripts/gates.sh NSFormalization.Section3.T11.RestartBeyond`: completes the build, checks, `make test`, and mutation suite; mutation suite reports `Mutation suite passed`. The direct negative probe exits nonzero with the reproducing horizon type mismatch above, as required. `check_contracts.py --base-ref origin/erenup/integration-section3` was included by the gate and reports the contract architecture checks.

ACCEPT-WITH-NOTES — fix: revise the report's “0 warnings” wording to “no warnings from this module; dependency warnings may print”.
