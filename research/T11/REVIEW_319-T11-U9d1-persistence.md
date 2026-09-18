ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker explicitly does not claim an unconditional U9d1 analytic closure: the report says the common-horizon result is conditional on one input (`research/T11/REPORT_319.md:5-6`). The claimed physical theorem is the conditional `torusForcedMildOn_persistence`; its report transcription (`research/T11/REPORT_319.md:9-21`) matches the declaration in `formalization/NSFormalization/Section3/T11/Persistence.lean:221-244` exactly, including `hν`, `hT`, all datum/force hypotheses, the `Ico 0 T` domain, canonical `IsPeriodicReweight`, `ContinuousOn`, and compact-subset bounds.

The one peeled input is a real `def`, not an axiom: `TorusHalfStepInput` is stated at `formalization/NSFormalization/Section3/T11/Persistence.lean:165-186`. It quantifies one half-order step from an already continuous order-`r` realization to order `r+1/2`, retaining the same `T` and `Ico 0 T`; the report reproduces the same input (`research/T11/ATTEMPTS_PERSISTENCE.md:46-73`). This is an honest single residual under the brief's peeling rule, not a restatement of the all-order conclusion.

The literal brief target is also present as `persistence_literal_target` (`formalization/NSFormalization/Section3/T11/Persistence.lean:76-88`) and is discharged with the full-premise probe (`research/T11/probes/persistence_closes.lean:34-48`). The worker correctly flags that this is not physical persistence: `PeriodicSobolev` is a phantom-indexed carrier (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:94-99`), while physical order transport is the weighted `IsPeriodicReweight` relation (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:209-214`). This diagnosis is consistent with the paper's weighted torus norm (`paper/sections/01-introduction.tex:80-103`), and is stated plainly in the report (`research/T11/REPORT_319.md:64-70`).

## 2. What is in Lean

The unconditional algebraic layer is substantive and matches its comments: reflexivity and transitivity of reweights are proved at `formalization/NSFormalization/Section3/T11/Persistence.lean:31-45`; the bounded descending multiplier and its reweight identity are at `:47-68`; datum/reweight transport is at `:90-111`; and compact-subset boundedness from `ContinuousOn` is at `:70-74`. The order-3 mild predicate really contains nonnegative horizon, continuity on `Icc`, both integrability clauses, and the Duhamel equation (`formalization/NSFormalization/Section3/T11/LocalExistenceProbe.lean:244-258`), so the descent proof does not silently use an empty interval or a junk integral.

The ladder starts at `n=0`, applies exactly the one supplied half-step input at each successor, and composes reweights (`formalization/NSFormalization/Section3/T11/Persistence.lean:188-216`). The final theorem takes rung `2*m` and applies the genuine bounded descent to order `m` (`formalization/NSFormalization/Section3/T11/Persistence.lean:234-243`), so it is not merely identifying phantom carriers. The constant-mode witness is proved directly, including the heat identity, zero convection, integrability, and Duhamel equation (`formalization/NSFormalization/Section3/T11/Persistence.lean:118-163`). The non-vacuity example uses an inhabited positive-viscosity contract, `c = e₁`, a nonzero datum, the nonstationary mild solution, and independently supplied half-step realizations (`research/T11/probes/persistence_closes.lean:50-70`).

The 17 declarations in the module are all covered by guarded axiom checks (`research/T11/axioms_persistence.lean:5-71`), and the guards passed. The base comparison is clean: `git diff --name-only origin/erenup/integration-section3...HEAD` lists only the new persistence module and lane research records; no existing module or contract is modified.

## 3. Gaps

The residual is real and remains unresolved, exactly as reported (`research/T11/REPORT_319.md:54-62`): the existing torus smoothing theorem only supplies the order-one gain (`formalization/NSFormalization/Section3/T11/LocalExistenceProbe.lean:123-140`), and the existing convolution theorem is specifically an order-3-to-order-2 estimate (`formalization/NSFormalization/Section3/T11/ConvolutionBound.lean:272-293`, `:347-360`), not the real-order/fractional estimate required by `TorusHalfStepInput`. The paper does state common-interval all-order smoothness (`paper/sections/02-preliminaries.tex:105-120`, `paper/sections/appendix-a-local-theory.tex:60-76`), but the lane has not formalized that analytic implication. The paper's mild formula is the intended route (`paper/sections/appendix-a-local-theory.tex:109-116`), and the worker is correct not to claim it has been proved here.

I searched the whole `formalization/NSFormalization/Section4` tree for the missing half-step/torus persistence declarations. The closest all-order results are whole-space/R3 interfaces (`formalization/NSFormalization/Section4/A01/GronwallInstance.lean:109-123` and `formalization/NSFormalization/Section4/A01/DatumPathSmooth.lean:710-734`); neither has the torus `TorusForcedMildOn`/`IsPeriodicReweight` statement. The worker's checkout-absence claims for `PhysicalRecovery.lean`, `ForcePaths.lean`, and `REPORT_318.md` are accurate (`research/T11/REPORT_319.md:72-73`; the three paths are absent in this checkout).

The required substantive negative check succeeds. In the added reviewer probe, the main transitivity target is widened from `q` to `q+1` (`research/T11/probes/rev319_negative.lean:9-16`); Lean breaks at line 16 with:

```
error: Application type mismatch: The argument
  hBD
has type
  IsPeriodicReweight r q B D
but is expected to have type
  IsPeriodicReweight r (q + 1) B D
```

This changes the mathematical order and is not an argument-dropping test. The supplied non-vacuity witness is substantive as noted above.

One hygiene discrepancy is reproducible. The worker report says `git diff --check` passed (`research/T11/REPORT_319.md:91-94`), but rerunning it gives the exact failure:

```
research/T11/axioms_persistence.lean:72: new blank line at EOF.
```

This is the sole review note; it does not affect Lean elaboration or the axiom guards.

## 4. Commands and results

All Lean commands were run after sourcing `. scripts/lean-env.sh`, from `verification/`, with `LEAN_NUM_THREADS=6`; Lake was run only there.

| Command | Exact result |
|---|---|
| `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Persistence` | exit 0; `Build completed successfully (9973 jobs).` Dependency replay emits pre-existing warnings; no warning originates in `Persistence.lean`. |
| `lake env lean ../formalization/NSFormalization/Section3/T11/Persistence.lean` | exit 0, stdout empty |
| `lake env lean ../research/T11/probes/persistence_closes.lean` | exit 0, stdout empty |
| `lake env lean ../research/T11/axioms_persistence.lean` | exit 0, stdout empty; all 17 `#guard_msgs` checks passed |
| `make check` | exit 0; `test_contract_policy.py` reports `.............` then `OK`; `check_work_queue.py` reports `45 work items: ownership, contract registration and task cards consistent.` Its architecture scan also reports the pre-existing copied-umbrella `BoundaryCorollary.lean:90` `sorry` and `Explicit axiom/admission tokens, all copied sources: 11`; neither is in this lane's changed files. |
| `LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T11.Persistence` | exit 0; mutation tail is `extra_axiom: rejected as required`, `weakened_hypothesis: rejected as required`, `Mutation suite passed. This is an infrastructure check, not a PDE proof.`; final line `== gates OK` |
| negative probe `lake env lean ../research/T11/probes/rev319_negative.lean` | expected exit 1 with the type-mismatch shown in §3 |
| `git diff --check origin/erenup/integration-section3...HEAD` | exit 2 with `research/T11/axioms_persistence.lean:72: new blank line at EOF.` |

`verification/` is untouched in the lane diff, so the conditional section3-base contract command was not required; `scripts/gates.sh` nevertheless ran its default `check_contracts.py --base-ref origin/erenup/integration` and ended with `== gates OK`.

No prohibited token occurs in the new proof module or conformance probe, and no `maxHeartbeats` override is present (`formalization/NSFormalization/Section3/T11/Persistence.lean:1-245`). The report's conditional scope, the single named residual, and the physical-vs-phantom distinction are accurate.

Fix: remove the final blank line at `research/T11/axioms_persistence.lean:72`, then rerun `git diff --check`.
