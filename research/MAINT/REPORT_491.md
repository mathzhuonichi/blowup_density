# Owner `main` full build verification (2026-09-20)

Purpose: verify the complete retained Lean source tree and the repository gates after the owner's streamlining commit and the lead process layer. No Lean source or Lake configuration was changed.

## Environment

| Item | Value |
|---|---|
| Checked source commit (`git rev-parse HEAD`, before this report-only commit) | `30107e2741bdc45b94b8bf8dd65e097eeeeae2a6` |
| `git rev-parse origin/main` | `3239486b2006340e547b4c633d2c502c3e607988` |
| Branch | `erenup/491-MAINT-main-build-check` |
| Worktree | `.claude/worktrees/491-MAINT-main-build-check` |
| Toolchain | Lean 4.34.0-rc2, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d` |
| Lake | `5.0.0-src+6a10ac8` |
| Mathlib revision | `85e3a25e006c35636f0e53b0e9296caca2685bc0` |
| Threads | `LEAN_NUM_THREADS=6` |
| Invocation rule | `. scripts/lean-env.sh`; every direct `lake` invocation ran from `verification/` |

The checked source commit is the lead process layer. Its parent chain contains owner commit `1a1b53b6`; the local remote-tracking `origin/main` had advanced to `3239486b` when the check ran.

## Module inventory

`find formalization/NSFormalization -name '*.lean' | wc -l` = **587**. Counts use the first directory component, except that Section 3 and Section 4 are split by their next component.

| Directory | `.lean` files |
|---|---:|
| `Paper1/` | 62 |
| `Paper3/` | 45 |
| `Section3/T10/` | 7 |
| `Section3/T11/` | 30 |
| `Section3/T12/` | 12 |
| `Section3/T13/` | 7 |
| `Section3/T14/` | 1 |
| `Section3/T15/` | 18 |
| `Section3/T16/` | 4 |
| `Section3/T17/` | 15 |
| `Section3/T18/` | 12 |
| `Section3/T19/` | 7 |
| `Section3/T20/` | 13 |
| `Section3/T21/` | 11 |
| `Section3/T22/` | 12 |
| `Section3/T23/` | 29 |
| `Section3/T24/` | 18 |
| **Section 3 subtotal** | **196** |
| `Section4/A01/` | 55 |
| `Section4/A02/` | 9 |
| `Section4/A03/` | 6 |
| `Section4/A04/` | 25 |
| `Section4/A05/` | 5 |
| `Section4/B01/` | 5 |
| `Section4/B02/` | 10 |
| `Section4/C01/` | 18 |
| `Section4/D01/` | 26 |
| `Section4/I01/` | 3 |
| `Section4/I02/` | 5 |
| `Section4/I03/` | 5 |
| `Section4/R41/` | 4 |
| `Section4/R42/` | 6 |
| `Section4/R43/` | 11 |
| `Section4/R44/` | 7 |
| **Section 4 subtotal** | **200** |
| `Source/` | 84 |
| **Total** | **587** |

`formalization/lakefile.toml` declares `globs = ["NSFormalization.+"]`, contains no `FormalPatched` library, and lists these **44** HeliCorgi roots:

```text
Formal.EndpointSafeTwoSpaceDuhamel
Formal.EndpointSafeTwoSpacePicard
Formal.FlowMapChainRule
Formal.FlowMapContDiffOne
Formal.FlowMapFTC
Formal.FlowMapLocalContDiff
Formal.FlowMapNonextendibilityCriterion
Formal.FlowMapOperatorContinuity
Formal.NavierStokesTimeBridge
Formal.PDEBridgeAdapter
Formal.R3ClosedSolenoidalCarrier
Formal.R3ConjugationReflection
Formal.R3CoordinateLinearAux
Formal.R3DivergencePointwise
Formal.R3FourierConjugationBridge
Formal.R3H2AdditiveConvolutionWeight
Formal.R3H2BesselWeightGeometry
Formal.R3H2CoordinateFourierBounds
Formal.R3H2FourierL1Bound
Formal.R3H2VelocityFourierL1Bound
Formal.R3H2WeightedConvolutionKernel
Formal.R3H2YoungWeightedBridge
Formal.R3L2CoordinateAux
Formal.R3L2ScalarAux
Formal.R3LerayComplexDivergenceBridge
Formal.R3LerayComplexFiberSymbol
Formal.R3LerayFourierBridge
Formal.R3LerayFrequencySymbol
Formal.R3LerayL2Operator
Formal.R3LerayPointwiseL2
Formal.R3NormalizedDivergenceFrequency
Formal.R3NormalizedDivergenceTerm
Formal.R3NormalizedFrequencyLpTop
Formal.R3SchwartzConvection
Formal.R3SchwartzConvectionSobolevReduction
Formal.R3SchwartzSobolevCore
Formal.R3SchwartzSobolevMonotonicity
Formal.R3SobolevCarrier
Formal.R3SolenoidalCarrierCompleteness
Formal.R3SolenoidalSobolevCarrier
Formal.R3StokesFrequencySymbol
Formal.R3StokesL2Operator
Formal.R3YoungL1L2Bochner
Formal.UniformRestartContinuation
```

## Full `NSFormalization` rebuild

Only these two artifact subtrees were deleted:

```text
formalization/.lake/build/lib/lean/NSFormalization/
formalization/.lake/build/ir/NSFormalization/
```

They contained 2,975 and 1,785 files, respectively. The 587 module names were generated from the sorted `find` result and passed to one `lake build` invocation. Combined output is `tmp/main_build.log`.

| Item | Result |
|---|---:|
| Exit code | **0** |
| Wall time | **787.67 s** |
| `grep -c 'error' tmp/main_build.log` | **0** |
| `NSFormalization` Built | **587 / 587** |
| `NSFormalization` Replayed | **0** |
| All Built lines | **589**: 587 `NSFormalization`, 2 `Bindings` dependencies |
| All Replayed lines | **12**: HeliCorgi modules |
| Lines beginning `warning:` | **81**: 54 `NSFormalization`, 27 HeliCorgi |
| `grep -c 'warning:' tmp/main_build.log` | **107**; 26 additional matches are warning-hint continuation lines |
| `.olean` files under the cleaned `NSFormalization` subtree | **587** |
| Final Lake line | `Build completed successfully (10867 jobs).` |

There is no warning from `NSFormalization/Section3/`; the former T22 `boundedDomainNorm` warning is absent. These are all **54** warning start lines from `NSFormalization/`:

```text
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Paper1/PeriodicSobolevHilbert.lean:60:51: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/LocalizationBoundary.lean:355:36: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Paper1/LocalizationBoundary.lean:361:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: NSFormalization/Paper1/PeriodicH2Embedding.lean:148:2: Try this:
warning: NSFormalization/Paper1/PeriodicH2Embedding.lean:263:23: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicH2Embedding.lean:268:9: Variable name `k` is not explicitly referenced.
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
warning: NSFormalization/Paper1/PeriodicMeanZeroEstimate.lean:65:2: `push_neg` has been deprecated. Prefer using `push Not` instead.
warning: NSFormalization/Paper1/PeriodicFiniteL3.lean:29:8: `continuous_finset_sum` has been deprecated: Use `continuous_finsetSum` instead
warning: NSFormalization/Paper1/PeriodicWeightShift.lean:23:10: Unused tactic linter: `ring` does nothing
warning: NSFormalization/Paper1/PeriodicWeightShift.lean:23:10: this tactic is never executed
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
warning: NSFormalization/Paper1/PeriodicPacketEndpointRates.lean:45:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicPacketEndpointRates.lean:72:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicForceConvergence.lean:53:13: This simp argument is unused:
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:43:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:44:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:69:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:70:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Source/BoundedViscosityUniqueness.lean:21:28: This simp argument is unused:
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead
warning: NSFormalization/Paper1/PeriodicScalarForceEndpoints.lean:156:5: `continuous_finset_sum` has been deprecated: Use `continuous_finsetSum` instead
warning: NSFormalization/Paper1/PeriodicInsertionSupport.lean:129:13: Variable name `hr` is not explicitly referenced.
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused:
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead
warning: NSFormalization/Paper1/PeriodicDensityFiber.lean:85:5: Variable name `hT` is not explicitly referenced.
warning: NSFormalization/Paper1/PeriodicDensityFiber.lean:118:5: Variable name `hT` is not explicitly referenced.
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:30: Variable name `hB` is not explicitly referenced.
warning: NSFormalization/Source/RieszPotentialNearField.lean:49:4: try 'simp' instead of 'simpa'
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:100:23: Variable name `U` is not explicitly referenced.
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:325:24: Variable name `V` is not explicitly referenced.
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:335:24: Variable name `V` is not explicitly referenced.
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:400:26: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:587:13: Variable name `hS` is not explicitly referenced.
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Source/RieszL2Fourier.lean:31:2: Try this:
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.
warning: NSFormalization/Source/FractionalRealization.lean:60:2: Try this:
warning: NSFormalization/Source/FractionalRealization.lean:83:2: Try this:
warning: NSFormalization/Source/FractionalRealization.lean:104:2: Try this:
warning: NSFormalization/Section4/A01/AprioriFamily.lean:148:31: Variable name `ha` is not explicitly referenced.
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.
```

The command sequence was:

```sh
. scripts/lean-env.sh
find formalization/NSFormalization -type f -name '*.lean' | sort > tmp/main_modules_paths.txt
sed -e 's#^formalization/##' -e 's#\.lean$##' -e 's#/#.#g' tmp/main_modules_paths.txt > tmp/main_modules.txt
find formalization/.lake/build/lib/lean/NSFormalization -depth -delete
find formalization/.lake/build/ir/NSFormalization -depth -delete
cd verification
/usr/bin/time -f 'WALL_SECONDS=%e' -o ../tmp/main_build_time.txt \
  env LEAN_NUM_THREADS=6 lake build $(cat ../tmp/main_modules.txt) \
  > ../tmp/main_build.log 2>&1
```

## `Bindings.*` and `Tests.*` build

The second invocation received every module found under `verification/Bindings/` and `verification/Tests/`: **59 Bindings + 29 Tests = 88 targets**. Its combined output is `tmp/verification_build.log`.

| Item | Result |
|---|---:|
| Exit code | **0** |
| Wall time | **204.66 s** |
| `grep -c 'error' tmp/verification_build.log` | **0** |
| Requested target Built lines | **85**: 56 Bindings + 29 Tests |
| Requested target Replayed lines | **0** |
| Requested targets already current, with no status line | **3**: `Bindings.Packet`, `Bindings.PacketImport`, `Bindings.Thresholds` |
| All Built lines | **130** |
| All Replayed lines | **43** |
| Lines beginning `warning:` | **84**: 54 `NSFormalization`, 27 HeliCorgi, 3 Bindings, 0 Tests |
| `grep -c 'warning:' tmp/verification_build.log` | **110**; 26 additional matches are warning-hint continuation lines |
| Current source modules with matching `.olean` | **88 / 88**: 59 Bindings + 29 Tests |
| Raw `.olean` subtree counts | 72 Bindings + 53 Tests, including prior cached artifacts |
| Final Lake line | `Build completed successfully (11000 jobs).` |

The three target-local warning lines are:

```text
warning: Bindings/BoundedDomainNorm.lean:54:0: Definition `toCanonical` is a proposition; use `theorem` instead of `def`
warning: Bindings/BoundedDomainNorm.lean:59:0: Definition `ofCanonical` is a proposition; use `theorem` instead of `def`
warning: Bindings/BoundedDomainNorm.lean:80:0: Definition `boundedDomainNorm` is a proposition; use `theorem` instead of `def`
```

The command was:

```sh
find verification/Bindings verification/Tests -type f -name '*.lean' | sort > tmp/verification_modules_paths.txt
sed -e 's#^verification/##' -e 's#\.lean$##' -e 's#/#.#g' tmp/verification_modules_paths.txt > tmp/verification_modules.txt
cd verification
/usr/bin/time -f 'WALL_SECONDS=%e' -o ../tmp/verification_build_time.txt \
  env LEAN_NUM_THREADS=6 lake build $(cat ../tmp/verification_modules.txt) \
  > ../tmp/verification_build.log 2>&1
```

## Repository gates

| Command | Exit | Wall time | Recorded result |
|---|---:|---:|---|
| `make check` | 0 | 16.09 s | 41 proof nodes; 27 article/guide mappings; 2,238 source modules; 29 registered contracts; 11 policy tests passed |
| `make test` | 0 | 4.08 s | 29 `Tests.*` modules replayed; **41** lines contain `standard logical axioms only` |
| `make test-mutations` | 0 | 19.35 s | implementation refactor accepted; admitted proof, extra axiom, and weakened hypothesis rejected as required |
| `python3 experiments/check_contracts.py --summary` | 0 | 3.94 s | `registered_contracts: 29` |
| `python3 experiments/check_formalization_plan.py --check` | 0 | 7.76 s | 41 proof nodes; 27 mappings; 2,238 source modules; imports and package paths resolve |
| `python3 experiments/audit_article_axioms.py --build --output-dir tmp/article-audit --workers 2` | 0 | 38.05 s | 56 declarations; 27 article entries; 0 forbidden-axiom results |

The mutation suite's result lines are:

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

The generated axiom report allows exactly `Classical.choice`, `Quot.sound`, and `propext`. It reports 2,249 source files, source-tree hash `f820dd950a76efbfc73300b56e0a4b85f02e7a89c8941cbfe448e400a3ababaf`, an empty `source_tokens` list, and no `unexpected_axioms`. `tmp/article-audit/report.json` is byte-for-byte identical to `formalization/blueprint/AXIOM_AUDIT.json`.

## Paper build

`make paper` exited **0** in **1.69 s**. It ran `latexmk`/`pdflatex` for both reader PDFs and then `check_reader_documents.py`. The exact reader-check summary is:

```text
Source inventory: 18 works; missing full text: none. Chapter-only coverage is explicitly marked.
26 numbered article statements and their guide mappings checked.
27 article results mapped, including the numbered remark; proof declaration kinds and source line numbers verified.
86 article labels resolved.
16 bibliography entries resolved; 29 registry declarations found; guide code paths verified.
Both PDF build logs are clean. Scope: structural checks, not a new proof certification.
```

The two regenerated tracked PDFs were restored to their checked-in versions after this result was recorded; they are not part of the report commit.

## Conclusion

Both build invocations and all seven requested gate/paper commands exited 0. The cleaned full build produced 587/587 `NSFormalization` `.olean` files with 0 error matches, and the 88 current Bindings/Tests source modules all have matching `.olean` files. The mutation suite passed, the article audit found 0 forbidden axioms and reproduced the checked-in JSON byte-for-byte, and the final reader-document check reported both PDF logs clean. The output was not warning-free: the full build printed 54 `NSFormalization` and 27 HeliCorgi warning start lines, while the verification build repeated those and printed three Bindings warnings. The former Section3/T22 warning was absent. `make test` printed 41 `standard logical axioms only` lines rather than the requested expected count of 29; it nevertheless exited 0 and the registry count is 29.

Items not green:

- The full rebuild has 81 warning start lines: the 54 exact `NSFormalization/` lines are reproduced above, plus 27 HeliCorgi warning start lines.
- The Bindings/Tests build has the three exact `Bindings/BoundedDomainNorm.lean` warning lines reproduced above; it also replays the same 54 local and 27 HeliCorgi warning lines.
- The requested expectation for `make test` was 29 lines, while `grep -c 'standard logical axioms only' tmp/make_test.log` returned **41**. The command exit code is 0 and `check_contracts.py --summary` reports 29 registered contracts.

There were no command failures, error matches in either build log, forbidden-axiom results, missing reader sources, or dirty tracked files outside these reports.

## Four-part record

**What was checked:** A clean one-invocation rebuild of all 587 retained `NSFormalization` modules; one build of all 59 `Bindings.*` and 29 `Tests.*` source modules; `make check`, `make test`, `make test-mutations`, the standalone contract and plan checks, the two-worker article axiom audit, and `make paper` with its reader-document check.

**What is in the tree:** 587 `NSFormalization` sources: Paper1 62, Paper3 45, Section3 196, Section4 200, Source 84; 44 configured HeliCorgi roots; 59 Bindings sources; 29 Tests sources; 29 registered contracts. The cleaned formalization artifact subtree contains 587 `.olean` files, and all 88 current Bindings/Tests sources have matching `.olean` files.

**What is not green, with exact text:** The 54 local warning lines and three Bindings warning lines are quoted verbatim above; the build also emitted 27 HeliCorgi warning start lines. The count mismatch is exactly `grep -c 'standard logical axioms only' tmp/make_test.log` = `41`, versus the requested expectation `29`. No gate has a nonzero exit status.

**Commands and results:** Full build rc 0, 787.67 s, 587 NS Built, 0 NS Replayed, 0 error matches; Bindings/Tests build rc 0, 204.66 s, all 88 target artifacts present, 0 error matches. `make check`/`make test`/`make test-mutations`/contract summary/plan check/article audit/`make paper` all returned 0 in 16.09/4.08/19.35/3.94/7.76/38.05/1.69 s. `make test` printed 41 standard-axiom lines; the audit checked 56 declarations with 0 forbidden results and matched the checked-in audit byte-for-byte; the reader check reported both PDF logs clean.
