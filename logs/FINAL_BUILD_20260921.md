# Final Phase 5 `erenup/core` build verification (2026-09-21)

Purpose: clean-build every retained `NSFormalization` module after all six Phase 5 Partial entries were closed, build every current Bindings/Tests module, run the owner gates, and check the delivery diff before a single PR to `main`. No Lean source or Lake configuration was changed.

## 1. Environment

| Item | Value |
|---|---|
| Checked Lean source commit | `b1f09c92ee92d46cd5f08b491afc0383ad1b5c1f` |
| Final checked pre-report `git rev-parse HEAD` | `97eb422ce892b2eeaa11037a5406b56835af8d3d` |
| `git rev-parse origin/main` | `3239486b2006340e547b4c633d2c502c3e607988` |
| Branch | `erenup/512-MAINT-final-build-check` |
| Worktree | `.claude/worktrees/512-MAINT-final-build-check` |
| Toolchain | Lean 4.34.0-rc2, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d` |
| Lake | `5.0.0-src+6a10ac8` |
| Mathlib revision | `85e3a25e006c35636f0e53b0e9296caca2685bc0` |
| Threads | `LEAN_NUM_THREADS=6` |
| Invocation rule | `. scripts/lean-env.sh`; direct `lake` invocations ran from `verification/` |

The full Lean rebuild was performed at `b1f09c92`. The only intervening tracked change was the separately committed regenerated audit hash, commit `97eb422c` (`[512-MAINT] Regenerate article axiom audit`); all final owner gates ran at that commit. During the run, `origin/erenup/core` advanced independently to sibling commit `76a8edb2`, so this branch ended one commit ahead and one behind that process-layer branch. Per the lane rules, no merge or rebase was performed.

## 2. Module inventory

`find formalization/NSFormalization -name '*.lean' | wc -l` = **609**.

| Directory | `.lean` files |
|---|---:|
| `Paper1/` | 62 |
| `Paper3/` | 45 |
| `Section3/T10/` | 7 |
| `Section3/T11/` | 34 |
| `Section3/T12/` | 12 |
| `Section3/T13/` | 7 |
| `Section3/T14/` | 1 |
| `Section3/T15/` | 19 |
| `Section3/T16/` | 4 |
| `Section3/T17/` | 16 |
| `Section3/T18/` | 13 |
| `Section3/T19/` | 10 |
| `Section3/T20/` | 13 |
| `Section3/T21/` | 11 |
| `Section3/T22/` | 12 |
| `Section3/T23/` | 29 |
| `Section3/T24/` | 24 |
| **Section 3 subtotal** | **212** |
| `Section4/A01/` | 55 |
| `Section4/A02/` | 9 |
| `Section4/A03/` | 6 |
| `Section4/A04/` | 31 |
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
| **Section 4 subtotal** | **206** |
| `Source/` | 84 |
| **Total** | **609** |

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

The exact output of `git diff --name-only origin/main..HEAD -- formalization verification | grep '\.lean$'` contains these **43 Phase 5 Lean modules**:

```text
formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean
formalization/NSFormalization/Section3/T11/H1Bridges.lean
formalization/NSFormalization/Section3/T11/H1Restart.lean
formalization/NSFormalization/Section3/T11/H1RestartBeyond.lean
formalization/NSFormalization/Section3/T15/PlacementAt.lean
formalization/NSFormalization/Section3/T17/ArticleScope.lean
formalization/NSFormalization/Section3/T18/ForceAmplitude.lean
formalization/NSFormalization/Section3/T19/ForceAmplitude.lean
formalization/NSFormalization/Section3/T19/FromData.lean
formalization/NSFormalization/Section3/T19/ThreadingAt.lean
formalization/NSFormalization/Section3/T24/ConservativeOmega.lean
formalization/NSFormalization/Section3/T24/MultipleOmega.lean
formalization/NSFormalization/Section3/T24/MultipleOmegaAssembled.lean
formalization/NSFormalization/Section3/T24/MultipleOmegaAssembly.lean
formalization/NSFormalization/Section3/T24/MultipleOmegaComponents.lean
formalization/NSFormalization/Section3/T24/MultipleOmegaRegions.lean
formalization/NSFormalization/Section4/A04/EnstrophyBarrier.lean
formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean
formalization/NSFormalization/Section4/A04/H1Bridges.lean
formalization/NSFormalization/Section4/A04/H1BridgesSmooth.lean
formalization/NSFormalization/Section4/A04/H1Restart.lean
formalization/NSFormalization/Section4/A04/H1RestartBeyond.lean
verification/Bindings/ConservativeForcingV2.lean
verification/Bindings/ContinuationV3.lean
verification/Bindings/Correction3V2.lean
verification/Bindings/ForceAmplitude.lean
verification/Bindings/MultipleRegionsV2.lean
verification/Bindings/PeriodicInsertionV2.lean
verification/Bindings/TorusLocalTheoryV2.lean
verification/Contracts/V1/ForceAmplitude.lean
verification/Contracts/V2/ConservativeForcing.lean
verification/Contracts/V2/Correction3.lean
verification/Contracts/V2/MultipleRegions.lean
verification/Contracts/V2/PeriodicInsertion.lean
verification/Contracts/V2/TorusLocalTheory.lean
verification/Contracts/V3/Continuation.lean
verification/Tests/ConservativeForcingV2.lean
verification/Tests/ContinuationV3.lean
verification/Tests/Correction3V2.lean
verification/Tests/ForceAmplitude.lean
verification/Tests/MultipleRegionsV2.lean
verification/Tests/PeriodicInsertionV2.lean
verification/Tests/TorusLocalTheoryV2.lean
```

## 3. Full rebuilds

### `NSFormalization`

Only these two artifact subtrees were deleted:

```text
formalization/.lake/build/lib/lean/NSFormalization/
formalization/.lake/build/ir/NSFormalization/
```

They contained 3,122 and 1,888 entries including their root directories. The 609 sorted module names were passed to one `lake build` invocation. Combined output is `tmp/final_build.log`.

| Item | Result |
|---|---:|
| Exit code | **0** |
| Wall time | **443.14 s** |
| `grep -c 'error' tmp/final_build.log` | **0** |
| Requested `NSFormalization` Built | **609 / 609** |
| Requested `NSFormalization` Replayed | **0** |
| All Built lines | **611**: 609 `NSFormalization`, 2 `Bindings` dependencies |
| All Replayed lines | **12**: HeliCorgi modules |
| Lines beginning `warning:` | **87**: 60 `NSFormalization`, 27 HeliCorgi |
| `grep -c 'warning:' tmp/final_build.log` | **113**; 26 additional matches are warning-hint continuation lines |
| `.olean` files under the cleaned subtree | **609** |
| Final Lake line | `Build completed successfully (10889 jobs).` |

The Route B H1 bridge/restart modules under `Section3/T11/` and `Section4/A04/` are warning-free. The six Phase 5 warning starts under Section 3 are all in `Section3/T11/EnstrophyInequality.lean`; no warning starts come from a `Section4/A04/` module.

All **60** `NSFormalization` warning start lines are:

```text
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Paper1/PeriodicSobolevHilbert.lean:60:51: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
warning: NSFormalization/Paper1/LocalizationBoundary.lean:355:36: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Paper1/LocalizationBoundary.lean:361:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: NSFormalization/Paper1/PeriodicMeanZeroEstimate.lean:65:2: `push_neg` has been deprecated. Prefer using `push Not` instead.
warning: NSFormalization/Paper1/PeriodicH2Embedding.lean:148:2: Try this:
warning: NSFormalization/Paper1/PeriodicH2Embedding.lean:263:23: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicH2Embedding.lean:268:9: Variable name `k` is not explicitly referenced.
warning: NSFormalization/Paper1/PeriodicFiniteL3.lean:29:8: `continuous_finset_sum` has been deprecated: Use `continuous_finsetSum` instead
warning: NSFormalization/Paper1/PeriodicWeightShift.lean:23:10: Unused tactic linter: `ring` does nothing
warning: NSFormalization/Paper1/PeriodicWeightShift.lean:23:10: this tactic is never executed
warning: NSFormalization/Paper1/PeriodicPacketEndpointRates.lean:45:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicPacketEndpointRates.lean:72:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
warning: NSFormalization/Paper1/PeriodicForceConvergence.lean:53:13: This simp argument is unused:
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:43:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:44:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:69:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:70:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead
warning: NSFormalization/Paper1/PeriodicScalarForceEndpoints.lean:156:5: `continuous_finset_sum` has been deprecated: Use `continuous_finsetSum` instead
warning: NSFormalization/Paper1/PeriodicInsertionSupport.lean:129:13: Variable name `hr` is not explicitly referenced.
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused:
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Source/BoundedViscosityUniqueness.lean:21:28: This simp argument is unused:
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
warning: NSFormalization/Source/RieszL2Fourier.lean:31:2: Try this:
warning: NSFormalization/Source/FractionalRealization.lean:60:2: Try this:
warning: NSFormalization/Source/FractionalRealization.lean:83:2: Try this:
warning: NSFormalization/Source/FractionalRealization.lean:104:2: Try this:
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.
warning: NSFormalization/Section4/A01/AprioriFamily.lean:148:31: Variable name `ha` is not explicitly referenced.
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.
warning: NSFormalization/Section3/T11/EnstrophyInequality.lean:93:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Section3/T11/EnstrophyInequality.lean:125:20: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Section3/T11/EnstrophyInequality.lean:132:20: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Section3/T11/EnstrophyInequality.lean:466:66: This simp argument is unused:
warning: NSFormalization/Section3/T11/EnstrophyInequality.lean:502:13: This simp argument is unused:
warning: NSFormalization/Section3/T11/EnstrophyInequality.lean:543:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
```

The command sequence was:

```sh
. scripts/lean-env.sh
find formalization/NSFormalization -type f -name '*.lean' | sort > tmp/final_modules_paths.txt
sed -e 's#^formalization/##' -e 's#\.lean$##' -e 's#/#.#g' tmp/final_modules_paths.txt > tmp/final_modules.txt
find formalization/.lake/build/lib/lean/NSFormalization -depth -delete
find formalization/.lake/build/ir/NSFormalization -depth -delete
cd verification
/usr/bin/time -f 'WALL_SECONDS=%e' -o ../tmp/final_build_time.txt \
  env LEAN_NUM_THREADS=6 lake build $(<../tmp/final_modules.txt) \
  > ../tmp/final_build.log 2>&1
```

### Every `Bindings.*` and `Tests.*` module

The second invocation received every source module found under `verification/Bindings/` and `verification/Tests/`: **66 Bindings + 36 Tests = 102 targets**.

```text
Bindings.AffineVariation
Bindings.BochnerPartial
Bindings.BoundaryInsertion
Bindings.BoundaryInsertionV2
Bindings.BoundedDomainNorm
Bindings.CompactClassDensity
Bindings.CompactClassRider
Bindings.CompletedClosure
Bindings.CompletedDensity
Bindings.CompletedSobolevDensity
Bindings.ConservativeForcing
Bindings.ConservativeForcingV2
Bindings.ContinuationV2
Bindings.ContinuationV3
Bindings.Correction
Bindings.Correction3
Bindings.Correction3V2
Bindings.CorrectionV2
Bindings.CriticalFiniteHorizon
Bindings.CriticalRegularity
Bindings.CriticalRegularityT
Bindings.DatumLemmas
Bindings.Density
Bindings.DensityFromInsertion
Bindings.FluxCancellation
Bindings.ForceAmplitude
Bindings.ForceCellIntegral
Bindings.ForceClasses
Bindings.GridAssembly
Bindings.GridAssemblyNorms
Bindings.GridLemmas
Bindings.GridObservations
Bindings.HomogeneousNorm
Bindings.HomogeneousPartial
Bindings.HomogeneousPartialV2
Bindings.InsertionFamily
Bindings.InsertionFromData
Bindings.InsertionLifespan
Bindings.InsertionLifespanV2
Bindings.LocalPotential
Bindings.LocalTheoryV2
Bindings.Localization
Bindings.MainThresholds
Bindings.MaximalPartial
Bindings.MaximalPartialV2
Bindings.MeanZeroCalculus
Bindings.MultipleRegions
Bindings.MultipleRegionsV2
Bindings.Packet
Bindings.PacketImport
Bindings.PeriodicInsertion
Bindings.PeriodicInsertionV2
Bindings.RapidClassDensity
Bindings.Scaling
Bindings.Scaling3
Bindings.ScalingEnergy
Bindings.ScalingHomogeneous
Bindings.ScalingHomogeneousClosed
Bindings.ScalingNorms
Bindings.Thresholds
Bindings.TorusData
Bindings.TorusLocalTheory
Bindings.TorusLocalTheoryV2
Bindings.TorusMain
Bindings.TorusNonDensity
Bindings.Uniqueness
Tests.AffineVariation
Tests.BoundaryInsertionV2
Tests.BoundedDomainNorm
Tests.CompletedDensity
Tests.ConservativeForcing
Tests.ConservativeForcingV2
Tests.ContinuationV2
Tests.ContinuationV3
Tests.Correction3
Tests.Correction3V2
Tests.CriticalFiniteHorizon
Tests.CriticalRegularity
Tests.CriticalRegularityT
Tests.Density
Tests.ForceAmplitude
Tests.ForceClasses
Tests.GridObservations
Tests.InsertionFamily
Tests.InsertionLifespanV2
Tests.LocalPotential
Tests.LocalTheoryV2
Tests.Localization
Tests.MainThresholds
Tests.MaximalPartialV2
Tests.MultipleRegions
Tests.MultipleRegionsV2
Tests.Packet
Tests.PacketImport
Tests.PeriodicInsertion
Tests.PeriodicInsertionV2
Tests.Scaling3
Tests.TorusLocalTheory
Tests.TorusLocalTheoryV2
Tests.TorusMain
Tests.TorusNonDensity
Tests.Uniqueness
```

Combined output is `tmp/final_verification_build.log`.

| Item | Result |
|---|---:|
| Exit code | **0** |
| Wall time | **95.20 s** |
| `grep -c 'error' tmp/final_verification_build.log` | **0** |
| Requested Built | **99**: 63 Bindings + 36 Tests |
| Requested Replayed | **0** |
| Requested targets already current, with no status line | **3**: `Bindings.Packet`, `Bindings.PacketImport`, `Bindings.Thresholds` |
| All Built lines | **151** |
| All Replayed lines | **44** |
| Lines beginning `warning:` | **90**: 60 `NSFormalization`, 27 HeliCorgi, 3 Bindings, 0 Tests |
| `grep -c 'warning:' tmp/final_verification_build.log` | **116**; 26 additional matches are warning-hint continuation lines |
| Current source modules with matching `.olean` | **102 / 102** |
| Raw `.olean` subtree counts | 79 Bindings + 60 Tests, including prior cached artifacts |
| Final Lake line | `Build completed successfully (11043 jobs).` |

The three target-local warning lines are:

```text
warning: Bindings/BoundedDomainNorm.lean:54:0: Definition `toCanonical` is a proposition; use `theorem` instead of `def`
warning: Bindings/BoundedDomainNorm.lean:59:0: Definition `ofCanonical` is a proposition; use `theorem` instead of `def`
warning: Bindings/BoundedDomainNorm.lean:80:0: Definition `boundedDomainNorm` is a proposition; use `theorem` instead of `def`
```

The command was:

```sh
find verification/Bindings verification/Tests -type f -name '*.lean' | sort > tmp/final_verification_modules_paths.txt
sed -e 's#^verification/##' -e 's#\.lean$##' -e 's#/#.#g' tmp/final_verification_modules_paths.txt > tmp/final_verification_modules.txt
cd verification
/usr/bin/time -f 'WALL_SECONDS=%e' -o ../tmp/final_verification_build_time.txt \
  env LEAN_NUM_THREADS=6 lake build $(<../tmp/final_verification_modules.txt) \
  > ../tmp/final_verification_build.log 2>&1
```

## 4. Owner gates

| Command | Exit | Wall time | Key result |
|---|---:|---:|---|
| Initial `make check` | 2 | 7.70 s | Expected stale audit: `AssertionError: Source changed: rerun the article axiom audit` |
| Final `make check` | 0 | 11.80 s | 41 proof nodes; 27 article/guide mappings; 2,281 source modules; 36 contracts; 11 policy tests passed |
| `make test` | 0 | 2.09 s | 36 `Tests.*` modules replayed; 56 checked declarations printed `standard logical axioms only` |
| `make test-mutations` | 0 | 13.11 s | Refactor accepted; admitted proof, extra axiom, and weakened hypothesis rejected |
| `make paper` | 0 | 1.59 s | Both PDFs built; document checker passed; both PDF logs clean |
| `python3 experiments/check_reader_documents.py` | 0 | 0.04 s | 18 sources, 26 numbered statements, 27 mapped results, 86 labels, 16 bibliography entries, 36 registry declarations |
| `python3 experiments/check_formalization_plan.py` | 0 | 7.77 s | 41 proof nodes; 27 mappings; 2,281 source modules; no change to `DEPENDENCY_GRAPH.md` |
| `python3 experiments/audit_article_axioms.py --build --output-dir tmp/article-audit --workers 2` (final rerun) | 0 | 38.52 s | 76 declarations; 27 article entries; 0 forbidden-axiom results; report matched `AXIOM_AUDIT.json` byte-for-byte |
| `git diff --check` | 0 | 0.00 s | No output |
| `python3 experiments/check_contracts.py --summary` | 0 | 3.84 s | `registered_contracts: 36` |

The mutation suite's exact result lines are:

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

The reader-check summary, identical inside `make paper` and in the standalone command, is:

```text
Source inventory: 18 works; missing full text: none. Chapter-only coverage is explicitly marked.
26 numbered article statements and their guide mappings checked.
27 article results mapped, including the numbered remark; proof declaration kinds and source line numbers verified.
86 article labels resolved.
16 bibliography entries resolved; 36 registry declarations found; guide code paths verified.
Both PDF build logs are clean. Scope: structural checks, not a new proof certification.
```

### Stale-artifact handling

The initial `make check` failed exactly as anticipated:

```text
assert digest == report['source_tree_sha256'], 'Source changed: rerun the article axiom audit'
AssertionError: Source changed: rerun the article axiom audit
make: *** [Makefile:4: check] Error 1
```

The first two-worker audit exited 0 in 38.53 s. Its generated report differed from the checked-in `formalization/blueprint/AXIOM_AUDIT.json` only in this source hash:

```text
old: 488abf2ed1d220363704ae12de665d9a80d95790fef5fdc4629dfde454677cf8
new: 4a5e46fee81e59f96eea669c598ae4b9d2f2ed677cba6b05931e725f2b09f9ae
```

It reports 2,292 source files, zero source admission/custom-axiom tokens, allowed axioms `Classical.choice`, `Quot.sound`, and `propext`, and zero unexpected axioms. The regenerated JSON was committed separately as `97eb422c` (`[512-MAINT] Regenerate article axiom audit`). The final rerun again exited 0 and left it byte-for-byte unchanged.

The requested expected count was 72 declarations, but both the pre-existing final-tree JSON and both regenerations contain **76** targets, and the script's exact summary is:

```text
76 declarations; 27 article entries; 0 forbidden-axiom results
```

No claim of 72 is therefore made. This is a requested-expectation mismatch, not a gate failure.

`check_formalization_plan.py` did not change `DEPENDENCY_GRAPH.md`; `CLOSURE_AUDIT.md` also remained unchanged. `make paper` changed both PDF byte hashes, but extracted text hashes, page counts, and file sizes matched the committed PDFs exactly. Only embedded `CreationDate` and `ModDate` moved from 01:56 to 03:00 EDT. Those metadata-only outputs were restored to their checked-in bytes and were not committed.

## 5. Contract closure

All 36 registry entries are enabled, and each registry declaration appears in the `make test` output for its registered test module. `make test` prints `standard logical axioms only`; `TestSupport.checkAxioms` permits the set `{propext, Classical.choice, Quot.sound}` and rejects every axiom outside it, but does not print which subset a declaration actually uses. Accordingly, “standard only” below means an actual axiom set contained in that permitted set.

| Contract | Test module | Registered checked declaration | `make test` axiom result |
|---|---|---|---|
| `I01.packet` | `Tests.Packet` | `BlowupDensity.Tests.checkedPacket` | standard only |
| `R42.insertion_family` | `Tests.InsertionFamily` | `BlowupDensity.Tests.checkedInsertionFamily` | standard only |
| `A02.uniqueness` | `Tests.Uniqueness` | `BlowupDensity.Tests.checkedUniqueness` | standard only |
| `A02.maximal_partial_v2` | `Tests.MaximalPartialV2` | `BlowupDensity.Tests.checkedMaximalPartialV2` | standard only |
| `R42.insertion_lifespan_v2` | `Tests.InsertionLifespanV2` | `BlowupDensity.Tests.checkedInsertionLifespanV2` | standard only |
| `R43.critical_regularity` | `Tests.CriticalRegularity` | `BlowupDensity.Tests.checkedCriticalRegularity` | standard only |
| `R44.critical_finite_horizon` | `Tests.CriticalFiniteHorizon` | `BlowupDensity.Tests.checkedCriticalFiniteHorizon` | standard only |
| `R41.main_thresholds` | `Tests.MainThresholds` | `BlowupDensity.Tests.checkedMainThresholds` | standard only |
| `R45.force_classes` | `Tests.ForceClasses` | `BlowupDensity.Tests.checkedForceClasses` | standard only |
| `A01.local_theory_v2` | `Tests.LocalTheoryV2` | `BlowupDensity.Tests.checkedLocalTheoryV2` | standard only |
| `A04.continuation_v2` | `Tests.ContinuationV2` | `BlowupDensity.Tests.checkedContinuationV2` | standard only |
| `A04.continuation_v3` **(Phase 5)** | `Tests.ContinuationV3` | `BlowupDensity.Tests.checkedContinuationV3` | standard only |
| `R47.grid_observations` | `Tests.GridObservations` | `BlowupDensity.Tests.checkedGridObservations` | standard only |
| `R46.completed_density` | `Tests.CompletedDensity` | `BlowupDensity.Tests.checkedCompletedDensity` | standard only |
| `T01.torus_local_theory` | `Tests.TorusLocalTheory` | `BlowupDensity.Tests.checkedTorusLocalTheory` | standard only |
| `T01.torus_local_theory_v2` **(Phase 5)** | `Tests.TorusLocalTheoryV2` | `BlowupDensity.Tests.checkedTorusLocalTheoryV2` | standard only |
| `T01.packet_import` | `Tests.PacketImport` | `BlowupDensity.Tests.checkedPacketImport` | standard only |
| `T02.local_potential` | `Tests.LocalPotential` | `BlowupDensity.Tests.checkedLocalPotential` | standard only |
| `T02.localization` | `Tests.Localization` | `BlowupDensity.Tests.checkedLocalization` | standard only |
| `T03.critical_regularity` | `Tests.CriticalRegularityT` | `BlowupDensity.Tests.checkedCriticalRegularityT` | standard only |
| `T04.bounded_domain_norm` | `Tests.BoundedDomainNorm` | `BlowupDensity.Tests.checkedBoundedDomainNorm` | standard only |
| `T04.affine_variation` | `Tests.AffineVariation` | `BlowupDensity.Tests.checkedAffineVariation` | standard only |
| `T04.conservative_forcing` | `Tests.ConservativeForcing` | `BlowupDensity.Tests.checkedConservativeForcing` | standard only |
| `T02.correction` | `Tests.Correction3` | `BlowupDensity.Tests.checkedCorrection3` | standard only |
| `T03.periodic_insertion` | `Tests.PeriodicInsertion` | `BlowupDensity.Tests.checkedPeriodicInsertion` | standard only |
| `T03.density` | `Tests.Density` | `BlowupDensity.Tests.checkedDensity` | standard only |
| `T03.non_density` | `Tests.TorusNonDensity` | `BlowupDensity.Tests.checkedTorusNonDensity` | standard only |
| `T03.main` | `Tests.TorusMain` | `BlowupDensity.Tests.checkedTorusMain` | standard only |
| `T02.scaling` | `Tests.Scaling3` | `BlowupDensity.Tests.checkedScaling3` | standard only |
| `T04.multiple_regions` | `Tests.MultipleRegions` | `BlowupDensity.Tests.checkedMultipleRegions` | standard only |
| `T23.boundary_insertion_v2` | `Tests.BoundaryInsertionV2` | `BlowupDensity.Tests.checkedBoundaryInsertionV2` | standard only |
| `T02.correction_v2` **(Phase 5)** | `Tests.Correction3V2` | `BlowupDensity.Tests.checkedCorrection3V2` | standard only |
| `T03.periodic_insertion_v2` **(Phase 5)** | `Tests.PeriodicInsertionV2` | `BlowupDensity.Tests.checkedPeriodicInsertionV2` | standard only |
| `T03.force_amplitude` **(Phase 5)** | `Tests.ForceAmplitude` | `BlowupDensity.Tests.checkedForceAmplitude` | standard only |
| `T04.conservative_forcing_v2` **(Phase 5)** | `Tests.ConservativeForcingV2` | `BlowupDensity.Tests.checkedConservativeForcingV2` | standard only |
| `T04.multiple_regions_v2` **(Phase 5)** | `Tests.MultipleRegionsV2` | `BlowupDensity.Tests.checkedMultipleRegionsV2` | standard only |

The seven Phase 5 additions are exactly `T02.correction_v2`, `T03.periodic_insertion_v2`, `T03.force_amplitude`, `T04.conservative_forcing_v2`, `T04.multiple_regions_v2`, `A04.continuation_v3`, and `T01.torus_local_theory_v2`.

## 6. Delivery-diff sanity

The exact output of `git diff --stat origin/main..HEAD -- formalization verification paper experiments README.md output Makefile .github` at the checked pre-report commit was:

```text
 README.md                                          |   6 +-
 experiments/check_reader_documents.py              |   6 +-
 experiments/test_contract_policy.py                |  23 +-
 .../Section3/T11/EnstrophyInequality.lean          | 745 +++++++++++++++++++++
 .../NSFormalization/Section3/T11/H1Bridges.lean    | 174 +++++
 .../NSFormalization/Section3/T11/H1Restart.lean    | 592 ++++++++++++++++
 .../Section3/T11/H1RestartBeyond.lean              |  75 +++
 .../NSFormalization/Section3/T15/PlacementAt.lean  |  65 ++
 .../NSFormalization/Section3/T17/ArticleScope.lean | 281 ++++++++
 .../Section3/T18/ForceAmplitude.lean               | 343 ++++++++++
 .../Section3/T19/ForceAmplitude.lean               |  23 +
 .../NSFormalization/Section3/T19/FromData.lean     |  86 +++
 .../NSFormalization/Section3/T19/ThreadingAt.lean  | 271 ++++++++
 .../Section3/T24/ConservativeOmega.lean            | 129 ++++
 .../Section3/T24/MultipleOmega.lean                | 203 ++++++
 .../Section3/T24/MultipleOmegaAssembled.lean       | 231 +++++++
 .../Section3/T24/MultipleOmegaAssembly.lean        |  99 +++
 .../Section3/T24/MultipleOmegaComponents.lean      | 158 +++++
 .../Section3/T24/MultipleOmegaRegions.lean         | 345 ++++++++++
 .../Section4/A04/EnstrophyBarrier.lean             | 195 ++++++
 .../Section4/A04/EnstrophyInequality.lean          | 493 ++++++++++++++
 .../NSFormalization/Section4/A04/H1Bridges.lean    | 257 +++++++
 .../Section4/A04/H1BridgesSmooth.lean              |  96 +++
 .../NSFormalization/Section4/A04/H1Restart.lean    | 292 ++++++++
 .../Section4/A04/H1RestartBeyond.lean              |  75 +++
 formalization/blueprint/AXIOM_AUDIT.json           | 336 +++++++++-
 formalization/blueprint/CLOSURE_AUDIT.md           |  35 +-
 formalization/blueprint/DEPENDENCY_GRAPH.md        |  61 +-
 formalization/blueprint/README.md                  |   2 +-
 formalization/blueprint/RESULT_MAP.md              |  12 +-
 formalization/blueprint/entrypoints.json           |  38 +-
 formalization/blueprint/proof_graph.json           |  91 +--
 output/pdf/blowup_density_revised.pdf              | Bin 487816 -> 492052 bytes
 output/pdf/formalization_guide.pdf                 | Bin 321067 -> 324391 bytes
 paper/formalization_guide.tex                      |  73 +-
 verification/Bindings/ConservativeForcingV2.lean   |  30 +
 verification/Bindings/ContinuationV3.lean          |  48 ++
 verification/Bindings/Correction3V2.lean           |  40 ++
 verification/Bindings/ForceAmplitude.lean          |  51 ++
 verification/Bindings/MultipleRegionsV2.lean       | 171 +++++
 verification/Bindings/PeriodicInsertionV2.lean     |  27 +
 verification/Bindings/TorusLocalTheoryV2.lean      |  51 ++
 verification/Contracts/V1/ForceAmplitude.lean      |  32 +
 verification/Contracts/V2/ConservativeForcing.lean |  37 +
 verification/Contracts/V2/Correction3.lean         |  27 +
 verification/Contracts/V2/MultipleRegions.lean     | 164 +++++
 verification/Contracts/V2/PeriodicInsertion.lean   |  56 ++
 verification/Contracts/V2/TorusLocalTheory.lean    |  58 ++
 verification/Contracts/V3/Continuation.lean        |  52 ++
 verification/README.md                             |   2 +-
 verification/Tests/ConservativeForcingV2.lean      |  23 +
 verification/Tests/ContinuationV3.lean             |  48 ++
 verification/Tests/Correction3V2.lean              |  14 +
 verification/Tests/ForceAmplitude.lean             |  14 +
 verification/Tests/MultipleRegionsV2.lean          |  16 +
 verification/Tests/PeriodicInsertionV2.lean        |  15 +
 verification/Tests/TorusLocalTheoryV2.lean         |  53 ++
 verification/contracts.json                        |  77 +++
 58 files changed, 6850 insertions(+), 167 deletions(-)
```

The command `git diff --name-only origin/main..HEAD | grep -vE '^(formalization|verification|paper|experiments|README.md|output|Makefile|.github)'` emitted **3,049 process-layer paths**. The following is an exhaustive prefix-compressed listing; a count of one is the literal path shown, while a directory count means that many emitted paths under that directory. Counts sum to 3,049.

```text
.claude/agents/ (1)
.claude/hooks/ (2)
.claude/settings.json
.claude/skills/ (2)
CLAUDE.md
NEXT_SESSION.md
PLAN.md
archive/section3/ (4)
archive/section4/ (124)
collaboration/DESIGN.md
collaboration/REPORT_268.md
collaboration/TASKS.md
collaboration/briefs/ (265)
collaboration/tasks/ (45)
collaboration/work_items.json
docs/proof_map/ (2)
logs/AGENT_RUNS.csv
logs/APPENDIX_REDUCTION_INDEPENDENT_REVIEW_20260912.md
logs/COLLABORATION_SETUP_20260913.md
logs/FORMALIZATION_PLAN_CHECK.json
logs/FORMALIZATION_REORGANIZATION_20260913.md
logs/FORMALIZATION_RESUME_20260915.md
logs/FORMALIZATION_SOURCE_MANIFEST.json
logs/LESSONS.md
logs/MAIN_BRANCH_20260913.md
logs/MAIN_BUILD_20260920.md
logs/MANUSCRIPT_CHECK.json
logs/MERGE_DEPENDENCIES_20260915.md
logs/PLAN_HISTORY_20260913.md
logs/POST_REVISION_SEMANTIC_REVIEW_20260912.md
logs/POST_REVISION_SOURCE_MANIFEST_20260912.json
logs/PROGRESS_20260913.md
logs/README.md
logs/REVISION_20260912.md
logs/SECTION3_BUILD_20260918.md
logs/SECTION3_BUILD_20260918b.md
logs/SECTION3_BUILD_20260918c.md
logs/SECTION3_BUILD_20260918d.md
logs/SECTION3_BUILD_20260918e.md
logs/SECTION3_BUILD_20260918f.md
logs/SECTION3_BUILD_20260919g.md
logs/SECTION3_BUILD_20260919h.md
logs/SECTION3_BUILD_20260919i.md
logs/SECTION3_OWNER_DECISIONS_20260919.md
logs/SECTION4_FULL_BUILD_20260917.md
logs/SECTION4_FULL_BUILD_20260917_ASTRA.md
logs/SOL_MAX_AUDIT_SOURCE_MANIFEST_20260912.json
logs/SOL_MAX_AUDIT_SYNTHESIS_20260912.md
logs/SOL_MAX_INDEPENDENT_AUDIT_1_20260912.md
logs/SOL_MAX_INDEPENDENT_AUDIT_2_20260912.md
logs/SOL_MAX_INDEPENDENT_AUDIT_3_20260912.md
logs/SOURCE_MANIFEST.json
logs/THEOREM_CORRESPONDENCE.md
logs/VALIDATION_163_20260915.md
logs/VALIDATION_164_20260915.md
logs/VALIDATION_165_20260915.md
logs/VALIDATION_166_20260915.md
logs/VALIDATION_167_20260915.md
logs/VALIDATION_168_20260915.md
logs/VALIDATION_169_20260915.md
research/A01/ (384)
research/A02/ (37)
research/A03/ (7)
research/A04/ (106)
research/A05/ (25)
research/B01/ (15)
research/B02/ (43)
research/C01/ (106)
research/D01/ (111)
research/I01/ (5)
research/I02/ (7)
research/I03/ (16)
research/MAINT/ (37)
research/P21/ (58)
research/R41/ (20)
research/R41D/ (32)
research/R42/ (34)
research/R43/ (66)
research/R44/ (45)
research/R45/ (32)
research/R46/ (28)
research/R47/ (36)
research/README.md
research/SPEC
research/T01/ (4)
research/T10/ (62)
research/T11/ (202)
research/T12/ (87)
research/T13/ (58)
research/T14/ (21)
research/T15/ (114)
research/T16/ (42)
research/T17/ (111)
research/T18/ (71)
research/T19/ (62)
research/T20/ (87)
research/T21/ (32)
research/T22/ (85)
research/T23/ (103)
research/T24/ (137)
research/U05/ (11)
research/section4/ (3)
scripts/codex_lane.sh
scripts/codex_review.sh
scripts/codex_status.sh
scripts/gates.sh
scripts/lean-env.sh
scripts/lean-install.sh
scripts/merge_json3.py
scripts/merge_lane.sh
```

This report itself is added only by the final report commit and is likewise process-layer material, not part of the stated delivery path set.

## 7. Verdict

The final Phase 5 tree is **build-ready but not unconditionally consistency-ready for the delivery PR**. The complete 609-module clean rebuild and 102-module Bindings/Tests build passed with zero error matches; all requested final-tree gates passed; the proof graph is 41/41 Closed; the guide has 27 Closed and 0 Partial entries; and all 36 registered contract declarations passed the transitive-axiom policy. There is no Lean failure or forbidden axiom.

Two owner-visible consistency items remain before calling the delivery PR fully ready:

- `verification/README.md` says “30 current typed acceptance interfaces,” but `verification/contracts.json`, `make check`, `make test`, the reader check, and `check_contracts.py --summary` all establish **36**. The root `README.md` and blueprint README correctly say 27 Closed / 0 Partial. This lane was forbidden to edit that documentation.
- The lane request expected an article-audit total of 72 declarations, while the checked-in final-tree target list and two clean regenerations contain **76**. Both audits passed with 27 article entries and zero forbidden results. The owner should either accept 76 as the intended expanded scope or identify the four targets that should not be audited.

The seven new registered interfaces are the V2 additions `T02.correction_v2`, `T03.periodic_insertion_v2`, `T04.conservative_forcing_v2`, `T04.multiple_regions_v2`, and `T01.torus_local_theory_v2`, the new `T03.force_amplitude` V1 interface, and `A04.continuation_v3`. The guide and blueprint delivery changes close all six former Partial article entries. The only regenerated tracked artifact in this lane is `AXIOM_AUDIT.json`, committed separately; `DEPENDENCY_GRAPH.md`, `CLOSURE_AUDIT.md`, and the committed PDF bytes were unchanged by this check.

Warnings do not block the gates: the clean formalization build emitted 60 local and 27 HeliCorgi warning start lines, and the verification build added the three quoted `Bindings/BoundedDomainNorm.lean` warnings. The Route B H1 modules were warning-free.

## Four-part record

**What was checked:** One clean invocation for all 609 retained `NSFormalization` modules; one invocation for all 66 Bindings and 36 Tests modules; `make check`, `make test`, `make test-mutations`, `make paper`, standalone reader/plan/contract checks, a two-worker final article-axiom audit, and `git diff --check`.

**What is in the tree:** 609 `NSFormalization` sources; 44 configured HeliCorgi roots; 66 Bindings sources; 36 Tests sources; 36 enabled registry entries; 41/41 Closed proof nodes; 27/27 Closed article entries. The cleaned formalization subtree has 609 `.olean` files, and all 102 current Bindings/Tests sources have matching `.olean` files.

**What is not green, with exact text:** `verification/README.md` says `There are 30 current typed acceptance interfaces.` while the executable count is 36. The requested audit expectation was 72, while the executable summary is `76 declarations; 27 article entries; 0 forbidden-axiom results`. The initial stale check failed with `AssertionError: Source changed: rerun the article axiom audit`; after the separate artifact commit, every final gate was green. All warning start lines are quoted above.

**Commands and results:** Full rebuild rc 0, 443.14 s, 609 Built, 0 Replayed, 0 error matches; Bindings/Tests build rc 0, 95.20 s, all 102 current artifacts present, 0 error matches. Final `make check`/`make test`/`make test-mutations`/`make paper`/reader check/plan regeneration/article audit/`git diff --check`/contract summary all returned 0 in 11.80/2.09/13.11/1.59/0.04/7.77/38.52/0.00/3.84 seconds. The final audit matched the regenerated checked-in JSON byte-for-byte.
