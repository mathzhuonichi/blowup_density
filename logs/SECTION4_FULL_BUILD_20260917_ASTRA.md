# Section 4 independent full build — Astra, 2026-09-17

## Environment

Verified HEAD: `0832de60c16e0f4695dfd9cf620262a0d84d83b3`, branch
`erenup/282-MAINT-s4-full-build-astra`, in the assigned worktree. Initial tracked
status was clean. Read `CLAUDE.md` first and sourced `. scripts/lean-env.sh`.
Lean processes used `LEAN_NUM_THREADS=6`; direct Lake calls ran from `verification/`.
Root-level make targets select that same verification workspace.

```
Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)
Lake version 5.0.0-src+6a10ac8 (Lean version 4.34.0-rc2)
```

Mathlib lock: `85e3a25e006c35636f0e53b0e9296caca2685bc0`, inputRev
`v4.34.0-rc2`, from `verification/lake-manifest.json`.
Local `main` used by the compatibility gate: `4ba9f2b40c4df8c87b19342395b03fa4bfde17a8`.
No push, merge, rebase, source edit, or dependency installation was performed.
Only this report is a new tracked file; scratch logs/probes are in gitignored
`tmp/282-astra/` in this worktree.

## Full build

Filesystem enumeration (`find`, not a Git pathspec) found **206 modules**, including
`Section4/HeliCorgiPort.lean`. Before building, removed only these existing directories:

- `formalization/.lake/build/lib/lean/NSFormalization/Section4/`
- `formalization/.lake/build/ir/NSFormalization/Section4/`

Both resolved inside this worktree; the library directory was confirmed absent after
deletion. Mathlib/vendor caches were retained. All 206 generated module names were
passed to **one** `lake build` invocation. The log contains exactly **206**
`Built NSFormalization.Section4.*` entries: this was genuine re-elaboration.

| Measurement | Result |
|---|---|
| Wall time (Python monotonic clock around subprocess) | 219.648 seconds |
| Exit code | 0 |
| Errors (`^error` or `error:`) | 0 |
| Final line | `Build completed successfully (10636 jobs).` |
| Warning diagnostics (`^warning:`) | 74 |

There are 95 lines containing `warning:`, but 21 are hint continuations, not separate
warnings. Of the 74 diagnostics, **46 are replayed HeliCorgi warnings**, **19 replayed
Source warnings**, **7 replayed Paper3 warnings**, and **2 freshly emitted Section 4
warnings**. Each non-Section4 warning was associated with a `Replayed` log entry.
They concern unused arguments/variables, unnecessary `simpa` or sequencing, tactic
suggestions, deprecated lemmas, and one proposition defined with `def`.

Fresh Section 4 warnings, verbatim:

```
warning: NSFormalization/Section4/A01/AprioriFamily.lean:148:31: Variable name `ha` is not explicitly referenced.
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.
```

All warning-bearing files and diagnostic counts (paths as printed by Lake):

| File | Count |
|---|---:|
| `../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean` | 5 |
| `../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean` | 4 |
| `../vendor/HeliCorgi/Formal/R3ConvectionSourceIdentification.lean` | 4 |
| `../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean` | 4 |
| `../vendor/HeliCorgi/Formal/R3DivergencePointwise.lean` | 1 |
| `../vendor/HeliCorgi/Formal/R3H2LerayBridge.lean` | 1 |
| `../vendor/HeliCorgi/Formal/R3L2ScalarAux.lean` | 1 |
| `../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean` | 1 |
| `../vendor/HeliCorgi/Formal/R3LerayFourierBridge.lean` | 1 |
| `../vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean` | 1 |
| `../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean` | 2 |
| `../vendor/HeliCorgi/Formal/R3ProjectedMomentumDuhamelInfrastructure.lean` | 5 |
| `../vendor/HeliCorgi/Formal/R3SobolevCarrier.lean` | 1 |
| `../vendor/HeliCorgi/Formal/R3SobolevConvectionExtension.lean` | 2 |
| `../vendor/HeliCorgi/Formal/R3StokesH2H3Smoothing.lean` | 2 |
| `../vendor/HeliCorgi/Formal/R3StokesL2Operator.lean` | 1 |
| `../vendor/HeliCorgi/Formal/R3YoungRealL1L2Bochner.lean` | 2 |
| `../vendor/HeliCorgi/Formal/R3YoungRealSetIntegralBridge.lean` | 3 |
| `../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean` | 5 |
| `NSFormalization/Paper3/RealPositiveDensity.lean` | 4 |
| `NSFormalization/Paper3/RealVectorPositiveDensity.lean` | 1 |
| `NSFormalization/Paper3/SobolevDirectionalDerivative.lean` | 1 |
| `NSFormalization/Paper3/SpatiallyCompactTime.lean` | 1 |
| `NSFormalization/Section4/A01/AprioriFamily.lean` | 1 |
| `NSFormalization/Section4/A01/MildGronwall.lean` | 1 |
| `NSFormalization/Source/BoundedReferenceComparison.lean` | 2 |
| `NSFormalization/Source/BoundedReferenceFlux.lean` | 1 |
| `NSFormalization/Source/BoundedViscosityUniqueness.lean` | 1 |
| `NSFormalization/Source/FiniteHilbertBochner.lean` | 3 |
| `NSFormalization/Source/FractionalRealization.lean` | 3 |
| `NSFormalization/Source/PacketForceExtension.lean` | 1 |
| `NSFormalization/Source/RealSobolev.lean` | 3 |
| `NSFormalization/Source/RieszL2Fourier.lean` | 1 |
| `NSFormalization/Source/RieszPotentialNearField.lean` | 3 |
| `NSFormalization/Source/ViscosityPacket.lean` | 1 |

## Gates

All four requested gates passed. Logs are `check.log`, `test.log`, `mutations.log`,
and `base.log` under `tmp/282-astra/`.

| Command from worktree root | Exit | Wall seconds |
|---|---:|---:|
| `make check` | 0 | 9.774 |
| `make test` | 0 | 24.073 |
| `make test-mutations` | 0 | 13.382 |
| `python3 experiments/check_contracts.py --base-ref main` | 0 | 4.868 |

Key outputs:

```
Ran 13 tests in 0.044s
OK
30 work items: ownership, contract registration and task cards consistent.
"registered_contracts": 37
"base_compatibility_checked": true
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

The base-compatibility value above is from the explicit `--base-ref main` invocation;
the unbased checker inside `make check` appropriately reports false.

## Axiom audit

The registry contains **37 contracts, all enabled, with 37 distinct Tests modules**.
`make test` emitted **39 distinct successful `checkAxioms` messages**. A set comparison
against every registry `declaration` found **zero missing declarations**. The two
additional audited declarations were:

- `BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4`
- `BlowupDensity.Tests.energyAbsorptionV4_terminalFinite`

`checkAxioms` checks actual transitive dependencies and permits only `propext`,
`Classical.choice`, and `Quot.sound`; its message does not enumerate the set.
Therefore a supplemental probe imported each registered Tests module separately and
ran `#print axioms` on its registered declaration. **All 37 processes exited 0**, and
all 37 printed **exactly `[propext, Classical.choice, Quot.sound]`**. Total probe wall
time: 93.635 seconds. Output: `tmp/282-astra/axioms-individual.log`.

Every declaration below has both successful `checkAxioms` coverage and the exact
three-axiom set (declaration names share the prefix `BlowupDensity.Tests.`):

| Contract id | Declaration |
|---|---|
| `R41.threshold_arithmetic` | `checkedThresholds` |
| `I01.packet` | `checkedPacket` |
| `I02.correction` | `checkedCorrection` |
| `I02.correction_v2` | `checkedCorrectionV2` |
| `A05.gradient_l6` | `checkedGradientL6` |
| `A03.bounded_representative` | `checkedBoundedRepresentative` |
| `I03.scaling` | `checkedScaling` |
| `A03.tame_products` | `checkedTameProduct` |
| `R42.insertion_family` | `checkedInsertionFamily` |
| `D01.datum_lemmas` | `checkedDatumLemmas` |
| `D01.datum_lemmas_v2` | `checkedDatumLemmasV2` |
| `D01.datum_lemmas_v3` | `checkedDatumLemmasV3` |
| `A02.uniqueness` | `checkedUniqueness` |
| `A02.maximal_partial` | `checkedMaximalPartial` |
| `A02.maximal_partial_v2` | `checkedMaximalPartialV2` |
| `B01.bochner_partial` | `checkedBochnerPartial` |
| `C01.energy_absorption_partial` | `checkedEnergyAbsorptionPartial` |
| `C01.energy_absorption_partial_v2` | `checkedEnergyAbsorptionPartialV2` |
| `R42.insertion_lifespan` | `checkedInsertionLifespan` |
| `B02.homogeneous_partial` | `checkedHomogeneousPartial` |
| `A01.regularity_partial` | `checkedRegularityPartial` |
| `R42.insertion_lifespan_v2` | `checkedInsertionLifespanV2` |
| `B02.homogeneous_partial_v2` | `checkedHomogeneousPartialV2` |
| `A04.energy_high_partial` | `checkedEnergyHighPartial` |
| `A04.energy_high_partial_v2` | `checkedEnergyHighPartialV2` |
| `C01.energy_absorption_partial_v3` | `checkedEnergyAbsorptionPartialV3` |
| `C01.energy_absorption_v4` | `checkedEnergyAbsorptionV4` |
| `D01.homogeneous_norm` | `checkedHomogeneousNorm` |
| `A05.gradient_l6_v2` | `checkedGradientL6V2` |
| `R43.critical_regularity` | `checkedCriticalRegularity` |
| `R44.critical_finite_horizon` | `checkedCriticalFiniteHorizon` |
| `R41.main_thresholds` | `checkedMainThresholds` |
| `R45.force_classes` | `checkedForceClasses` |
| `A01.local_theory_v2` | `checkedLocalTheoryV2` |
| `A04.continuation_v2` | `checkedContinuationV2` |
| `R47.grid_observations` | `checkedGridObservations` |
| `R46.completed_density` | `checkedCompletedDensity` |

### Supplemental combined-import anomaly

Before the separate probes, an exploratory `Audit.lean` imported all 37 Tests modules
in one environment. That supplemental command exited **1** (1.957 seconds):

```
../tmp/282-astra/Audit.lean:1:0: error: import Bindings.Scaling failed, environment already contains 'BlowupDensity.Bindings.navierStokesResidual_eq' from Bindings.Packet
```

This is a real combined-import name collision; it does not invalidate the separately
compiled Tests modules or any requested gate. No code was changed. Separate probes
completed the exact axiom audit. The report establishes the existing module/gate
workflow, not that every Tests module can be imported together into one environment.

## Forbidden tokens & heartbeats

Ran the exact requested scan across Section4, Contracts (all versions), Bindings,
and Tests:

```sh
grep -rnE "^\s*(axiom|sorry|admit)\b|native_decide" formalization/NSFormalization/Section4 verification/Contracts verification/Bindings verification/Tests
```

Exit 0 means a match was found. The **only** hit was:

```
formalization/NSFormalization/Section4/R43/Pieces.lean:15:`native_decide`, and no placeholder `Prop`.
```

This is prose inside the module docstring (the preceding line says “It contains no
`sorry`, no `axiom`, no”). No executable forbidden token was found by this scan;
there were no `declaration uses 'sorry'` build warnings.

Every Section 4 numeric `set_option maxHeartbeats N` with `N > 400000`:

| File (relative to Section4) | Line | N |
|---|---:|---:|
| `A03/ScalarTameProduct.lean` | 249 | 1200000 |
| `A01/ForcedSourceUpgrade.lean` | 51 | 800000 |
| `A01/ForcedSourceUpgrade.lean` | 85 | 800000 |
| `A01/ForcedMaximalRegularity.lean` | 58 | 800000 |
| `A01/ContinuationInvariant.lean` | 60 | 600000 |

## Comparison with the earlier report

Read `logs/SECTION4_FULL_BUILD_20260917.md` **only after** the full build, all gates,
forbidden-token/heartbeat scan, and all 37 individual axiom probes had finished and
passed. Its verified commit is `ee71af7db3b59609917048e55c3120c0ed906692`, whereas this
run verified `0832de60c16e0f4695dfd9cf620262a0d84d83b3`. `git diff --name-only` between
those commits lists only `logs/SECTION4_FULL_BUILD_20260917.md`: the proof sources,
verification harness, scripts, and toolchain are unchanged.

Agreements: 206 modules, 37 registered contracts, 206 fresh builds, 10636 Lake jobs,
zero build errors, 74 warnings with identical source distribution and identical two
Section 4 diagnostics, all gates passing, 39 audited declarations including the same
two extra helpers, standard-axiom-only dependencies, and the same five elevated
heartbeat settings. This run additionally confirms the exact three-axiom set for
all 37 registered declarations.

Differences: this build took 219.648 seconds versus 232 seconds. Our requested anchored
scan covers four trees and yields one prose hit; the earlier broader unanchored scan
of Section4 alone counted 20 prose hits. These are different scan expressions, not a
contradiction. The earlier report mentions two stale seeded oleans; this run deleted
the specified directories without inventorying stale artifacts and does not claim to
independently confirm that observation. The supplemental combined-import collision
above was not reported earlier. No disagreement in the requested build/gate outcome
was found. This is a local verification of the recorded HEAD, not a fresh remote PR
head or cloud CI check, nor a new paper-to-contract semantic review.

## Exact commands and outputs' key lines

Environment and enumeration:

```sh
cat CLAUDE.md
git status --short
git rev-parse HEAD
. scripts/lean-env.sh
lean --version
lake --version
find formalization/NSFormalization/Section4 -name '*.lean' | sort > tmp/282-astra/sources.txt
wc -l tmp/282-astra/sources.txt
```

Key lines: HEAD and version strings in Environment; `206 tmp/282-astra/sources.txt`.
Mathlib was selected by `p['name'] == 'mathlib'` from the manifest's `packages` list.
The exact expanded 206-target command is saved in `tmp/282-astra/build-command.txt`;
it was generated and executed using this Python code (after sourcing the environment
and `export LEAN_NUM_THREADS=6`):

```python
root = pathlib.Path.cwd()
mods = [p.removeprefix('formalization/').removesuffix('.lean').replace('/', '.')
        for p in (root/'tmp/282-astra/sources.txt').read_text().splitlines()]
for p in ['formalization/.lake/build/lib/lean/NSFormalization/Section4',
          'formalization/.lake/build/ir/NSFormalization/Section4']:
    q = root/p
    assert q.resolve().is_relative_to(root)
    if q.exists(): shutil.rmtree(q)
assert not (root/'formalization/.lake/build/lib/lean/NSFormalization/Section4').exists()
cmd = ['lake', 'build', *mods]
t = time.monotonic()
with open(root/'tmp/282-astra/build.log', 'w') as f:
    r = subprocess.run(cmd, cwd=root/'verification', stdout=f, stderr=subprocess.STDOUT)
```

Result: exit 0, 219.648 seconds, `Build completed successfully (10636 jobs).`
Gate commands and key lines are recorded in Gates above; each ran with the sourced
environment and `LEAN_NUM_THREADS=6`. The check/base gates ran while the full build
was in progress; `make test` and mutations ran sequentially after the build finished.

Supplemental audit commands, run from `verification/`:

```sh
lake env lean ../tmp/282-astra/Audit.lean
```

The combined probe's exact error is recorded above. For each registry entry, Python
wrote `tmp/282-astra/Audit00.lean` through `Audit36.lean`, each containing:

```lean
import <entry.test_module>
#print axioms <entry.declaration>
```

Each was executed as `subprocess.run(['lake', 'env', 'lean', str(p)],
cwd=root/'verification', capture_output=True, text=True)`, where `p` is the absolute
probe path. Example output:

```
'BlowupDensity.Tests.checkedThresholds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All 37 exact sets were compared programmatically with the registry and permitted set.
Heartbeat enumeration iterated every Section4 `*.lean` file and every line, matching
`r'set_option\s+maxHeartbeats\s+(\d+)'` and selecting `int(N) > 400000`.

Final comparison commands:

```sh
cat logs/SECTION4_FULL_BUILD_20260917.md
git diff --stat ee71af7db3b59609917048e55c3120c0ed906692 HEAD -- formalization verification scripts experiments Makefile lean-toolchain
git diff --name-only ee71af7db3b59609917048e55c3120c0ed906692 HEAD
```

The first diff is empty; the second lists only the earlier report.
