ACCEPT

## 1. What the lane claims

Reviewed HEAD `2815d6073552a1c0e9010583106f9b00fc824e4e` against local remote-tracking integration `eb1b5796f90a741d6c82ec7b64ac19003e5ea924`. No fetch, index changes, commits, or edits to existing files were made.

`research/R47/REPORT_253.md:5` claims the exact lane-251 compact momentum identity without an additional analytic hypothesis; `:9` claims force zero mean and observation equality on [0,T), retaining only the original `hg` for observations. `:14` claims 12 theorems, and `:23` claims standard axioms and four application examples. All are present with the claimed mathematical statements.

## 2. What is in Lean

- **Exact input discharged:** `verification/Bindings/FluxCancellation.lean:229` matches `verification/Bindings/ForceCellIntegral.lean:146` (and `:205`): same R42 record, positive scale interval Ioc, same containing grid cell, same interior time interval Ioo, viscosity, residual difference, and whole-space time derivative. There is no added premise. The applications at FluxCancellation `:286` and `:294` kernel-check this interface.
- **All 12 declarations:** FluxCancellation `:36` proves integrability and zero integral of a compact smooth vector directional derivative; `:50` sums the three flux derivatives; `:60` proves tensor-difference compactness; `:70` proves integrability and zero mean of the advection difference under the two honest divergence hypotheses; `:102` proves spatial pressure-gauge invariance for arbitrary c(t); `:108` and `:133` prove the pressure-gradient and Laplacian difference results; `:170` proves the integrated residual identity with explicitly named smoothness, compactness, divergence, temporal differentiability, and residual integrability assumptions; `:218` supplies reference pressure smoothness; `:229`, `:282`, and `:289` supply the three requested conclusions. The generic assumptions are discharged from A inside the main proof, not passed to its caller.
- **Paper fidelity:** opened `paper/sections/04-whole-space.tex:305–320` using sed. The tensor difference, positive pressure term, negative ν-Laplacian term, and time derivative match eq:gridforce at `:314`. Conservative form uses the actual `formalization/NSFormalization/Section4/A01/ConvectionDivergence.lean:113`, whose Leibniz proof is at `:92`. The residual definition is `verification/Contracts/V1/Packet.lean:127`; the underlying inserted equation was inspected at `formalization/NSFormalization/Section4/R42/Assembly.lean:122`.
- **Support and gauge:** `verification/Contracts/V1/InsertionFamily.lean:255` already localizes the actual pressure difference in the chosen compact gauge (pressure formula at `:183`); no extra gauge assumption is hidden. FluxCancellation `:246` obtains compactness from this field. Its independent gauge lemma at `:102` needs no time regularity. The containing-cell assumption is sufficient because the closed supports lie in the open insertion ball.
- **No totalized-integral shortcut:** FluxCancellation `:39`, `:55`, `:189`, `:204`, and `:250` establish the needed integrability. The residual difference is identified with the smooth compact force difference via ForceCellIntegral `:75`, then restricted to the whole space at FluxCancellation `:257`. This uses momentum and support, never force zero mean, so it is not circular. Although the inherited time-mean lemma has an `integral_undef` branch at ForceCellIntegral `:136`, the present lane independently establishes temporal integrability at FluxCancellation `:204`.
- **Time endpoints and non-vacuity:** force conclusions use Ico at FluxCancellation `:283` and `:290`; time zero is handled by ForceCellIntegral `:89`, `:155`, not by a two-sided derivative assertion there. The existing audit `research/R47/axioms_flux_cancellation.lean:24` chooses ε=A.ε₀ and t=A.T/2, using strict positivity; `:34` and `:46` apply the main conclusions with no flux input; `:56` checks gauge t². These are nonempty-range applications conditional on an actual R42 record, not an independent existence proof, as honestly stated in `research/R47/ATTEMPTS_FLUX.md:104`. The existing construction `verification/Bindings/InsertionFamily.lean:189` supplies precisely this record from scaling and its reference solution. No new contradictory premise, unused quantified datum, or ENNReal.toReal bound was introduced. Grid cell averaging uses the existing bounded positive-width cells and actual integral equalities, not an infinite-volume zero normalization.
- **Cited tree lemmas opened:** `formalization/NSFormalization/Paper3/CompactObservations.lean:33`, `Paper3/TimeObservations.lean:15`, A01 conservative form above, and Mathlib `Analysis/Calculus/LineDeriv/IntegrationByParts.lean:212`. Their hypotheses agree with the uses in the two lanes.
- **Hygiene:** the triple-dot diff lists exactly the four added deliverables below, with no modified existing module. No forbidden token or heartbeat override appears in the new module or audit. All 12 printed axiom lists are exactly the required three. `experiments/build_changed_lean.py:18` covers this new binding; its dry run selects `Bindings.FluxCancellation`.

## 3. Gaps

No blocking mathematical or build gap remains in this lane. Full RGridFamily assembly and registration are explicitly out of scope at `research/R47/REPORT_253.md:29`, not claimed as completed.

For the requested whole-tree absence check, ran `grep -rn -E 'integral_fderiv_eq_zero_of_hasCompactSupport|RGridFamily|compactMomentumIntegral' formalization/NSFormalization/Section4`: no matches (exit 1). Also searched all pinned Mathlib for the suggested derivative-integral name: no matches (exit 1), confirming the narrowly phrased claim at `research/R47/ATTEMPTS_FLUX.md:28`. A broader whole-Section4 derivative/integral search found existing integration-by-parts uses in A05/HessianLaplacian, D01/OrderZeroCurl, D01/OrderZeroSymbol and A01/PressureRegularity; no claim that integration-by-parts infrastructure is absent is accepted or needed.

The worker's recorded `--base-ref HEAD` run at `research/R47/REPORT_253.md:46` alone would not meet the review gate. The required integration-reference check passes in this review. The currently reviewed HEAD includes the integration merge, so the older report's no-merge statement is treated as the worker's historical action report, not a description of current branch ancestry.

**Substantive negative check:** `research/R47/probes/rev253_wrong_force_mean.lean:12` changes the main force-mean conclusion from 0 to coordinateVector 0, preserving every binder and the original proof. Lean rejects it with the expected equality-target type mismatch at `:13`, reproduced below. This changes a mathematical constant, not an argument list.

Fixes required: none.

## 4. Commands and results

Read CLAUDE.md, lane-review SKILL.md, NEXT_SESSION.md, HANDOFF §0, the first 40 LESSONS lines, both lane reports/attempts, all ForceCellIntegral and GridLemmas, and the cited sources. Used the already installed, symlinked package environment; did not rerun the installer because the review is read-only. All actual lake invocations ran from verification after sourcing scripts/lean-env.sh, with LEAN_NUM_THREADS=6. Large gate JSON output is quoted verbatim at the first/last 40 lines, with explicit omission markers.

### Module build and direct check

```sh
. scripts/lean-env.sh
cd verification
LEAN_NUM_THREADS=6 lake build Bindings.FluxCancellation
```

Exit 0. No diagnostic from FluxCancellation; only existing dependency replay warnings. Exact first two and last output lines:

```text
⚠ [8779/8830] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
[... dependency replay warnings omitted ...]
Build completed successfully (8830 jobs).
```

Other replay-warning modules: Source.RealSobolev, Paper3.SpatiallyCompactTime, Paper3.RealPositiveDensity, Paper3.RealVectorPositiveDensity. This meets “silent for this module”; it is not a claim of globally silent dependencies.

```sh
. scripts/lean-env.sh
cd verification
LEAN_NUM_THREADS=6 lake env lean Bindings/FluxCancellation.lean
```

Exit 0, stdout/stderr 0 bytes.

### Axiom audit and existing non-vacuity examples

```sh
. scripts/lean-env.sh
cd verification
LEAN_NUM_THREADS=6 lake env lean ../research/R47/axioms_flux_cancellation.lean
```

Exit 0; exact complete output:

```text
'BlowupDensity.Bindings.compact_directional_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.compact_flux_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.tensorDifference_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.advectionDifference_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.pressureGradient_sub_timeConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.pressureGradientDifference_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.laplacianDifference_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.residualDifference_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.insertion_reference_pressure_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.compactMomentumIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.forceDifference_cell_integral_zero'' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.force_gridObservation_eq'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Architecture and integration compatibility checks

The following are exact captured first/last 40 output lines for each large command, including the capture wrapper's command, exit, and line-count metadata.

```text
COMMAND: make check EXIT: 0 LINES: 33680
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 548,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
{
  "registered_contracts": 32,
  "closures": {
    "R41.threshold_arithmetic": [
      "Bindings.Thresholds",
      "Contracts.V1.Thresholds",
      "NSFormalization.Paper3.Thresholds",
      "TestSupport.Axioms",
      "Tests.Thresholds"
    ],
    "I01.packet": [
      "Bindings.Packet",
      "Contracts.V1.Packet",
      "NSFormalization.Paper1.ScalarEnergy",
      "NSFormalization.Section4.I01.Energy",
      "NSFormalization.Section4.I01.Extension",
[... middle omitted ...]
      "NavierStokes.TransitionRamp",
      "NavierStokes.TransportPrimitive",
      "NavierStokes.TrueConeLoop",
      "NavierStokes.UniformAngularReset",
      "NavierStokes.UniformBlockBounds",
      "NavierStokes.UniformCone",
      "NavierStokes.UniformFourierAlias",
      "NavierStokes.UniformHarmonicInteraction",
      "NavierStokes.UniformPrimaryWeights",
      "NavierStokes.ValidBandGluing",
      "NavierStokes.ValidDyadicBandCover",
      "NavierStokes.VariableGaugeMean",
      "NavierStokes.ViscousPropagator",
      "NavierStokes.VolterraAnalyticBounds",
      "NavierStokes.VolterraParity",
      "NavierStokes.VolterraRegularity",
      "NavierStokes.WaveEdgeExtension",
      "NavierStokes.WaveEnvelopeTransport",
      "NavierStokes.WaveInteractionBounds",
      "NavierStokes.WaveStateRegularity",
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.MainThresholds"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.041s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
COMMAND: python3 experiments/check_contracts.py --base-ref origin/erenup/integration EXIT: 0 LINES: 33648
{
  "registered_contracts": 32,
  "closures": {
    "R41.threshold_arithmetic": [
      "Bindings.Thresholds",
      "Contracts.V1.Thresholds",
      "NSFormalization.Paper3.Thresholds",
      "TestSupport.Axioms",
      "Tests.Thresholds"
    ],
    "I01.packet": [
      "Bindings.Packet",
      "Contracts.V1.Packet",
      "NSFormalization.Paper1.ScalarEnergy",
      "NSFormalization.Section4.I01.Energy",
      "NSFormalization.Section4.I01.Extension",
      "NSFormalization.Section4.I01.Quiet",
      "NSFormalization.Source.Insertion",
      "NSFormalization.Source.PacketEndpoint",
      "NSFormalization.Source.PacketEnergy",
      "NSFormalization.Source.PacketForceExtension",
      "NSFormalization.Source.PacketPressure",
      "NSFormalization.Source.PacketScaling",
      "NSFormalization.Source.ParabolicScaling",
      "NSFormalization.Source.SelectedPacketEnergy",
      "NSFormalization.Source.ViscosityPacket",
      "NSFormalization.Source.ViscosityScaling",
      "NavierStokes.ActivationBounds",
      "NavierStokes.ActivationCone",
      "NavierStokes.ActivationContinuation",
      "NavierStokes.ActivationHolomorphic",
      "NavierStokes.ActivationStocks",
      "NavierStokes.ActiveAnnulusWeight",
      "NavierStokes.ActualBaseResidual",
      "NavierStokes.ActualBaseVelocityBounds",
      "NavierStokes.ActualCandidateAssembly",
      "NavierStokes.ActualCandidateConstruction",
      "NavierStokes.ActualCarrierGeometry",
      "NavierStokes.ActualCarrierTransport",
      "NavierStokes.ActualCarrierTransportBase",
[... middle omitted ...]
      "NavierStokes.TerminalEdgeFactor",
      "NavierStokes.TerminalHistoryBridge",
      "NavierStokes.TerminalPressure",
      "NavierStokes.TerminalStress",
      "NavierStokes.TimeLocalization",
      "NavierStokes.TorusAverages",
      "NavierStokes.TorusInverse",
      "NavierStokes.TorusMeanRequestRebase",
      "NavierStokes.TransitionRamp",
      "NavierStokes.TransportPrimitive",
      "NavierStokes.TrueConeLoop",
      "NavierStokes.UniformAngularReset",
      "NavierStokes.UniformBlockBounds",
      "NavierStokes.UniformCone",
      "NavierStokes.UniformFourierAlias",
      "NavierStokes.UniformHarmonicInteraction",
      "NavierStokes.UniformPrimaryWeights",
      "NavierStokes.ValidBandGluing",
      "NavierStokes.ValidDyadicBandCover",
      "NavierStokes.VariableGaugeMean",
      "NavierStokes.ViscousPropagator",
      "NavierStokes.VolterraAnalyticBounds",
      "NavierStokes.VolterraParity",
      "NavierStokes.VolterraRegularity",
      "NavierStokes.WaveEdgeExtension",
      "NavierStokes.WaveEnvelopeTransport",
      "NavierStokes.WaveInteractionBounds",
      "NavierStokes.WaveStateRegularity",
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.MainThresholds"
    ]
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

The copied-source `sorry` reported by the architecture census is pre-existing Paper1/BoundaryCorollary, outside this lane's audited dependency proof constants; it is not a token added by this lane. The gate exits successfully; all new theorem axiom closures above are clean.

### Full gates

```sh
. scripts/lean-env.sh
export LEAN_NUM_THREADS=6
function make() {
  if [[ "$#" == 1 && "$1" == test ]]; then
    (cd verification && lake test)
  else
    command make "$@"
  fi
}
export -f make
bash scripts/gates.sh Bindings.FluxCancellation
```

Exit 0; 33788 output lines. The shell-local wrapper only runs the unchanged `make test` recipe from verification, preserving the review's cwd rule; no script or Makefile was edited. The module build, contract tests, mutation suite and integration-base check all ran. Exact final ten lines:

```text
info: Tests/MainThresholds.lean:15:0: Contract BlowupDensity.Tests.checkedMainThresholds: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

The script filters contract-test output, but the mutation runner itself invokes `lake test` with `check=True` (`experiments/test_contract_mutations.py:60`), so its completed suite also confirms successful contract compilation. All three expected rejected mutations passed the runner's assertions.

### Lane-specific negative probe

```sh
. scripts/lean-env.sh
cd verification
LEAN_NUM_THREADS=6 lake env lean ../research/R47/probes/rev253_wrong_force_mean.lean
```

Exit 1, expected. Complete output:

```text
../research/R47/probes/rev253_wrong_force_mean.lean:13:2: error: Type mismatch
  forceDifference_cell_integral_zero A (compactMomentumIntegral A) hε ht grid k₀ hB
has type
  ∫ (x : NavierStokes.ProblemStatement.Space) in NSFormalization.Paper3.CartesianGrid.cell grid k₀,
      A.force ε (t, x) - A.g (t, x) =
    0
but is expected to have type
  ∫ (x : NavierStokes.ProblemStatement.Space) in NSFormalization.Paper3.CartesianGrid.cell grid k₀,
      A.force ε (t, x) - A.g (t, x) =
    NavierStokes.ProblemStatement.coordinateVector 0
```

The positive control is the unchanged theorem at FluxCancellation:282, accepted by the zero-output direct module check. The failed probe is intentionally left under the expressly authorized reviewer probe path.

### Hygiene and CI coverage

```sh
git diff --name-only origin/erenup/integration...HEAD
```

Exit 0, exact output:

```text
research/R47/ATTEMPTS_FLUX.md
research/R47/REPORT_253.md
research/R47/axioms_flux_cancellation.lean
verification/Bindings/FluxCancellation.lean
```

`git diff --name-status origin/erenup/integration...HEAD` marks all four as A.
`git diff --check`: exit 0, no output.
`rg -n '\\b(sorry|admit|axiom|native_decide)\\b|maxHeartbeats' verification/Bindings/FluxCancellation.lean research/R47/axioms_flux_cancellation.lean`: exit 1, no matches (the audit's `#print axioms` is not an axiom declaration).

```sh
python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run
```

Exit 0, exact output:

```text
Changed Lean modules: Bindings.FluxCancellation
```

Required fixes: none.

