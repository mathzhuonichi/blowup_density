ACCEPT-WITH-NOTES

## 1. What the lane claims

Reviewed HEAD `5e8bec356c8bf2382bb76953a7667279df78b3c2` against local
`origin/erenup/integration = 071a9e8a27c6e480709072c407515267cd4679b7`.
Read CLAUDE.md, lane-review/SKILL.md, the first 40 LESSONS lines, the supplied
brief, reports 224/227/228/229, the sibling absorption source through git show,
the split/spec/comparison/attempts records, and HANDOFF §0 and §2 P6/P10.
The user’s read-only scope supersedes installation/record-edit workflow steps;
the existing dependency cache is already symlinked and operational.

REPORT_229.md:5 claims unconditional Proposition 4.4 with the fixed radius;
:14 claims q=2 non-density for s≥−1/2; :17 lists 25/4/3 declarations;
:24 identifies all nine API field values/proofs without claiming a registered
structure witness; :30 claims 56+19 standard axiom reports. These mathematical
and audit claims check out. The records-closure claim at :36 needs the one-line
fix below.

## 2. What is in Lean

Paths below beginning R44/ or R41/ are relative to
`formalization/NSFormalization/Section4/`.

- Statement fidelity: R44/Prop44.lean:14 and :24 have exactly the requested
  positive ν,S, admissible f, strict global inhomogeneous L² H^(−1/2) smallness,
  and strict zero-datum lifespan conclusion. R44/Prop44.lean:32 gives the
  identical-radius exclusion. Compare research/R44/Spec.lean:266 and :300,
  and paper/sections/04-whole-space.tex:136–144 (opened with sed).
  No differential provider remains in these statements.
- R44/Absorption.lean:250 supplies one derivative function, integrable on every
  closed presingular window 0≤S<T, with derivative identity and conditional
  inequality on Ioo 0 T. The explicit derivative at :101, pairing bridge at
  :42/:50, and scalar absorption at :133 preserve lane 228’s mathematics.
  Lane 228 receives credit at :7. Constants are renamed at :65/:68/:73,
  and its provider spelling is retained at :300.
- The adapter at R44/Absorption.lean:281 constructs Endpoint’s existing
  structure (:57), without duplicate types. At :269 the reciprocal comparison
  uses trilinearConstJ=3*Cemb³ (R44/TrilinearJ.lean:416) and positivity;
  12*Cemb³≤100*(Cemb+1)³ gives theta≤thetaAbs. At :292/:293 coefficients
  increase from 3/2,3 to 2,4, with positive viscosity and squared factors.
  This is the paper’s eq:Rcritical2 at paper/sections/04-whole-space.tex:160–164.
- Opened the cited suppliers: R44/EnergyIdentity.lean:286 is the actual
  unconditional classical-solution energy derivative; R44/TrilinearJ.lean:563
  bounds the same advection pairing; R41/NonDensityL1.lean:42 proves norm
  monotonicity for every q and physical force, including absent datum paths.
  R44/Absorption.lean:29 constructs the required advection datum from each
  classical slice, rather than adding it as a hypothesis.
- No top-toReal vacuity: R44/JWeight.lean:149/:155/:168 identify Y,Z²,B with
  finite datum norms; R44/EnergyIdentity.lean:64 constructs these data on valid
  classical slices. Endpoint.lean:98 uses a MemLp force path and explicitly
  supplies finiteness for toReal monotonicity. Endpoint.lean:280 proves the
  lifespan finite before converting it to a real at :282. Its positive
  lifespan guard is explicit at :285.
- Universal constants are fixed before ν,S,f (Endpoint.lean:22–41), with
  radius=(theta/20)*ν^(3/2:ℝ)*exp(−3νS)>0 for ν>0. All nine spec components
  are available: c/C/radius and their positivity from Endpoint, formula from
  research/R44/axioms_prop44.lean:58, main/exclusion from :41/:50.
  The unused positive-S proof in radiusPos (:63) is harmless: positivity
  actually holds for every real S. Endpoint’s unused _hf structure index
  is also harmless; the unconditional provider requires admissibility and
  proves the structure for all classical solutions.
- R41/NonDensityL2.lean:14/:24/:32 prove respectively the explicit-radius
  lower bound, the requested existential bound, and failure of BreakdownDenseR.
  They use the imported definitions at NonDensityL1.lean:58–79, matching
  Data.lean:672/:678/:686/:702/:707. The actual Data-vocabulary theorems and
  lifespan/set/density equality bridges compile in
  research/R41D/axioms_nondensity_l2.lean:25/:40/:51/:57.
  The threshold agrees with verification/Contracts/V1/Thresholds.lean:15.
  Paper/sections/04-whole-space.tex:179 explicitly gives this q=2 deduction.
  The brief’s research/section4/STATEMENTS.md:140–146 citation has drifted
  (it now begins a contract skeleton); the authoritative paper/spec agree.
- Non-vacuity is already supplied: Prop44.lean:40 proves actual strict zero-force
  smallness and :51 applies the endpoint. The audits instantiate zeroSol at
  research/R44/axioms_prop44.lean:70 and Data non-density at ν=T=1 at
  research/R41D/axioms_nondensity_l2.lean:66. All these examples compile.
- Hygiene: no forbidden proof token or heartbeat override in any of the three
  new modules; all 32 named declarations are audited. Three-dot diff shows
  only new implementation modules, no changed existing Lean file and no
  verification change. Endpoint is unchanged against both integration and
  lane 227; TrilinearJ is unchanged against integration.

## 3. Gaps and exact fix

1. **Documentation, one-line fix.** research/R44/REPORT_229.md:36 says the split
   ledger records closure, but research/R44/R44_SPLIT.md:191/:198/:200 still
   says S1 is pending, and the file is absent from the lane diff.
   Insert immediately after the title of R44_SPLIT.md this exact single line:

   > Current status (lane 229; supersedes the historical status text below): S1–S6 and G1–G5 are closed in implementation by R44.Absorption.rCritical2Differential_of_classical and R44.Prop44.main/nonDensityBallZero; all nine RCritical2API field values/proofs are available with c=theta/20 and C=3, q=2 non-density is proved in R41.NonDensityL2, and only API witness assembly/contract registration remains.

   This makes the required update concrete while preserving historical records.
   No Lean fix is requested. R41D/COMPARISON.md:90 already records both instances.

2. Remaining registration work is honestly separated at REPORT_229.md:42.
   Ran `grep -rnE 'RCritical2API|RMainAPI|densityFixedInitial|densityZero|rcritical2_endpoint_unconditional' formalization/NSFormalization/Section4`
   over the entire tree: matches are the endpoint skeleton, these implementations,
   and API comments; no complete API witness or density implementation appears.
   Also `rg -n 'R44|RCritical2' verification/contracts.json` returns no match.
   No missing analytic lemma is asserted by this worker report. The historical
   missing TrilinearJ episode in ATTEMPTS_PROP44.md:27 is not a current gap:
   TrilinearJ.lean:416/:563 exists and matches integration. No claim is made here
   that the radius mutation is mathematically false; it tests proof sensitivity.

3. Negative check: research/R44/probes/rev229_radius.lean:10 doubles the main
   statement’s admissible radius, retaining every binder and the original proof.
   Lean rejects the final application at :14 with the precise changed-threshold
   mismatch below. This is a substantive widening, not a dropped argument.

## 4. Commands and results

All Lean invocations sourced `. scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, and ran Lake serially from verification/.
No git mutation or edits to lane sources/records were made.
Only this review and the permitted negative probe were created.

Build command:
```sh
cd verification
LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R44.Absorption NSFormalization.Section4.R44.Prop44 NSFormalization.Section4.R41.NonDensityL2
```
Exit 0. No diagnostic originates in any of the three new modules.
Aggregate output is not silent: existing dependency diagnostics are replayed.
Exact beginning and ending excerpts (middle omitted):
```text
⚠ [8781/9288] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply
[middle omitted]
Build completed successfully (10553 jobs).
```

Direct module checks and both audits, exact captured output (COMMAND/EXIT/BYTES
are the review harness’s metadata; blank module output is genuinely zero bytes):
```text
COMMAND: lake env lean ../formalization/NSFormalization/Section4/R44/Absorption.lean EXIT: 0 BYTES: 0

COMMAND: lake env lean ../formalization/NSFormalization/Section4/R44/Prop44.lean EXIT: 0 BYTES: 0

COMMAND: lake env lean ../formalization/NSFormalization/Section4/R41/NonDensityL2.lean EXIT: 0 BYTES: 0

COMMAND: lake env lean ../research/R44/axioms_prop44.lean EXIT: 0 BYTES: 6273
'NSFormalization.Section4.R44.advectionJDatumPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.energyAdvectionJPairing_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.energyAdvectionJPairing_path_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.thetaAbs' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.C₂Abs' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.C₃Abs' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.thetaAbs_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.trilinear_theta' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.C₂Abs_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.C₂Abs_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.C₃Abs_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.C₃Abs_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.rcritical2EnergyDerivative' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.rcritical2EnergyDerivative_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.rcritical2EnergyDerivative_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.young_absorption' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.rcritical2_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.smoothRcritical2EnergyDerivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.smoothRcritical2EnergyDerivative_continuousOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.rcritical2EnergyDerivative_eq_smooth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.rcritical2EnergyDerivative_intervalIntegrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.rcritical2_differential' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.theta_le_thetaAbs' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.rCritical2Differential_of_classical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.rcritical2Differential_of_classical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.rcritical2_endpoint_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.nonDensityBallZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.zero_force_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'Prop44Conformance.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'Prop44Conformance.nonDensityBallZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Prop44Conformance.radiusFormula' depends on axioms: [propext, Classical.choice, Quot.sound]
'Prop44Conformance.radiusPos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radiusCoefficient_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radiusRate_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.halfHomogeneousComponent' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.halfHomogeneousDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.halfHomogeneousDatum_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.halfHomogeneousDatum_isDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.inhomogeneousCriticalL3' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.halfDatumCyclesComponent' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.halfDatumPhysicalComponent' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.halfDatumPhysicalComponent_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.halfDatumPhysicalLp' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.halfDatumPhysicalField' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.halfDatumPhysicalField_memLp' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.halfDatumPhysicalField_isDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.inhomogeneous_half_order_parseval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.advectionFieldJ' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.AdvectionJDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.advectionJPairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.advectionJHolder' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.trilinearConstJ' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.trilinearConstJ_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.advection_pairing_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.advection_pairing_le' depends on axioms: [propext, Classical.choice, Quot.sound]

COMMAND: lake env lean ../research/R41D/axioms_nondensity_l2.lean EXIT: 0 BYTES: 2069
'NSFormalization.Section4.R41.angularOrderLowering_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.lowerVectorL_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.forceSobolevENorm_mono_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.forceClassR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.breakdownSetIn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.breakdownSetR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.breakdownSetRZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.RelativelyDense' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.BreakdownDenseR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.radius_le_forceSobolevENorm_L2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.nonDensityZero_L2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.zero_mem_forceClassR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.not_breakdownDenseR_zero_L2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityL2Conformance.breakdownSetIn_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityL2Conformance.breakdownSetR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityL2Conformance.breakdownSetRZero_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityL2Conformance.BreakdownDenseR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityL2Conformance.nonDensityZero_L2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityL2Conformance.not_breakdownDenseR_zero_L2' depends on axioms: [propext, Classical.choice, Quot.sound]


```

Every axiom list is exactly [propext, Classical.choice, Quot.sound], including
lists formatted by Lean over multiple lines: 56+19=75 reports.

`make check`, exit 0; exact first/last 40 lines, with harness metadata:
```text
EXIT: 0 LINES: 30031
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 546,
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
  "registered_contracts": 30,
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
[middle omitted]
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
      "Tests.CriticalRegularity"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
.............
----------------------------------------------------------------------
Ran 13 tests in 0.043s

OK

```
The copied-source admission/source-hash diagnostics above are existing
repository-wide informational output, not failures in this import closure;
the transitive axiom audits pass.

`lake env lean ../research/R44/probes/rev229_radius.lean`, expected exit 1:
```text
../research/R44/probes/rev229_radius.lean:14:48: error: Application type mismatch: The argument
  hsmall
has type
  forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (2 * radius ν S)
but is expected to have type
  forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν S)
in the application
  rcritical2_endpoint_of_differential ν S hν hS f hf (rCritical2Differential_of_classical hν hf) hsmall

```

`git diff --name-only origin/erenup/integration...HEAD`, exact output:
```text
formalization/NSFormalization/Section4/R41/NonDensityL2.lean
formalization/NSFormalization/Section4/R44/Absorption.lean
formalization/NSFormalization/Section4/R44/Prop44.lean
research/R41D/COMPARISON.md
research/R41D/axioms_nondensity_l2.lean
research/R44/ATTEMPTS_PROP44.md
research/R44/REPORT_229.md
research/R44/axioms_prop44.lean
```
`git diff --check`: exit 0, no output.
`git diff --name-only origin/erenup/integration...HEAD -- verification`:
exit 0, no output. Consequently scripts/gates.sh and the explicit
check_contracts.py --base-ref origin/erenup/integration gate are not triggered
by the brief’s verification-touch condition and were not rerun.
The worker’s extra lake-test/mutation claims are not independently rerun here.

`rg -n 'sorry|admit|\\baxiom\\b|native_decide|maxHeartbeats'` on the three
delivered modules: no matches (exit 1).
`git diff --quiet erenup/227-R44-endpoint -- formalization/NSFormalization/Section4/R44/Endpoint.lean`:
exit 0, no output. Integration comparisons for Endpoint and TrilinearJ likewise
have no output. Review leaves all tracked content unchanged except this new report.

