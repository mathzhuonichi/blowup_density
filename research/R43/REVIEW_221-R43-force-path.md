ACCEPT-WITH-NOTES

## 1. What the lane claims

Reviewed commit `9781203` on `erenup/221-R43-force-path`, against the original brief in the review request and its continuation addendum. The on-disk `collaboration/briefs/221-R43-force-path.md` is absent; the supplied brief was used. Read CLAUDE.md, the lane-review skill, the top 40 LESSONS lines, the handoff, and reports 216/219/221.

`research/R43/REPORT_221.md:5` claims exact G2 domination and G3 finiteness, identification/continuity/integrability of the force norm, and the primitive's continuity, interior FTC and monotonicity. Its zero-datum bootstrap statement at :12 accurately includes positive viscosity, force membership, `0 ≤ S < T`, `0 ≤ c < 1/(2*trilinearConst)`, and prefix smallness. Its scope disclaimer at :38 does not claim the full global-regularity proposition.

Opened with sed the manuscript `paper/sections/04-whole-space.tex:81`–105 and :125–132: b is the homogeneous half-order force norm; the energy inequality has the correct minus sign and factor 1/2; regularized integration gives the prefix bound; :132 gives the inhomogeneous comparison. The manuscript's smaller radius 1/(4C₀) is compatible with the scalar supplier's sufficient bound 1/(2C₀); the later absorption step is outside this theorem.

## 2. What is in Lean

All 25 claimed declarations exist; the audit contains exactly 25 corresponding print commands (`research/R43/axioms_force_path.lean:10`–34). Here and below ForcePath means `formalization/NSFormalization/Section4/R43/ForcePath.lean`.

- G2 is literally the requested inequality at ForcePath:67. The unused `_hf` at :68 is honest: the comparison holds for arbitrary forces by transporting every admissible path. Measurability is separately transported at :74, and the pointwise contraction at :42 controls the eLpNorm at :84.
- G3 is the exact non-top statement at :88. Its finite upper bound is `Section4/D01/HalfOrder.lean:178`. The canonical path is identified at :99, continuous at :109, homogeneous at :119, MemLp 1 at :125, and AE strongly measurable at :138. The positive-time measure and path infimum agree with `Section4/D01/HomogeneousWitness.lean:615,622,627` and `verification/Contracts/V1/Data.lean:375,390`; there is no replacement norm definition.
- Identification is at :145; continuity on the future half-line, Icc and Ico at :151,159,165; nonnegativity and interval integrability at :171,176. The source `Section4/R43/CriticalPairing.lean:59,63,87` identifies the infimum with the finite norm of an actual datum, so this is not an exploitation of top.toReal = 0.
- The actual interval integral is defined at :186. Continuity, FTC, initial value and monotonicity are at :190,201,215,221. Prefix comparison with the global homogeneous norm is at :231, and the real-valued inhomogeneous comparison at :258 explicitly supplies finiteness before using toReal_mono (:265–273).
- Zero-field reductions are at :278,283. The bootstrap at :292 has exactly the reported statement. Its proof applies `Section4/R43/CriticalMomentum.lean:334` and `Section4/R43/Pieces.lean:145` at :322 and :340. The clamped extension is only an auxiliary scalar function; local equality transfers derivatives on Ioo (:328), and the conclusion returns to the original velocity (:347).
- Supplier statements were opened and checked: `Paper1/ScalarEnergy.lean:147` (critical_norm_bound), `Section4/C01/EnergyBounds.lean:180` (sqrt_energy_le_primitive'), and Pieces:145 have exactly the primitive continuity/zero/FTC/nonnegativity shapes provided here. No extra analytic hypothesis or contradictory named input was added.
- The worker's zero and nonzero compact bump instances compile (`research/R43/axioms_force_path.lean:37,46`); the latter is nonzero at (2,0), not merely nonzero at a negative time (:82–91). The cited source `research/A01/probes/memForceR_bump_witness.lean:30,71` exists. An additional reviewer instance `research/R43/probes/rev221_nonvacuity.lean:7` applies the bootstrap with ν=1, T=2, S=1, c=0 and the zero solution, ruling out reliance on the worker probe's degenerate interval.
- Hygiene: no forbidden proof tokens or heartbeat override in ForcePath. The inherited CriticalMomentum override at :279 is declaration-local, 400000, and explained at :277. No existing Lean module is modified. The triple-dot diff includes new modules from parent lanes 216/219 as well as 221; the sole modified tracked file is the authorized research split. The last commit adds only ForcePath and its lane records/probe, plus the split update.
- `experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run` selects ForcePath, so it is covered by changed-module CI even though no new contract is registered.

## 3. Gaps and exact fixes

1. **Low severity, documentation only:** ForcePath:56–57 says “Every inhomogeneous datum path ... has a measurable homogeneous image path.” The theorem at :58 assumes only IsSobolevPath and concludes only IsHomogeneousPath; neither predicate contains measurability. The actual measurable-path proof is correctly separate at :74. **Exact one-line fix:** replace the docstring at :56–57 with `/-- Every inhomogeneous datum path of nonnegative order has a homogeneous image path for the same physical force. -/`. Do not change the theorem.

No mathematical blocker was found. Unused `_hS` in continuity at :160 simply permits the stronger empty-interval case; interval integrability, primitive comparisons and the bootstrap carry the appropriate endpoint guards.

The negative search was performed with `grep -rnE 'sqrt_energy_le_primitive|critical_norm_bound|continuous_bootstrap|critical_bootstrap|lifespanInfiniteOfLocallyFinite|maximal_h2TimeIntegral' formalization/NSFormalization/Section4`, plus whole-tree endpoint/continuation searches. It finds `R43/MaximalEndpoint.lean:15,38` (endpoint gluing conditional on absorption), `A04/Continuation.lean:223` (continuation conditional on Restart and HigherOrderBound), and `C01/EnergyBounds.lean:180` (general initial-energy scalar comparison). Thus these ingredients must not be described as absent. REPORT_221:41–43 says their assembly is separate, which is accurate. The apparent G5-open row at `research/R43/R43_SPLIT.md:228` is explicitly superseded by that file's opening update at :3–17. No correction to that historical row is required for this lane.

The substantive mutation copies the entire FTC proof, retains all hypotheses, and changes its derivative to `criticalForceAt f t + 1` (`research/R43/probes/rev221_mutation.lean:7`). It fails at the FTC application (:15), with the precise expected derivative mismatch below. This is not a missing-argument test.

## 4. Commands and results

All lake commands ran from verification after sourcing scripts/lean-env.sh, with LEAN_NUM_THREADS=6, one lake process at a time. No git mutation, implementation edit, or existing-record edit was made. Reviewer additions are this report and the two rev221 probes.

The conditional verification-change gates (`scripts/gates.sh` and `check_contracts.py --base-ref origin/erenup/integration`) were not required: neither triple-dot diff nor the lane commit changes verification/. The direct build, Lean, make check, lake test and make test-mutations gates were run. Large outputs below are exact head/tail excerpts, with omissions labelled.

### Target build — exit 0

`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R43.ForcePath`

No diagnostic comes from ForcePath; dependency diagnostics are replayed, as the worker reported. Exact first/last 40 lines:

```text
⚠ [8777/9231] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [insert, coord]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9866/10536] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9867/10536] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10264/10536] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:30: Variable name `hB` is not explicitly referenced.
[... dependency output omitted ...]
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10512/10536] Replayed NSFormalization.Source.RieszL2Fourier
warning: NSFormalization/Source/RieszL2Fourier.lean:31:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [10513/10536] Replayed NSFormalization.Source.FractionalRealization
warning: NSFormalization/Source/FractionalRealization.lean:60:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: NSFormalization/Source/FractionalRealization.lean:83:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: NSFormalization/Source/FractionalRealization.lean:104:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
Build completed successfully (10536 jobs).

```

### Direct checks

`lake env lean ../formalization/NSFormalization/Section4/R43/ForcePath.lean`: exit 0, stdout/stderr exactly empty.

`lake env lean ../research/R43/probes/lane221_s2_wiring.lean`: exit 0, stdout/stderr exactly empty.

`lake env lean ../research/R43/probes/rev221_nonvacuity.lean`: exit 0, stdout/stderr exactly empty. An initial reviewer-only probe had a function-zero simplification mismatch; explicitly typing the zero spatial field repaired it, without touching lane code.

`lake env lean ../research/R43/axioms_force_path.lean`: exit 0. Full exact output:

```text
'NSFormalization.Section4.R43.ofSobolevVector_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.isHomogeneousPath_of_isSobolevPath' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.forceHomogeneousENorm_le_forceSobolevENormL1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.forceHomogeneousENorm_one_half_ne_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.criticalForceHalf_eq_of_orderOnePath' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.criticalForceHalf_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalForceHalf_isHomogeneousPath' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.criticalForceHalf_memLp_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalForceHalf_aestronglyMeasurable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.criticalForceAt_eq_norm_criticalForceHalf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.criticalForceAt_continuousOn_future' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.criticalForceAt_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalForceAt_continuousOn_Ico' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.criticalForceAt_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalForceAt_intervalIntegrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.criticalForcePrimitive' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalForcePrimitive_continuousOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.criticalForcePrimitive_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.criticalForcePrimitive_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalForcePrimitive_monotoneOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.criticalForcePrimitive_le_forceHomogeneousENorm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.criticalForcePrimitive_le_forceSobolevENormL1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.zero_dotHomogeneousENorm_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.zero_mem_initialClassR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.critical_bootstrap_zero_datum' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Negative mutation — exit 1, expected

`lake env lean ../research/R43/probes/rev221_mutation.lean`

```text
../research/R43/probes/rev221_mutation.lean:15:2: error: Type mismatch
  intervalIntegral.integral_hasDerivAt_right hint
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (ContinuousOn.mono (criticalForceAt_continuousOn hf hS) Ioo_subset_Icc_self) t ht)
    hcont
has type
  HasDerivAt (fun u => ∫ (x : ℝ) in 0..u, criticalForceAt f x) (criticalForceAt f t) t
but is expected to have type
  HasDerivAt (criticalForcePrimitive f) (criticalForceAt f t + 1) t
```

### make check — exit 0

Captured stdout followed by stderr, first/last 40 lines:

```text
exit: 0 lines: 28234
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 534,
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
  "registered_contracts": 29,
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
      "Tests.GradientL6V2"
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
Ran 13 tests in 0.050s

OK
```

The copied-source admission notice and source_hashes_match=false are pre-existing architecture notices, not ForcePath dependencies introducing extra axioms; the transitive declaration audit above is clean.

### Registered tests and harness mutations

`cd verification && LEAN_NUM_THREADS=6 lake test`: exit 0. Dependency warnings and successful standard-axiom contract checks were printed, including:

```text
info: Tests/EnergyAbsorptionV4.lean:18:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionV4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
```

`LEAN_NUM_THREADS=6 make test-mutations`: exit 0, exact captured excerpts:

```text
exit: 0
python3 experiments/test_contract_mutations.py
⚠ [8778/8927] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]
[... dependency replay omitted ...]
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
ℹ [10572/10573] Replayed Tests.TameProduct
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
ℹ [10573/10573] Replayed Tests.EnergyAbsorptionV4
info: Tests/EnergyAbsorptionV4.lean:18:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionV4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

`rg -n 'sorry|admit|\\baxiom\\b|native_decide|maxHeartbeats' formalization/NSFormalization/Section4/R43/ForcePath.lean`: no output (no matches).
`git diff --check`: exit 0, no output.

`git diff --name-only origin/erenup/integration...HEAD`:

```text
formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean
formalization/NSFormalization/Section4/R43/CriticalMomentum.lean
formalization/NSFormalization/Section4/R43/ForcePath.lean
research/R43/ATTEMPTS_CRITICAL_DATUM.md
research/R43/ATTEMPTS_CRITICAL_MOMENTUM.md
research/R43/ATTEMPTS_FORCE_PATH.md
research/R43/R43_SPLIT.md
research/R43/REPORT_216.md
research/R43/REPORT_219.md
research/R43/REPORT_221.md
research/R43/axioms_critical_datum.lean
research/R43/axioms_critical_momentum.lean
research/R43/axioms_force_path.lean
research/R43/probes/lane221_s2_wiring.lean
```

Fix list: the single docstring replacement in finding 1; no proof or statement changes.

