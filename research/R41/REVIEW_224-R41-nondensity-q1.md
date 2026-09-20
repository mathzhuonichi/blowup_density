ACCEPT

## 1. What the lane claims

Reviewed commit `fd0c87a9952e29ddf5591e9289976da36d4e7667`, lane 224 only, with its inherited lane-223 endpoint dependency. Read CLAUDE.md, the lane-review skill, the top 40 lines of logs/LESSONS.md, HANDOFF §0/§2 P10, the supplied brief, the fallback worker message, and the actual report at `research/R41D/REPORT_224.md` (the requested `research/R41/REPORT_224.md` does not exist).

The claim at `research/R41D/REPORT_224.md:5` is exactly the q=1 non-density direction of Theorem 4.1(ii): for ν,T>0 and s≥1/2, an excluded relative ball centred at zero has radius `R43.criticalConst * ν`. The report separately claims general order monotonicity (`:19`), 19 standard-axiom audits (`:22`), and no remaining premise (`:31`).

Read the paper using `sed -n '8,12p;176,181p' paper/sections/04-whole-space.tex`: `:8` gives s_q=2/q−3/2, `:11` is the zero-datum equivalence, and `:179` explicitly uses the critical q=1 ball and constant-one inclusion H^s→H^(1/2). This matches `research/section4/STATEMENTS.md:128` and the proposed `RMainAPI.nonDensityZero` at `:160`. No subcritical density, q=2 conclusion, or full API witness is claimed.

## 2. What is in Lean

All line references in the following inventory refer to `formalization/NSFormalization/Section4/R41/NonDensityL1.lean`.

| Declarations | Location | Verified statement |
|---|---|---|
| angularOrderLowering_norm_le | :16 | For all real r≤s and Fourier data v, lowering has norm ≤‖v‖. |
| lowerVectorL_norm_le | :30 | The corresponding real vector lowering has constant-one norm bound. |
| forceSobolevENorm_mono_order | :42 | For every q:ℝ≥0∞, s≤s′, and physical force f, norm(q,s,f)≤norm(q,s′,f); no force-class or finiteness premise. |
| forceClassR | :58 | Exact Data definition at :553. |
| breakdownSetIn | :61 | Exact Data definition at :672; membership in Y and maximal lifespan ≤ofReal T. |
| breakdownSetR | :66 | Exact Data definition at :678. |
| breakdownSetRZero | :70 | Exact Data definition at :686, with zero initial field. |
| RelativelyDense | :74 | Exact Data definition at :702; every ambient g and every positive ENNReal radius. |
| BreakdownDenseR | :78 | Exact Data definition at :707. |
| criticalRadius_le_forceSobolevENorm | :82 | Explicit radius lower bound, assuming ν>0, s≥1/2, and breakdown membership. |
| nonDensityZero_L1 | :93 | Exact requested quantifier order and existential positive real radius; witness is criticalConst*ν. |
| zero_mem_forceClassR | :101 | Zero belongs to the ambient force class. |
| not_breakdownDenseR_zero_L1 | :105 | Exact requested negation, for all ν,T>0 and s≥1/2. |

The six definitions are exact text matches, including their full bodies, against `verification/Contracts/V1/Data.lean:553,672,678,686,702,707`. They use the existing D01 norm (`D01/HalfOrder.lean:141`), not another norm copy. `research/R41D/axioms_nondensity_l1.lean:23` and `:38` check force-class and relative-density equality by rfl; `:25,30,34,40` bridge all lifespan-dependent definitions through the existing `verification/Bindings/MaximalPartial.lean:130` equality. Distinct solution structures explain why these four bridges use that equality instead of rfl. The two conformance theorems at `:51` and `:57` verify the final conclusions in literal Data vocabulary.

Analytic proof checked against the actual tree:
- `D01/LaplacianPairing.lean:138,146` factors angular lowering through the unitary dilation and identifies its multiplier.
- `D01/RealPairing.lean:114` simplifies that multiplier to the Bessel weight of r−s; `Paper3/SobolevOrderLowering.lean:13` bounds its norm by one for nonpositive order. This justifies NonDensityL1:18–27.
- `D01/HalfOrder.lean:103,120` supplies the continuous linear lowering and preservation of every slice-datum clause. NonDensityL1:44–55 maps each higher-order admissible path, preserves strong measurability, and uses eLpNorm monotonicity before taking infima. The same construction pattern is visible at `R43/ForcePath.lean:58,67`. Admissibility requires measurability, not a separate MemLp premise.
- `R43/Endpoint.lean:17,22,134` supplies the explicit positive critical constant and unconditional global-lifespan theorem. NonDensityL1:85–90 contradicts finite `ofReal T` when a breakdown force is too small, then transfers the lower bound by order monotonicity.

No toReal operation occurs in this module. The time measure is the actual positive half-line (`D01/ForceClass.lean:147`), with slice conditions for all nonnegative times (`:152`), not an empty interval. In particular, absent paths correctly yield top and do not make the smallness condition true. Finite half-order norm for ambient forces is also independently available at `D01/HalfOrder.lean:178`.

The positive-T binder at NonDensityL1:93 is intentionally unused at :96: the explicit bound at :82 is stronger and holds for every real T because ofReal T is finite. This does not create vacuity or hide a new assumption. There are no named unresolved analytic hypotheses. The threshold comment at :4 agrees with `verification/Contracts/V1/Thresholds.lean:14,18`; `research/R41D/Spec.lean:20` explicitly uses literal thresholds, so the optional exponent-record restatement is not required.

Non-vacuity: NonDensityL1:114–117 and the conformance file:65–67 check the ambient centre and ν=T=1, s=1/2. The reviewer probe independently includes those controls and the numerical premise conjunction at `research/R41/probes/rev224_widen_threshold.lean:9`. No existence of a breakdown force is needed to establish non-density.

## 3. Gaps and hygiene

No blocking findings; required fixes: none.

1. The clause is fully proved. `research/R41D/REPORT_224.md:31` declares no missing lemma; its q=2 and subcritical exclusions are scope statements, not claims of tree-wide nonexistence. The old subcritical gap table in COMPARISON.md is explicitly outside this lane (`COMPARISON_NONDENSITY_L1.md:9`).
2. Checked the actual negative existence claim at `research/R41D/ATTEMPTS_NONDENSITY_L1.md:43` with `grep -rnE 'breakdownSetR|RelativelyDense' formalization/NSFormalization/Section4`. Every hit is in the new NonDensityL1 module (:66,70,71,74,79,83,94); no earlier copy exists. A second whole-tree search for all six definition names likewise finds only this module. The reused D01 norm was located at HalfOrder:141. The stated coarse-bound limitation of the rejected route is confirmed by `A03/RealAngularProduct.lean:198`.
3. Forbidden-token/heartbeat scan of the authored module and conformance file has zero output. The seven new Lean modules in the three-dot inherited diff contain no forbidden proof tokens; the only heartbeat override in that wider dependency set is `R43/CriticalMomentum.lean:279`, per declaration, 400000, explained by its preceding comment.
4. The three-dot diff against origin/erenup/integration has no modifications to existing formalization modules and no verification changes. It includes inherited R43 records modified by earlier lanes. Lane 224 itself (`git diff --name-status HEAD^ HEAD`) adds exactly five files and modifies none. The report's new-files claim is correct for this lane.
5. Supplying `research/R41D/COMPARISON_NONDENSITY_L1.md:1` instead of editing COMPARISON.md is a reasonable resolution of the brief's conflict with its strict new-files rule; the worker explicitly discloses it at REPORT_224:36.
6. The direct module build is warning-free for this module, although Lake replays warnings from dependencies (correctly disclosed at REPORT_224:46). Direct Lean output is exactly empty.
7. No contract registration is claimed. CI's changed-module job covers this new module: `.github/workflows/contracts.yml:77`, `experiments/build_changed_lean.py:18,32`; the dry run selects NonDensityL1.

Substantive negative test: copied the entire proof of the explicit-radius theorem, retained every argument, and widened its order range from s≥1/2 to s≥0. It fails at the expected monotonicity input (`research/R41/probes/rev224_widen_threshold.lean:23`), with no unrelated errors. This tests the threshold's role in this proof; it is not a proof that every widened formulation is false.

## 4. Commands and results

All explicit Lean commands used `. scripts/lean-env.sh`, ran lake from verification/, and set LEAN_NUM_THREADS=6. The package path was already a valid shared symlink; no installer or git mutation was needed. Required gates all passed. No verification/ files were touched, so the conditional scripts/gates.sh gate is inapplicable; its substantive test and mutation components and the base-compatibility check were also run separately.

Long outputs below use exact head/tail excerpts (at most 40 lines each), following logs/LESSONS.md:4; omitted interiors are explicitly marked.

### Module build

`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R41.NonDensityL1`: exit 0. Exact first/last 40 lines:

```text
⚠ [8777/9105] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9866/10545] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9867/10545] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10264/10545] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:30: Variable name `hB` is not explicitly referenced.
[interior omitted]
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10512/10545] Replayed NSFormalization.Source.RieszL2Fourier
warning: NSFormalization/Source/RieszL2Fourier.lean:31:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [10513/10545] Replayed NSFormalization.Source.FractionalRealization
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
Build completed successfully (10545 jobs).

```

### Direct module and axioms

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/R41/NonDensityL1.lean`: exit 0, 0 bytes of output.

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R41D/axioms_nondensity_l1.lean`: exit 0, complete output:

```text
'NSFormalization.Section4.R41.angularOrderLowering_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.lowerVectorL_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.forceSobolevENorm_mono_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.forceClassR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.breakdownSetIn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.breakdownSetR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.breakdownSetRZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.RelativelyDense' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.BreakdownDenseR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.criticalRadius_le_forceSobolevENorm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R41.nonDensityZero_L1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.zero_mem_forceClassR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.not_breakdownDenseR_zero_L1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityConformance.breakdownSetIn_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityConformance.breakdownSetR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityConformance.breakdownSetRZero_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityConformance.BreakdownDenseR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityConformance.nonDensityZero_L1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NonDensityConformance.not_breakdownDenseR_zero_L1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Architecture/policy gate

`make check`: exit 0, 28234 output lines, 1159606 bytes. Captured first/last 40 lines:

```text
exit: 0 lines: 28234 bytes: 1159606
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 538,
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
      "Tests.GradientL6V2"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

The copied umbrella's BoundaryCorollary sorry and source-hash diagnostic in this global output are pre-existing scan findings, not reachable axioms in this lane; the lane's exact axiom audit above passes.

### Additional registered tests and compatibility

`cd verification && LEAN_NUM_THREADS=6 lake test`: exit 0; exact trailing lines:

```text
ℹ [10559/10573] Replayed Tests.Uniqueness
info: Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only
ℹ [10560/10573] Replayed Tests.HomogeneousNorm
info: Tests/HomogeneousNorm.lean:17:0: Contract BlowupDensity.Tests.checkedHomogeneousNorm: checked; standard logical axioms only
ℹ [10565/10573] Replayed Tests.HomogeneousPartialV2
info: Tests/HomogeneousPartialV2.lean:35:0: Contract BlowupDensity.Tests.checkedHomogeneousPartialV2: checked; standard logical axioms only
ℹ [10568/10573] Replayed Tests.MaximalPartialV2
info: Tests/MaximalPartialV2.lean:24:0: Contract BlowupDensity.Tests.checkedMaximalPartialV2: checked; standard logical axioms only
ℹ [10571/10573] Replayed Tests.InsertionLifespanV2
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
ℹ [10572/10573] Replayed Tests.TameProduct
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
ℹ [10573/10573] Replayed Tests.EnergyAbsorptionV4
info: Tests/EnergyAbsorptionV4.lean:18:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionV4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
```

`make test-mutations`: exit 0; after its dependency/test replay, the complete result summary is:

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`: exit 0; exact excerpts:

```text
exit: 0 lines: 28202
{
  "registered_contracts": 29,
  "closures": {
    "R41.threshold_arithmetic": [
      "Bindings.Thresholds",
      "Contracts.V1.Thresholds",
      "NSFormalization.Paper3.Thresholds",
      "TestSupport.Axioms",
[middle omitted]
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.GradientL6V2"
    ]
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

### Reviewer mutation

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R41/probes/rev224_widen_threshold.lean`: expected exit 1, complete output:

```text
../research/R41/probes/rev224_widen_threshold.lean:23:62: error: Application type mismatch: The argument
  hs
has type
  0 ≤ s
but is expected to have type
  1 / 2 ≤ s
in the application
  forceSobolevENorm_mono_order 1 (1 / 2) s hs
```

### Text, scope, and CI checks

Definition comparison extracted each complete `def` declaration and compared raw text against Data:

```text
forceClassR: exact text match
breakdownSetIn: exact text match
breakdownSetR: exact text match
breakdownSetRZero: exact text match
RelativelyDense: exact text match
BreakdownDenseR: exact text match
```

`python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run`: exit 0:

```text
Changed Lean modules: NSFormalization.Section4.R41.NonDensityL1
```

`git diff --check origin/erenup/integration...HEAD`: exit 0, empty output.
`git diff --name-only origin/erenup/integration...HEAD -- verification/`: empty output.
`git diff --name-only --diff-filter=M origin/erenup/integration...HEAD -- formalization/`: empty output.
`rg -n '\\b(sorry|admit|axiom|native_decide)\\b|maxHeartbeats' formalization/NSFormalization/Section4/R41/NonDensityL1.lean research/R41D/axioms_nondensity_l1.lean`: no matches.

`git diff --name-only origin/erenup/integration...HEAD`: exact output:

```text
formalization/NSFormalization/Section4/A04/RestartFixedForce.lean
formalization/NSFormalization/Section4/A04/ShiftedExtension.lean
formalization/NSFormalization/Section4/R41/NonDensityL1.lean
formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean
formalization/NSFormalization/Section4/R43/CriticalMomentum.lean
formalization/NSFormalization/Section4/R43/Endpoint.lean
formalization/NSFormalization/Section4/R43/ForcePath.lean
research/R41D/ATTEMPTS_NONDENSITY_L1.md
research/R41D/COMPARISON_NONDENSITY_L1.md
research/R41D/REPORT_224.md
research/R41D/axioms_nondensity_l1.lean
research/R43/ATTEMPTS_CRITICAL_DATUM.md
research/R43/ATTEMPTS_CRITICAL_MOMENTUM.md
research/R43/ATTEMPTS_ENDPOINT.md
research/R43/ATTEMPTS_FORCE_PATH.md
research/R43/COMPARISON.md
research/R43/R43_SPLIT.md
research/R43/REPORT_216.md
research/R43/REPORT_219.md
research/R43/REPORT_221.md
research/R43/REPORT_223.md
research/R43/axioms_critical_datum.lean
research/R43/axioms_critical_momentum.lean
research/R43/axioms_endpoint.lean
research/R43/axioms_force_path.lean
research/R43/probes/lane221_s2_wiring.lean
```

Reviewer changes are limited to this new report and the permitted rev224_*.lean probe. No tracked lane file or git state was changed.

Required fixes: none.

