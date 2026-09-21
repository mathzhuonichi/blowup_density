REJECT

## 1. What the lane claims

Reviewed HEAD `824cf4daee6a55c979dfcf1f49c3640caa8928a8` against the requested brief and the local `origin/erenup/integration` reference `ddaa5b9d02e57ee5e1bd34fe5993393ca93e1c09`. The rejection is for the required integration gate, not a discovered false Lean theorem.

`research/R47/REPORT_251.md:5` claims unconditional velocity cell means on `[0,T)`; `:10` explicitly makes the force result conditional; `:18` claims the interior temporal mean and subtraction of momentum equations; `:24` identifies the additional original reference-force regularity assumption. These claims agree with the source. The brief explicitly permits one isolated, satisfiable analytic hypothesis; I do not reject the lane for using that allowance.

The paper was opened with `sed -n '297,330p' paper/sections/04-whole-space.tex`: `:308` gives the solenoidal velocity mean, `:314` begins eq:gridforce, and `:320` cancels the temporal mean and boundary flux. The relevant spec is `research/R47/Spec.lean:101` and `:109`, both on `[0,T)`. The lane supplies per-grid consequences, not the full existence/choice record; this limitation is stated at `REPORT_251.md:25`.

## 2. What is in Lean

All fourteen declarations exist in namespace `BlowupDensity.Bindings`, in `verification/Bindings/ForceCellIntegral.lean`. Exact statement audit:

| Declaration (line) | Checked conclusion and hypotheses |
| --- | --- |
| insertion_reference_smooth (25) | Reference velocity smooth on the insertion slab; the reference margin supplies the restriction. |
| velocityDifference_slice_smooth (34) | Smooth spatial difference for admissible ε and t in Ico. |
| velocityDifference_slice_compact (41) | Compact support of that slice, using the fixed closed ball. |
| velocityDifference_cell_integral_zero_component (48) | Each component integral is 0, assuming only the R42 record, admissible ε/t, and ball containment in the specified grid cell. |
| velocityDifference_cell_integral_zero (62) | Same vector integral is 0, with exactly those hypotheses. |
| insertion_momentum_difference (75) | Residual(uε,pε) − Residual(v,π) = forceε − g on Ioo; no false linearization of convection. |
| forceDifference_initial_zero (89) | forceε(0,x) − g(0,x) = 0 for every x and admissible ε. |
| velocityDifference_timeDerivative_integral_zero (96) | Whole-space integral of the vector time derivative is 0 for t in Ioo. |
| forceDifference_cell_integral_zero (145) | Force cell integral is 0 on Ico, conditional on the single displayed hcompactMomentumIntegral. |
| continuous_integrableOn_grid_cell (163) | Every continuous spatial field is integrable on any grid cell. |
| forceDifference_slice_support (175) | Force-difference slice support lies in the ball, at every real time. |
| velocity_gridObservation_eq (183) | Full gridObservation function equality on Ico, with ball containment. |
| force_gridObservation_eq (204) | Same for force, with hcompactMomentumIntegral and hg : MemForceR A.g. |
| force_gridObservation_initial_eq (234) | Initial force observations equal for every grid, with neither containment nor the analytic hypothesis. |

The R42 inputs are the existing fields in `verification/Contracts/V1/InsertionFamily.lean:146` (reference), `:196` (velocity regularity), `:219` (momentum), `:231` (velocity support), `:241` (difference divergence), `:255` (pressure support), and `:265` / `:270` (compact force/support); see the exact field identifiers in those neighborhoods. The actual residual subtraction is `ForceCellIntegral.lean:81`, using A.momentum and A.reference.momentum plus reference_velocity/reference_pressure.

Opened and checked the cited tree lemmas: `Paper3/CompactObservations.lean:33` requires smoothness, compact support, divergence zero, measurable cell, and support containment; all are supplied at `ForceCellIntegral.lean:52`. `Paper3/TimeObservations.lean:15` requires a compact common support on a closed time window and a genuine pointwise derivative; the window and derivative are supplied at `ForceCellIntegral.lean:105` and `:113`. The vector conversion uses integrability at `:67`. The temporal proof's `integral_undef` branch at `:136` is not an extra hypothesis or evidence that the actual field is nonintegrable: smoothness on a compact interior window and fixed spatial support give a genuinely integrable derivative. The component theorem already performs differentiation under the integral.

`verification/Bindings/GridLemmas.lean:49` really requires separate integrability of both fields and the zero vector integral. Calls at `ForceCellIntegral.lean:196` and `:226` supply them, rather than trying to infer zero mean merely from support. `Data.lean:774` defines the actual vector cell average, and `:784` the complete grid observation. Cells have positive mesh widths and bounded half-open coordinate intervals (`Paper3/GridGeometry.lean:15`, `:81`); these are not empty intervals or infinite-volume normalization tricks.

The audit's four examples (`research/R47/axioms_force_cell_integral.lean:28,38,44,49`) compile. In particular, ε = A.ε₀ and t = A.T/2 inhabit the positive ranges. They are conditional on an actual R42 record and, where needed, a containing cell; they do not construct a witness of the open flux input, and the report does not claim that they do. The nonzero constant-field integrability example is universally quantified in c. No extra non-vacuity probe was required by the review brief because the report already contains these examples.

Hygiene: no sorry/admit/axiom/native_decide declarations or maxHeartbeats settings in the new module/audit; all fourteen axiom prints are exactly the standard three. The three-dot diff contains only four additions, no changes to existing modules. The module is covered by the Bindings glob (`verification/lakefile.toml:15`) and the changed-module target mapping (`experiments/build_changed_lean.py:10`). No Lean source or lane records were edited by this reviewer; the only added files are this report and the permitted negative probe.

## 3. Gaps and findings

1. **Blocking — required integration compatibility gate fails.** Both `scripts/gates.sh Bindings.ForceCellIntegral` and the standalone `check_contracts.py --base-ref origin/erenup/integration` exit 1 with:
   `AssertionError: Removed stable specification: verification/Contracts/V1/MainThresholds.lean`.
   The check is `experiments/check_contracts.py:62`; the worker correctly disclosed the same issue at `research/R47/REPORT_251.md:66`. The file is absent at HEAD and present at the requested base reference (blob `ca17729a129c1e1be297c2428902fcbccc92d1db`). The merge-base is `b2db3263d9e85fdf6282a35557c515f2176579f4`, and the three-dot diff confirms this is baseline drift, not a deletion introduced by the lane. Nevertheless, the expressly required gate has not passed. **Fix:** synchronize the worker's lane with the current integration baseline while preserving existing contracts, then rerun the required compatibility check and complete gate suite. This reviewer made no git changes.

2. **Permitted analytic gap, honestly isolated.** `ForceCellIntegral.lean:146` quantifies the residual-integral identity over all admissible scales, containing grid cells, and interior times; `:205` repeats exactly that input for force observations. It is a large remaining assembly step and, with the proved momentum/temporal identities, is equivalent to the needed interior zero-force mean. It must not be described as an unconditional proof of eq:gridforce. The report does not do so. The mathematical satisfiability argument at `ATTEMPTS_FORCE_CELL.md:56` is sound: expand convection into the tensor divergence, use compact pressure/velocity support and smoothness for spatial derivative cancellation, and use a fixed time window for the temporal term. It imposes neither false two-sided regularity at zero nor regularity through blowup.

   Before accepting the missing-assembly claim, I ran recursive grep over the **entire** `formalization/NSFormalization/Section4` tree (commands below). Existing useful ingredients include `A04/AdvectionDivergence.lean:76` and `:91`, which were opened; `R42/Assembly.lean:122` and `:169`, also opened, are pointwise slab momentum/incompressibility, not the integrated force cancellation. Outside Section4, `Paper3/ForceObservations.lean:18` already proves compact-partial cancellation, `:28` proves a conditional conservative-flux integral, and `Paper3/TimeObservations.lean:40` provides its time-dependent version. Thus the gap is the actual inserted-family flux/support/integrability assembly, not missing general integration-by-parts or differentiation-under-the-integral lemmas. No ready-made assembly was found in the Section4 search.

3. **Negative check passed.** `research/R47/probes/rev251_constant.lean:10` copies the main component theorem and its proof, changing only the conclusion's constant from 0 to 1. Every argument and hypothesis is retained. Lean rejects it at `:14` because the compact-solenoidal lemma concludes integral = 0 whereas the mutated goal is integral = 1. This is a substantive constant mutation, not an omitted argument.

## 4. Commands and results

All Lean shells loaded `. scripts/lean-env.sh`; all lake commands ran from `verification/` with `LEAN_NUM_THREADS=6`, one at a time. Existing toolchain/cache were used; installation was unnecessary and was not run because this review preserves repository state. Long gate output is excerpted, with omissions explicitly marked; shown output lines are verbatim.

`lake build Bindings.ForceCellIntegral`: exit 0. No diagnostic from this module; dependency replay warnings mean the entire command is not literally silent. Exact beginning/end excerpts:
```text
⚠ [8779/8828] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
[intervening dependency replay warnings omitted]
⚠ [8818/8828] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (8828 jobs).
```

`lake env lean Bindings/ForceCellIntegral.lean`: exit 0, exactly 0 output bytes.

`lake env lean ../research/R47/axioms_force_cell_integral.lean`: exit 0, complete output:
```text
'BlowupDensity.Bindings.insertion_reference_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.velocityDifference_slice_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.velocityDifference_slice_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.velocityDifference_cell_integral_zero_component' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.velocityDifference_cell_integral_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.insertion_momentum_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.forceDifference_initial_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.velocityDifference_timeDerivative_integral_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.forceDifference_cell_integral_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.continuous_integrableOn_grid_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.forceDifference_slice_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.velocity_gridObservation_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.force_gridObservation_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.force_gridObservation_initial_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`make check`: exit 0; 31,833 output lines, exact first/last 40 lines below (wrapper adds exit/line count and omission marker):
```text
exit: 0 lines: 31833
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 547,
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
  "registered_contracts": 31,
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
      "Tests.CriticalFiniteHorizon"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

`lake env lean ../research/R47/probes/rev251_constant.lean`: expected exit 1, complete output:
```text
../research/R47/probes/rev251_constant.lean:14:2: error: Tactic `apply` failed: could not unify the conclusion of `setIntegral_component_eq_zero
  (ContDiff.of_le (velocityDifference_slice_smooth A hε ht) ?m.70) (velocityDifference_slice_compact A hε ht)`
  ∫ (x : NavierStokes.ProblemStatement.Space) in ?C, (A.velocity ε (t, x) - A.v (t, x)).ofLp ?j = 0
with the goal
  ∫ (x : NavierStokes.ProblemStatement.Space) in CartesianGrid.cell grid k₀, (A.velocity ε (t, x) - A.v (t, x)).ofLp j =
    1

Note: The full type of `setIntegral_component_eq_zero (ContDiff.of_le (velocityDifference_slice_smooth A hε ht) ?m.70)
  (velocityDifference_slice_compact A hε ht)` is
  (∀ (x : EuclideanSpace ℝ (Fin 3)),
      NavierStokes.Comparator.divergence (fun x => A.velocity ε (t, x) - A.v (t, x)) x = 0) →
    ∀ {C : Set NavierStokes.ProblemStatement.Space},
      MeasurableSet C →
        (Function.support fun x => A.velocity ε (t, x) - A.v (t, x)) ⊆ C →
          ∀ (j : Fin 3), ∫ (x : NavierStokes.ProblemStatement.Space) in C, (A.velocity ε (t, x) - A.v (t, x)).ofLp j = 0

ν : ℝ
P : PacketAPI ν
A : InsertionFamilyAPI ν P
ε t : ℝ
hε : ε ∈ Ioc 0 A.ε₀
ht : t ∈ Ico 0 A.T
grid : Grid
k₀ : Fin 3 → ℤ
hB : A.ball ⊆ CartesianGrid.cell grid k₀
j : Fin 3
⊢ ∫ (x : NavierStokes.ProblemStatement.Space) in CartesianGrid.cell grid k₀, (A.velocity ε (t, x) - A.v (t, x)).ofLp j =
    1
```

`LEAN_NUM_THREADS=6 bash scripts/gates.sh Bindings.ForceCellIntegral`: exit 1; 31,945 output lines. The build and contract test messages precede the successful mutation suite; the final compatibility check fails. Exact final excerpt:
```text
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
Traceback (most recent call last):
  File "/data_8T/ping/blowup_density/.claude/worktrees/251-R47-force-cell-integral/experiments/check_contracts.py", line 153, in <module>
    print(json.dumps(check(base=args.base_ref), indent=2))
                     ^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/data_8T/ping/blowup_density/.claude/worktrees/251-R47-force-cell-integral/experiments/check_contracts.py", line 143, in check
    check_compatibility(root, base, contracts)
  File "/data_8T/ping/blowup_density/.claude/worktrees/251-R47-force-cell-integral/experiments/check_contracts.py", line 62, in check_compatibility
    assert (root / path).is_file(), f'Removed stable specification: {path}'
           ^^^^^^^^^^^^^^^^^^^^^^^
AssertionError: Removed stable specification: verification/Contracts/V1/MainThresholds.lean
```

`make test`: independently checked because the existing gate script filters this output with an `|| true` pipeline; exit 0, 362 lines. Exact beginning/end excerpt:
```text
lake -d verification test
⚠ [8778/9037] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
[middle omitted]
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
ℹ [10690/10691] Replayed Tests.TameProduct
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
ℹ [10691/10691] Replayed Tests.CriticalFiniteHorizon
info: Tests/CriticalFiniteHorizon.lean:19:0: Contract BlowupDensity.Tests.checkedCriticalFiniteHorizon: checked; standard logical axioms only
```

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`: independently rerun, exit 1, exactly the same traceback shown above (without the gate headings/mutation output). The alternative merge-base check cannot substitute for this requested gate.

`git diff --name-only origin/erenup/integration...HEAD`: exit 0, complete output:
```text
research/R47/ATTEMPTS_FORCE_CELL.md
research/R47/REPORT_251.md
research/R47/axioms_force_cell_integral.lean
verification/Bindings/ForceCellIntegral.lean
```
`git diff --name-status origin/erenup/integration...HEAD` marks each of these A. `git diff --check`: exit 0, no output. Hygiene search `rg -n '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats' verification/Bindings/ForceCellIntegral.lean research/R47/axioms_force_cell_integral.lean`: no matches.

Missing-lemma searches (whole Section4, no subdirectory restriction):
```sh
grep -rnE 'compactMomentumIntegral|forceDifference_cell_integral|integral_spatialPartial_eq_zero|integral.*[Dd]iv|[Dd]iv.*integral|integral.*[Rr]esidual|[Rr]esidual.*integral' formalization/NSFormalization/Section4
grep -rnE 'compactMomentumIntegral|forceDifference_cell_integral|integral_timeDependent_force|integral_force_of_compact|integral_spatialPartial|setIntegral_component|advection_eq_sum_partialDeriv_outerColumn|integral.*(laplacian|gradient|residual|flux)|([Ll]aplacian|[Gg]radient|[Rr]esidual|[Ff]lux).*integral' formalization/NSFormalization/Section4
```
The first finds only the weak-divergence documentation at `A01/ConstructorDivergenceSlice.lean:24`; the second finds the A04 convection identities and unrelated C01 energy/Laplacian pairings, not an inserted-family cell residual integral. The cited A04 and Paper3 source statements were read, not inferred from their names.

Required fix: update the lane baseline and rerun the failing integration gates. No mathematical statement correction is requested for the permitted conditional result.

