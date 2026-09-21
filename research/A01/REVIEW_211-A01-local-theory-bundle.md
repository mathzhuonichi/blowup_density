ACCEPT

## 1. What the lane claims

Reviewed commit `08b71c5b4936f91e8f86b65dc61e2790aa7f6da4`, against local remote-tracking integration `c8e5625a1209259d3b05b359bcfe5c5ef562dd5b`. Read CLAUDE.md, the lane-review skill, the first 40 LESSONS lines, HANDOFF §0/§2 P7, NEXT_SESSION's 0600Z decision entry, Spec, reports 208–211, the 209 witness-preservation note, and the lane attempts.

`research/A01/REPORT_211.md:5` claims a fixed-force physical H⁷ uniform lower bound, antitonicity, and manuscript regularity for one bundled chosen solution. These claims are present with the stated types; this is deliberately not a proof of the original H¹ uniformity field. The paper passages were opened with sed: `paper/sections/02-preliminaries.tex:80` (projected equation), `:90` (pressure), `:96` (potential), `:105` (local theory), and `paper/sections/appendix-a-local-theory.tex:60`, `:71`, `:79`, `:146` (common all-order interval, endpoint smoothness, viscosity, H¹ restart). The fixed-force H⁷ theorem is the brief's explicitly authorized variant, not a claim to have proved the paper's H¹ statement.

## 2. What is in Lean

Below, B denotes `formalization/NSFormalization/Section4/A01/LocalTheoryBundle.lean`; other abbreviated A01 paths have the same directory.

1. **Carrier preservation — pass.** B:31–68 bundles positive viscosity/horizon, admissible force, datum and datum identification, U/hU0, the full all-order hpairs/hpaths, velocity/hslice/hc3, G/hG_int/hG, and w with velocity and initial-data equalities. B:83 chooses U exactly once; B:84 obtains the representative from that U and its paths; B:86 supplies pressure for those exact objects; B:88–89 passes them to the constructor. B:96–98 stores those same witnesses. `LocalSolution.lean:20` changes only the initial proof, preserving velocity and pressure. No unrelated existential w or carrier is reselected. B:291–308 chooses the entire resulting bundle on the horizon used by the solver. The selected smooth datum is the same in the radius and reconstruction (B:254, B:295–302).

   Opened the actual suppliers: `CylinderWiring.lean:36`, `JointRepresentative.lean:552`, `PressureRegularity.lean:362`, `ConstructorAssembly.lean:259` (the constructor defines pressure from the supplied G at line 287). Their binders match the bundle's witnesses. Although the structure does not separately export a pressure equality, the actual construction uses its retained G. No false same-carrier assertion is needed.

2. **Uniform selection — pass, with the brief's explicit-selection alternative.** B:111 defines admissible times in [0,1] satisfying both strict budgets; B:117 selects half their supremum. Nonemptiness/boundedness are proved at B:119/124; a positive member supplied by `exists_positive_time_budget` proves positivity at B:127. B:135 obtains an admissible time above the half-supremum and transfers both strict inequalities downward. B:154 proves antitonicity by inclusion of sets, using `HorizonUniform.lean:67` (`picard_budget_mono`). B:187 combines this with the increasing ball and Lipschitz bounds; the latter uses `HorizonUniform.lean:55`.

   This does **not** literally choose the existential witness of `exists_uniform_H7_sup_force_horizon`. It uses precisely that theorem's budgets (`HorizonUniform.lean:126–138`) and replays its Picard argument on a specified antitone selection (B:213–250). This is the mathematically necessary selection alternative expressly allowed by the brief. Likewise it reconstructs the witness-preserving composition behind `constructor_of_base`, rather than calling a nonexistent production export: that name exists at `research/A01/probes/a01_constructor_unconditional.lean:20`; the exported input is `TameAssembly.lean:408`, `hb_of_base''`. B:70–98 matches that pipeline and lane 208's `LocalSolution.lean:39`, retaining its witnesses.

   B:263 constructs the continuous H⁶ force path on [0,1] using `C01/JetPaths.lean:99`, `forcePath_jetLp_continuous`. B:269 proves finite real uniform bounds using `ContinuousMap.norm_coe_le_norm`. Compactness of Icc supplies the continuous-map sup norm; no ENNReal force norm is converted without a finiteness premise. B:274–281 is total, returning 1 on inadmissible inputs; on admissible inputs B:283 and B:184 establish positivity. Thus neither Ico nor Ioo is vacuous. B:298–301 builds the base solution and bundle on exactly this horizon. Restriction of the reference force to that interval elaborates without a new force hypothesis.

3. **H⁷ lower bound and physical comparison — pass.** Exact theorem at B:342:

```lean
theorem horizon_lower_bound_H7_fixedForce :
    ∀ ν, 0 < ν → ∀ f, D01.MemForceR f → ∀ K : ℝ≥0∞, K ≠ ⊤ →
      ∃ δ > 0, ∀ a, a ∈ A02.initialClassR → D01.sobolevENorm 7 a ≤ K →
        δ ≤ localHorizon' ν a f
```

   B:347 chooses δ = uniformHorizon ν (datumRadiusConstant * K.toReal) ‖referenceForce f hf‖ **before** introducing a at B:349. B:351 uses antitonicity in the correct direction. B:318 explicitly gives C = ∑ j ∈ Finset.range 8, D01.jetDatumConst j 7. B:324–337 proves cylinder radius ≤ C‖D‖ through `vendor/NavierStokesAndEuler/Euler/OrdinaryCauchyInterpolation.lean:40`, jet equality, and `D01/DatumToJets.lean:224`. The constant at `D01/DatumToJets.lean:218` is (‖physicalJetLp j‖ + 1) * frequencyUnit^(7:ℝ). At B:357–360, `ENNReal.toReal_mono hK` and a real Sobolev datum identify the physical norm, explicitly excluding the top-to-zero trap.

   Opened the suggested comparison lemmas: `D01/FiniteOrderNorm.lean:435` (16^m), `:496` (4^m), and `A01/OrderTwoCap.lean:129`. They bound the physical datum by derivative/cylinder bounds, the opposite direction to the radius bound here. The worker's replacement is correct, explicit, and sufficient.

4. **Unasserted H¹ field — pass.** B:372–379 is a Prop definition only. After binding horizon := localHorizon', its whitespace-token sequence is identical to `research/A01/Spec.lean:338–343`. No theorem concludes it and no bundle/constructor input assumes it. Whole-Section4 name searches find only this definition, its comment, and `HorizonUniform.lean:23`. `research/A01/probes/local_theory_api_shape.lean:99` proves definitional equality with lane 210's `HorizonLowerBoundH1 localHorizon'`; replay passed. This equality is not a proof of either proposition.

5. **Regularity and API — pass.** B:101–105 passes c.w, c.U, c.hpaths and its velocity-transported slice identity to `ManuscriptRegularity.lean:247`. B:310–314 specializes this to the chosen bundle on its exact horizon. All four manuscript clauses, including pressure recovery at zero, refer to the same solution. B:381–400 packages horizon, solution, regularity and the H⁷ bound. The API structure copied at `research/A01/probes/local_theory_api_shape.lean:11` matches the Spec structure text, including documentation; field checks at lines 81–90 replay silently. No full LocalTheoryAPI inhabitant is claimed.

6. **Hygiene, build coverage and non-vacuity — pass.** The 34 top-level declarations listed at `research/A01/axioms_local_theory_bundle.lean:7–40` all audit to exactly [propext, Classical.choice, Quot.sound], including wrapped output lists. No forbidden proof tokens or maxHeartbeats settings occur in either new production module. No existing Lean module or verification file changes in the three-dot diff. `experiments/build_changed_lean.py:18` includes formalization modules, and its dry run names both new modules; CI calls it at `.github/workflows/contracts.yml:81`.

   The existing audit's zero datum/force instance at `research/A01/axioms_local_theory_bundle.lean:43–46` constructs the actual bundle and regularity on a positive horizon; it replayed. The public constructor requires only admissibility and positive viscosity, not separate satisfiability assumptions about hc3/hpaths/G: those are derived internally. Thus the zero instance is not masking an added assumption restricting the theorem to stationary solutions.

## 3. Gaps and findings

No blocking findings or required fixes.

- The original H¹ uniformity and owner-approved V2 registration remain open exactly as reported (`REPORT_211.md:31–36`, B:368–379). Whole-tree `grep -rn` searches for H¹/H1, horizon_lower_bound, uniform restart/local existence, and the obligation names were followed by opening the closest candidates: `A01/Continuation.lean:249` still requires q ≥ 6 and a cylinder norm bound; `A01/Horizon.lean:61` explicitly excludes the H¹ field; `A01/HorizonUniform.lean:114` gives H⁷/time-sup force uniformity. None supplies the missing forced physical H¹ theorem. “Not provable from the tree” is understood as “no existing supplier closes the obligation,” not a metamathematical independence claim. The lane-210 L¹/sup obstruction is not silently claimed solved for varying force.
- The branch history is exactly lane 210 `d4febc0`, integration merge `9e0c8c6`, and lane 211 `08b71c5` beyond the common base. The literal two-tip `git diff origin/erenup/integration --stat` also shows integration-only records as deletions (PLAN, the lane brief, AGENT_RUNS, LESSONS). `git log HEAD..origin/erenup/integration` identifies the newer integration commits `25ffe80`, `0999014`, `c8e5625`; these are not lane deletions. The requested three-dot diff contains only the two new modules, research records and probes, with A3_SPLIT the only modified existing file. No git changes were made by this reviewer.
- **Substantive negative check:** `research/A01/probes/rev211_negative.lean:12` changes the H⁷ theorem's conclusion from δ ≤ localHorizon' to δ ≤ -localHorizon', preserving every premise and the complete original proof. Lean fails at line 18, where antitonicity cannot establish a negative horizon bound. This is a sign mutation, not an omitted argument. The positive control `research/A01/probes/rev211_control.lean:9` with the original sign and otherwise identical proof passes silently. The mutation is also mathematically false on the existing zero instance because both δ and its horizon are positive.

## 4. Commands and results

All Lean shells sourced `. scripts/lean-env.sh`; every lake invocation ran in verification with LEAN_NUM_THREADS=6, one at a time. Existing packages were already symlinked to the installed shared dependencies, so no installer or repository mutation was necessary. Only this report and the permitted rev211 probes were written.

Required gates: ordinary module build exit 0 (dependency warnings only, no LocalTheoryBundle diagnostics); quiet module build exit 0/zero bytes; direct module Lean exit 0/zero bytes; audit exit 0/34 exact standard lists; API probe exit 0/zero bytes; make check exit 0; lake test exit 0. Also ran the positive control, expected-failing mutation, base-ref contract checker, and git diff --check. No verification files were touched, so the conditional scripts/gates.sh gate does not apply; it was not run. The worker's make test-mutations claim was not independently replayed, since that harness mutates existing contract files, outside this read-only review.

Exact gate-output excerpts follow. For long output only the first and last 12 lines are quoted (stricter than the 40-line limit); no full build/make logs are embedded.

`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.LocalTheoryBundle` — exit 0.

```text
⚠ [8927/9494] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
[... middle omitted ...]
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10358/10412] Replayed NSFormalization.Section4.A01.MildGronwall
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (10412 jobs).
```

`cd verification && LEAN_NUM_THREADS=6 lake -q --log-level=error build NSFormalization.Section4.A01.LocalTheoryBundle` — exit 0; output: 0 bytes.

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/LocalTheoryBundle.lean` — exit 0; output: 0 bytes.

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_local_theory_bundle.lean` — exit 0.

```text
'NSFormalization.Section4.A01.LocalCarrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.localCarrier_of_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.LocalCarrier.regularity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.uniformBudgetSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.uniformBudget' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.uniformBudgetSet_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.uniformBudgetSet_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.uniformBudget_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.uniformBudget_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.uniformBudget_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.referenceCoefficients' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.uniformBallBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.uniformLipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.uniformHorizon' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.uniformHorizon_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.uniformHorizon_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.uniformHorizon_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.uniformHorizon_mild' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.selectedDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.selectedDatum_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.referenceForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.referenceForce_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.localHorizon'' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.localHorizon'_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.localCarrier_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.localCarrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.manuscriptLocalRegularity_localCarrier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.datumRadiusConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.datumRadiusConstant_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderDatum_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.horizon_lower_bound_H7_fixedForce' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.ManuscriptHorizonLowerBoundH1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.LocalTheoryDataShape' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.localTheoryData' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/local_theory_api_shape.lean` — exit 0; output: 0 bytes.

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev211_negative.lean` — exit 1.

```text
../research/A01/probes/rev211_negative.lean:18:2: error: Tactic `apply` failed: could not unify the type of `uniformHorizon_antitone ν ?m.82 le_rfl`
  uniformHorizon ν ?m.79 ?m.85 ≤ uniformHorizon ν ?m.78 ?m.85
with the goal
  uniformHorizon ν (datumRadiusConstant * K.toReal) ‖referenceForce f hf‖ ≤
    -uniformHorizon ν ‖ordinarySobolev 7 (selectedDatum a ha).toLp ⋯‖ ‖referenceForce f hf‖

ν : ℝ
hν : 0 < ν
f : NavierStokes.ProblemStatement.VelocityField
hf : D01.MemForceR f
K : ℝ≥0∞
hK : K ≠ ∞
a : A02.SpatialField
ha : a ∈ A02.initialClassR
hbound : D01.sobolevENorm 7 a ≤ K
⊢ uniformHorizon ν (datumRadiusConstant * K.toReal) ‖referenceForce f hf‖ ≤
    -uniformHorizon ν ‖ordinarySobolev 7 (selectedDatum a ha).toLp ⋯‖ ‖referenceForce f hf‖
```

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev211_control.lean` — exit 0; output: 0 bytes.

`cd verification && LEAN_NUM_THREADS=6 lake test` — exit 0.

```text
⚠ [8778/8983] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
[... middle omitted ...]
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

`make check` — exit 0; 28234 output lines. First/last 12:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 528,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
[... middle omitted ...]
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

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration` — exit 0; 28202 output lines. First/last 12:

```text
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
[... middle omitted ...]
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.GradientL6V2"
    ]
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

Final disposition: ACCEPT. Required fixes: none.

