REJECT

## 1. What the lane claims

Reviewed HEAD `2aa5573d186301632a9df716b24ef2ab41d681d7` against current `origin/erenup/integration` `cca9615b70c4d022733658a4ad2f23ae4f5bc695`; merge base `028b15efd6527f614ae036231f8381098199e875`. Read CLAUDE.md, lane-review skill, LESSONS first 40 lines, HANDOFF §0, the complete draft ScalingAPI, worker report and attempts.

`research/I03/REPORT_250.md:1` claims exact homogeneous Fourier/angular/datum/time scaling and the packet/correction bounds, conditional on one analytic input. Its API constants and same-family claims are at :3; the remaining measurability gap is explicitly acknowledged at :5. These mathematical claims check out as conditional results. Rejection is for the required current-base gates, not a discovered mathematical counterexample.

The manuscript was opened with `sed -n '64,80p;264,275p'`: `paper/sections/04-whole-space.tex:70` supplies the valid range; :57 defines beta; :264 gives the spatial homogeneous factor; :268 gives the two target bounds. Thus beta is `2/q - 3/2 - s`, and beta+1 is the correction exponent. At q=2,s=-1 these are 1/2 and 3/2.

## 2. What is in Lean

Paths abbreviated here: H = `formalization/NSFormalization/Section4/I03/HomogeneousScaling.lean`; B = `verification/Bindings/ScalingHomogeneous.lean`.

1. **Fidelity passes, conditional scope retained.** H:23 proves the weighted-integral identity; H:44 the spatial norm identity; H:51 and H:69 the time identities. H:190 proves the angular conversion factor `(2π)^(2s)`; H:213 identifies the actual datum norm. H:237 proves vector-datum spatial scaling, H:330 time scaling, and H:356 positive-axis restriction. These are homogeneous weights, not a negative-order Bessel contraction. H:83 and H:166 separately establish finiteness in the admissible range; the general scalar integral identities are explicitly totalized (H:11), not used to infer finiteness.

2. **Registered norm and exact packet constant.** B:27 states precisely one analytic hypothesis: a.e. strong measurability of D01's concrete compact path for every compact smooth force and -3/2<s<0. B:39–43 exhibits that path in the infimum defined at `verification/Contracts/V1/Data.lean:390`; slice predicates match Data:324, :367, :375. B:62 identifies the infimum with its path norm; B:76 and B:98 give the exact scaling identity with the necessary nonnegative delay and zero-past hypotheses. B:162 gives the bound with `(Data.forceHomogeneousENorm q s packet.force).toReal`; finiteness is proved at B:152 and used at B:173. There is no top-toReal loophole.

3. **Correction and same family.** H:109 derives actual correction scaling from `Paper1/CorrectionForceNorms.lean:100` (uniform finite profile time bounds) and :148 (physical force equals epsilon times the cubic-amplitude rescaling). H:173 sums components. B:178 transfers through the existing window extension to C.forceCorrection. B:192 chooses `(2π)^s * K.toReal` with K finite and independent of epsilon; B:211 assembles the constant family before epsilon is quantified. B:230 inhabits the existing HomogeneousScalingAPI, definitionally using `Bindings.scaling C th`. Both clauses use the same threshold, positive by `verification/Bindings/Scaling.lean:351`. Its interval is not empty.

4. **Draft / existing API comparison.** `research/I03/Spec.lean:444` and :465 are copied verbatim in `research/I03/ATTEMPTS_HOMOGENEOUS.md:6` and :11. Their ranges, powers and force families are preserved by the existing migrated API at `verification/Contracts/V1/Scaling.lean:535` and :548. The latter uses separate homogeneous constant fields rather than the draft's shared inhomogeneous constants; the lane correctly claims to assemble this existing API (B:227), not to construct the whole draft record. Neither homogeneous field is registered. Placement in Bindings is appropriate because Contracts is downstream (B:13).

5. **Source cross-checks.** Opened statements and proofs at `Source/TimeNormScaling.lean:133`, `Paper1/CorrectionVectorNorms.lean:83`, and `verification/Bindings/ScalingNorms.lean:133`, :161: their left sides are inhomogeneous, so they alone would not prove this lane. `Source/FourierScaling.lean:22`, :25, :39 confirm amplitude k³ and inverse Fourier dilation. `Paper3/HomogeneousTime.lean:82`, :108 prove the finite compact profile time norm. These citations agree with COMPARISON:46–49.

6. **Hygiene and non-vacuity.** Both new modules contain no sorry/admit/axiom/native_decide or maxHeartbeats override. All 36 named declarations are covered by the audit and print exactly the three allowed axioms. B:121 has a redundant `_hb` nonnegativity binder; it does not imply falsehood or hide a missing estimate. The standalone B:134 bound does not need the interval's upper bound, since it holds for every positive epsilon; the assembled API has a positive threshold. Zero force is checked at B:247, :255, :263 and audit:45. Audit:49 checks the actual PacketAPI slice path; `research/I03/packet_homogeneous_example.lean:8` checks finiteness for the concrete `Bindings.packet 1`. These examples pass, but do not prove the global measurability hypothesis; the report accurately says so.

7. **Negative check.** `research/I03/probes/rev250_exponent.lean:5` copies the spatial scaling proof and changes only 3/2 to 5/2 in its conclusion. Lean rejects it with the expected residual exponent equality (full error below). No argument was dropped.

The three-dot diff lists only two new Lean modules and new research files, plus the authorized COMPARISON row update; no existing Lean module was edited. The new modules are covered by changed-module discovery (`experiments/build_changed_lean.py:17`), although the unregistered homogeneous API is not added to the ordinary contract-test closure.

## 3. Gaps and required fixes

1. **Blocking — required current-base compatibility fails.** `scripts/gates.sh:13` and the standalone checker both exit 1:
   `AssertionError: Removed stable specification: verification/Contracts/V1/MainThresholds.lean`.
   The check is at `experiments/check_contracts.py:62`. This contract was added to integration by `d28b92b [249-R41] Theorem 4.1 contract` after this lane's fork; it is not a lane deletion in the three-dot diff. The worker disclosed the failure at `research/I03/REPORT_250.md:7`. Checking against the old merge base passes, but does not satisfy the requested current-base gate.
   **Fix:** the lane owner/integrator must synchronize the lane with current integration, preserve its stable contracts, and rerun the exact gates and direct Lean/audit checks. No synchronization or git mutation was performed by this reviewer.

2. **Allowed analytic gap, not an additional rejection reason.** B:27 remains unproved for general nonzero compact forces. Ran `grep -rnE 'compactHomogeneousPath|[Mm]easurable.*[Hh]omogeneous|[Hh]omogeneous.*[Mm]easurable' formalization/NSFormalization/Section4` across the whole Section4 tree, plus the B02 strong-measurability search. The relevant existing results are `D01/HomogeneousWitness.lean:644`, :656 (constructor and slice path) and :690 (norm equality still requiring measurability); `R43/ForcePath.lean:56` and `R43/CriticalDatumPath.lean:133` only convert nonnegative-order data. B02's frequency-variable measurability and separated paths do not assert measurability of the general compact path. No existing theorem discharging the claimed missing fact was found. The brief expressly permits one named exact analytic input, so this conditional delivery is mathematically within that allowance. It must not be described as unconditional Prop. 4.6 / Thm 4.7.

No proof-code fix is requested from the mathematical review. The remaining required fix is integration synchronization and successful gate reruns.

## 4. Commands and results

All direct Lake commands used `. scripts/lean-env.sh`, cwd `verification/`, and `LEAN_NUM_THREADS=6`, one Lake process at a time. The existing package symlink and configured toolchain worked; no installation or git-changing setup was run. Long raw outputs below are limited to exact head/tail excerpts (at most 40 lines each), following LESSONS; omissions are explicitly marked.

### Module build

`lake build NSFormalization.Section4.I03.HomogeneousScaling Bindings.ScalingHomogeneous`: exit 0. Dependency warnings are replayed; neither new module emits a warning. Literal global silence is therefore not claimed.

```text
⚠ [8784/8921] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9328/9388] Replayed NSFormalization.Source.RealSobolev
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
  Complex.smul_re

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_im]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused:
  Complex.smul_im

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_re]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9332/9388] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9339/9388] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9342/9388] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9353/9388] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9356/9388] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (9388 jobs).

```

### Direct checks and examples

Each command exited 0 with exactly zero output:
```sh
lake env lean ../formalization/NSFormalization/Section4/I03/HomogeneousScaling.lean
lake env lean Bindings/ScalingHomogeneous.lean
lake env lean ../research/I03/packet_homogeneous_example.lean
```

`lake env lean ../research/I03/axioms_homogeneous_scaling.lean`: exit 0, exact output:
```text
'NSFormalization.Section4.I03.homogeneous_integral_concentrated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.I03.homogeneous_norm_concentrated' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.homogeneous_time_scaling' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.homogeneous_time_scaling_epsilon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.I03.homogeneous_profile_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.homogeneous_norm_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.correction_scalar_homogeneous' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.componentTimeNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.componentTimeNorm_packet' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.componentTimeNorm_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.correction_componentTimeNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.angular_homogeneous_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.norm_homogeneousDatum_cycles' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.homogeneous_vector_datum_scaling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.I03.compactHomogeneousPath_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.compactHomogeneousPath_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.compactHomogeneousPath_norm_stronglyMeasurable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.I03.homogeneous_datum_time_scaling' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.homogeneous_datum_positive_eq_volume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.I03.CompactHomogeneousRealization' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.forceHomogeneousENorm_le_components' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.I03.forceHomogeneousENorm_eq_path' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.forceHomogeneousENorm_scaling' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.packetHomogeneousIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.packetHomogeneousConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.homogeneous_bound_of_components' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.I03.packetNegativeHomogeneous' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.forceHomogeneousENorm_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.packetNegativeHomogeneous_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.I03.correction_components' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.correctionNegativeHomogeneous' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.exists_correction_homogeneous_const' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.I03.homogeneousScaling' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.zero_homogeneous_path' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.forceHomogeneousENorm_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.I03.compact_realization_zero' depends on axioms: [propext, Classical.choice, Quot.sound]

```

### Substantive mutation

`lake env lean ../research/I03/probes/rev250_exponent.lean`: expected exit 1:
```text
../research/I03/probes/rev250_exponent.lean:8:54: error: unsolved goals
s : ℝ
f : Space → ℂ
k : ℝ
hk : 0 < k
⊢ k ^ (3 / 2 + s) * √(∫ (ξ : Space), ‖ξ‖ ^ (2 * s) * ‖FourierTransform.fourier f ξ‖ ^ 2) =
    k ^ (5 / 2 + s) * √(∫ (ξ : Space), ‖ξ‖ ^ (2 * s) * ‖FourierTransform.fourier f ξ‖ ^ 2)

```

### make check

Exit 0; 31833 output lines. Exact captured head/tail:
```text
EXIT 0 LINES 31833
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
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.

```
The copied umbrella's reported BoundaryCorollary token is pre-existing and not in the new modules' axiom closure.

### Standard gate script and contract compatibility

`LEAN_NUM_THREADS=6 bash scripts/gates.sh NSFormalization.Section4.I03.HomogeneousScaling Bindings.ScalingHomogeneous`: exit 1, 31955 lines. make check and the module build passed; the test output listed checked contracts; mutation tests passed. Exact final mutation/check portion:
```text
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
Traceback (most recent call last):
  File "/data_8T/ping/blowup_density/.claude/worktrees/250-I03-homogeneous-scaling/experiments/check_contracts.py", line 153, in <module>
    print(json.dumps(check(base=args.base_ref), indent=2))
                     ^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/data_8T/ping/blowup_density/.claude/worktrees/250-I03-homogeneous-scaling/experiments/check_contracts.py", line 143, in check
    check_compatibility(root, base, contracts)
  File "/data_8T/ping/blowup_density/.claude/worktrees/250-I03-homogeneous-scaling/experiments/check_contracts.py", line 62, in check_compatibility
    assert (root / path).is_file(), f'Removed stable specification: {path}'
           ^^^^^^^^^^^^^^^^^^^^^^^
AssertionError: Removed stable specification: verification/Contracts/V1/MainThresholds.lean

```

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`: exit 1, identical traceback above.

Diagnostic only: `python3 experiments/check_contracts.py --base-ref 028b15efd6527f614ae036231f8381098199e875`: exit 0, exact tail:
```text
EXIT 0
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}

```

Because `scripts/gates.sh:11` masks make-test failure with `|| true`, also ran `cd verification; LEAN_NUM_THREADS=6 lake test` directly: exit 0. Exact head/tail:
```text
⚠ [8778/8914] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9875/10652] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9876/10652] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10270/10652] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:30: Variable name `hB` is not explicitly referenced.
[middle omitted]
ℹ [10636/10691] Replayed Tests.InsertionFamily
info: Tests/InsertionFamily.lean:19:0: Contract BlowupDensity.Tests.checkedInsertionFamily: checked; standard logical axioms only
ℹ [10640/10691] Replayed Tests.RegularityPartial
info: Tests/RegularityPartial.lean:17:0: Contract BlowupDensity.Tests.checkedRegularityPartial: checked; standard logical axioms only
ℹ [10648/10691] Replayed Tests.BochnerPartial
info: Tests/BochnerPartial.lean:14:0: Contract BlowupDensity.Tests.checkedBochnerPartial: checked; standard logical axioms only
ℹ [10649/10691] Replayed Tests.DatumLemmas
info: Tests/DatumLemmas.lean:14:0: Contract BlowupDensity.Tests.checkedDatumLemmas: checked; standard logical axioms only
ℹ [10651/10691] Replayed Tests.BoundedRepresentative
info: Tests/BoundedRepresentative.lean:14:0: Contract BlowupDensity.Tests.checkedBoundedRepresentative: checked; standard logical axioms only
ℹ [10654/10691] Replayed Tests.CorrectionV2
info: Tests/CorrectionV2.lean:28:0: Contract BlowupDensity.Tests.checkedCorrectionV2: checked; standard logical axioms only
ℹ [10665/10691] Replayed Tests.HomogeneousPartial
info: Tests/HomogeneousPartial.lean:15:0: Contract BlowupDensity.Tests.checkedHomogeneousPartial: checked; standard logical axioms only
ℹ [10666/10691] Replayed Tests.GradientL6
info: Tests/GradientL6.lean:13:0: Contract BlowupDensity.Tests.checkedGradientL6: checked; standard logical axioms only
ℹ [10669/10691] Replayed Tests.GradientL6V2
info: Tests/GradientL6V2.lean:22:0: Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
ℹ [10672/10691] Replayed Tests.EnergyHighPartialV2
info: Tests/EnergyHighPartialV2.lean:30:0: Contract BlowupDensity.Tests.checkedEnergyHighPartialV2: checked; standard logical axioms only
ℹ [10675/10691] Replayed Tests.DatumLemmasV3
info: Tests/DatumLemmasV3.lean:31:0: Contract BlowupDensity.Tests.checkedDatumLemmasV3: checked; standard logical axioms only
ℹ [10676/10691] Replayed Tests.Correction
info: Tests/Correction.lean:19:0: Contract BlowupDensity.Tests.checkedCorrection: checked; standard logical axioms only
ℹ [10677/10691] Replayed Tests.MaximalPartial
info: Tests/MaximalPartial.lean:16:0: Contract BlowupDensity.Tests.checkedMaximalPartial: checked; standard logical axioms only
ℹ [10678/10691] Replayed Tests.Uniqueness
info: Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only
ℹ [10679/10691] Replayed Tests.HomogeneousNorm
info: Tests/HomogeneousNorm.lean:17:0: Contract BlowupDensity.Tests.checkedHomogeneousNorm: checked; standard logical axioms only
ℹ [10684/10691] Replayed Tests.HomogeneousPartialV2
info: Tests/HomogeneousPartialV2.lean:35:0: Contract BlowupDensity.Tests.checkedHomogeneousPartialV2: checked; standard logical axioms only
ℹ [10686/10691] Replayed Tests.MaximalPartialV2
info: Tests/MaximalPartialV2.lean:24:0: Contract BlowupDensity.Tests.checkedMaximalPartialV2: checked; standard logical axioms only
ℹ [10689/10691] Replayed Tests.InsertionLifespanV2
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
ℹ [10690/10691] Replayed Tests.TameProduct
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
ℹ [10691/10691] Replayed Tests.CriticalFiniteHorizon
info: Tests/CriticalFiniteHorizon.lean:19:0: Contract BlowupDensity.Tests.checkedCriticalFiniteHorizon: checked; standard logical axioms only
```

### Hygiene and scope

`rg -n 'sorry|admit|axiom|native_decide|maxHeartbeats' formalization/NSFormalization/Section4/I03/HomogeneousScaling.lean verification/Bindings/ScalingHomogeneous.lean`: no output, exit 1 (no matches).
`git diff --check`: no output, exit 0.
`git diff --name-only origin/erenup/integration...HEAD`:
```text
formalization/NSFormalization/Section4/I03/HomogeneousScaling.lean
research/I03/ATTEMPTS_HOMOGENEOUS.md
research/I03/COMPARISON.md
research/I03/REPORT_250.md
research/I03/axioms_homogeneous_scaling.lean
research/I03/packet_homogeneous_example.lean
verification/Bindings/ScalingHomogeneous.lean
```

Reviewer additions are only this report and the authorized rev250 exponent probe. Lane Lean, records, index, commits and refs were not modified.

