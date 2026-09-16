ACCEPT-WITH-NOTES

## 1. What the lane claims

Review of commit `31aa4ca`, against the operative second fix, superseding the first review previously at this untracked report path. `research/A01/REPORT_189.md:5` claims the exact fix6 PressureSupply with no extra projector, residual-agreement, or endpoint-time premise; this is correct. The definition at `formalization/NSFormalization/Section4/A01/PressureRegularity.lean:362` is **byte-identical**, hence token-identical, to both `cca4af7` and the inspected lane-180 branch definition at `ConstructorAssembly.lean:365`. Binder order is hpairs then hpaths. The theorem at `PressureRegularity.lean:396` concludes precisely that definition, at line 421, with exactly its parameters.

The paper was opened with sed: `paper/sections/02-preliminaries.tex:75` gives the projected equation and complement pressure, and line 94 gives longitudinality and symmetric cross derivatives. Lines 22–26 and `paper/sections/appendix-a-local-theory.tex:71` explicitly allow one-sided initial-time derivatives. The revised Ioo momentum identity and Ico spatial regularity faithfully respect this distinction. No scalar pressure is assumed; `PressureGauge.lean:132` is not used circularly.

## 2. What is in Lean

Paths below abbreviate `formalization/NSFormalization/Section4/`.

1. **Exact supply / all conjuncts.** `A01/PressureRegularity.lean:428` obtains G, joint smoothness, and Icc slice equality from 194's `A01/ComplementPath.lean:649` (`exists_complement_joint_representative`). Lines 431–436 transport `complementCarrier_identity` (`ComplementPath.lean:327`) to a datum for G. The interior identity uses 195's **datum-level core**, `interior_momentum_identity_of_datums` (`A01/InteriorMomentum.lean:153`), rather than literally invoking `interior_momentum_identity_of_complement_paths` (`InteriorMomentum.lean:288`). This is a valid assembly of the same proof and avoids rechoosing its existential datum. The residual premise is discharged by 197's `residualDatum_jointRepresentative` (`A01/LerayBridge.lean:348`). The time datum is proved locally at `PressureRegularity.lean:443`, using `hprojected_of_cylinder''` (`LerayBridge.lean:459`), order-two lowering, `vectorRepresentative_ae`, and `jointRepresentative_temporalDerivative_of_cylinder` (`InteriorMomentum.lean:107`). The latter invokes `datumPath_hasDerivAt` at line 129. Thus the internal name htime is a **proved interior fact**, not the rejected external endpoint assumption. Lines 469–473 prove MemLp from the transported zero-order datum and spatial continuity (`memLp_of_isSobolevDatum_zero`, line 276), and symmetry from this lane's Helmholtz converse (line 258).

2. **Arbitrary representative.** `pressureGradientOfVelocity_eq_of_slices` at `PressureRegularity.lean:328` assumes only the two slab smoothness statements and slice a.e. equality. Lines 338–340 upgrade to whole-slice equality by continuity; lines 343–347 obtain eventual time equality on Ioo and hence equality of ambient fderiv there. Whole-slice equality also identifies all spatial derivatives. The final transport is at lines 465–468. No extension, scalar pressure, momentum, or endpoint derivative hypothesis is hidden here. Endpoint smoothness is used only to obtain spatial continuity there; the time argument uses an interior neighborhood.

3. **Time zero.** The complement datum is valid for every Icc time (`PressureRegularity.lean:431`), including zero. `D01.contDiff_slice` (`D01/DatumToJets.lean:366`, opened) proves smoothness of a spatial slice at every Ico time by composition with x ↦ (t,x); it takes no ambient time derivative. Consequently lines 470–473 apply at t=0 and give both L² and symmetry there. The retained endpoint regression `research/A01/probes/rev189_endpoint_htime.lean:18`–78 independently demonstrates why ambient temporal regularity may not be inferred at zero.

4. **Pipeline / non-vacuity.** `research/A01/probes/pressure_supply_pipeline.lean:1` imports the real CylinderWiring, JointRepresentative, and PressureRegularity modules. Its theorem (line 22) has only hb beyond positive viscosity/horizon, force regularity, smooth L² initial data and initial divergence-freeness. Lines 37–42 obtain the same U/pairs/paths from `cylinderPair_of_bounds`, select velocity via lane 190, and invoke the exact supply. Lines 75–102 prove the zero bound via quadratic mild uniqueness, treating the degenerate auxiliary interval separately. Lines 105–116 specialize ν=S=1 and radius zero, **without assuming hb**. Neither an empty final slab nor ENNReal.toReal is involved.

5. **Helmholtz converse and declarations.** The report's retained helpers exist: longitudinal complement (line 40), inverse angular transport (66), distributional antisymmetry equality (119), classical curl-free consequence (144), symmetric Jacobian (258), zero-order MemLp (276), representative datum transport (288), smooth complement representative (302), arbitrary-slice transport (328), supply definition (362), and assembly (396). The Fourier proof uses no derivative L² premise: compact support is on test functions, and continuity upgrades the distributional equality to pointwise equality (lines 175–253). All ten theorem audits in `research/A01/axioms_pressure_regularity.lean:17`–26 have exactly the three standard axioms. A supplementary probe audits the definition as well.

## 3. Gaps and exact fixes

**Required one-line hygiene fix:** `PressureRegularity.lean:395` currently says `set_option maxHeartbeats 800000 in`, violating the explicit ≤400000 requirement and lacking its required explanatory comment. Replace that line with:

```lean
set_option maxHeartbeats 400000 in -- Elaborate the cylinder, datum, and representative assembly.
```

The entire unchanged module with only 800000 replaced by 400000 was independently checked in `research/A01/probes/rev189_assembly_400k.lean`: exit 0, zero output. No proof redesign is needed. This is why the verdict is ACCEPT-WITH-NOTES rather than an unconditional ACCEPT.

No mathematical gap remains in this pressure supply. The report's only current absence claim is ConstructorAssembly on integration (`REPORT_189.md:11`). Recursive grep over all Section4, Source, and Paper1 confirms that the only local PressureSupply definition is this copy. The historical open obligations in `ATTEMPTS_PRESSURE_REGULARITY.md:39` are superseded by its second-fix section at line 68: the same whole-tree search finds 194's complement representative, 195's time derivative, and 197's projector/residual bridges. They must not be read as current blockers.

For the lead: once lane 180 lands, import its canonical PressureSupply definition, delete this copy, and supply `pressureSupply_of_pieces` to the constructor. That removes the PressureSupply obligation; it does not by itself remove the separate hb/energy-bound obligation.

Hygiene: no forbidden proof constructs in the lane module/audit/pipeline; no existing production module changed. The three-dot diff has only the new module plus lane records/probes and the requested A3_SPLIT record update. The two-dot diff additionally shows newer integration-only log rows absent in this older branch; these are **base advancement**, not lane deletions (absent from the three-dot diff). No verification/ file is changed, so the conditional scripts/gates.sh and explicit base-ref contract checker are not required by this brief. The build replays upstream warnings but emits none for this module; direct checking of the module is silent.

**Substantive negative mutation:** `rev189_assembly_endpoint_mutation.lean` changes the contract's pressure identity from Ioo to Ico, leaving every premise and the proof unchanged. It fails when ht : t ∈ Ico 0 S is supplied to the interior identity requiring Ioo. This directly exercises the endpoint distinction, not a dropped argument. Exact output follows.

## 4. Commands and results

All Lean commands source scripts/lean-env.sh, run Lake only from verification/, and set LEAN_NUM_THREADS=6. The pre-existing package symlink was verified; no installation, git mutation, or production edit was performed. Full command outputs follow (including verbose make check output, without truncation).

400000-heartbeat full-module probe: exit 0; output empty.
Definition comparison against cca4af7 and lane-180 branch: byte-identical=True; token-identical=True.


### lake build NSFormalization.Section4.A01.PressureRegularity

```text
⚠ [9811/10250] Replayed NSFormalization.Source.FiniteHilbertBochner
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
ℹ [10099/10250] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10106/10250] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [10109/10250] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10117/10250] Replayed NSFormalization.Source.RealSobolev
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
⚠ [10121/10250] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [10128/10250] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10142/10250] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10145/10250] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
⚠ [10149/10250] Replayed Formal.R3LerayFrequencySymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean:43:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10153/10250] Replayed Formal.R3StokesL2Operator
warning: ../vendor/HeliCorgi/Formal/R3StokesL2Operator.lean:111:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [10154/10250] Replayed Formal.R3L2ScalarAux
warning: ../vendor/HeliCorgi/Formal/R3L2ScalarAux.lean:26:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [10162/10250] Replayed Formal.FlowMapNonextendibilityCriterion
warning: ../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean:40:16: Variable name `ht0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ht0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean:40:30: Variable name `htT` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _htT

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean:43:16: Variable name `ht0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ht0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean:43:30: Variable name `htT` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _htT

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10163/10250] Replayed Formal.UniformRestartContinuation
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:36:16: Variable name `ht0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ht0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:36:30: Variable name `htT` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _htT

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:39:16: Variable name `ht0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ht0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:39:30: Variable name `htT` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _htT

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:95:0: Definition `FlowMapUniformRestartPackage.toContinuationPackage` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
⚠ [10164/10250] Replayed Formal.R3SobolevCarrier
warning: ../vendor/HeliCorgi/Formal/R3SobolevCarrier.lean:80:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10167/10250] Replayed Formal.R3CoordinateLinearAux
warning: ../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean:10:11: Variable name `x` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _x

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean:10:13: Variable name `y` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _y

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean:11:12: Variable name `c` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _c

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean:11:14: Variable name `x` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _x

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10170/10250] Replayed Formal.R3DivergencePointwise
warning: ../vendor/HeliCorgi/Formal/R3DivergencePointwise.lean:25:19: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10174/10250] Replayed Formal.R3LerayL2Operator
warning: ../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean:34:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: ../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean:61:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10175/10250] Replayed Formal.R3LerayFourierBridge
warning: ../vendor/HeliCorgi/Formal/R3LerayFourierBridge.lean:73:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10176/10250] Replayed Formal.R3LerayComplexFiberSymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
Build completed successfully (10250 jobs).

EXIT_CODE=0
OUTPUT_BYTES=11971
```

### lake env lean ../formalization/NSFormalization/Section4/A01/PressureRegularity.lean

```text

EXIT_CODE=0
OUTPUT_BYTES=0
```

### lake env lean ../research/A01/axioms_pressure_regularity.lean

```text
'NSFormalization.Section4.A01.lerayComplement_longitudinal' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.longitudinal_symm_of_longitudinal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.tempered_antisym_eq_of_fourier_longitudinal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.curl_free_of_orderZeroDatum_longitudinal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.hasSymmetricJacobian_of_lerayComplement_orderZeroDatum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.memLp_of_isSobolevDatum_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.pressureSupply_of_pieces' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.pressureGradientOfVelocity_eq_of_slices' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.carrierDatum_physicalSlice' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.exists_smooth_lerayComplement_representative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT_CODE=0
OUTPUT_BYTES=1281
```

### lake env lean ../research/A01/probes/pressure_supply_pipeline.lean

```text
'NSFormalization.Section4.A01.PressureSupplyProbe.pipeline' depends on axioms: [propext, Classical.choice, Quot.sound]

EXIT_CODE=0
OUTPUT_BYTES=119
```

### lake env lean ../research/A01/probes/rev189_endpoint_htime.lean

```text

EXIT_CODE=0
OUTPUT_BYTES=0
```

### lake env lean ../research/A01/probes/rev189_definition_axioms.lean

```text
'NSFormalization.Section4.A01.PressureSupply' depends on axioms: [propext, Classical.choice, Quot.sound]

EXIT_CODE=0
OUTPUT_BYTES=105
```

### lake env lean ../research/A01/probes/rev189_assembly_endpoint_mutation.lean

```text
../research/A01/probes/rev189_assembly_endpoint_mutation.lean:465:23: error: Application type mismatch: The argument
  ht
has type
  t ∈ Ico 0 S
but is expected to have type
  t ∈ Ioo 0 S
in the application
  hid htime t ht
../research/A01/probes/rev189_assembly_endpoint_mutation.lean:468:44: error: Application type mismatch: The argument
  ht
has type
  t ∈ Ico 0 S
but is expected to have type
  t ∈ Ioo 0 S
in the application
  pressureGradientOfVelocity_eq_of_slices ν f (jointRepresentative U hpaths) velocity hJ hc3
    (fun r hr =>
      Filter.EventuallyEq.trans (jointRepresentative_slice U hpaths ⟨r, ⟨hr.left, LT.lt.le hr.right⟩⟩)
        (Filter.EventuallyEq.symm (hslice ⟨r, ⟨hr.left, LT.lt.le hr.right⟩⟩)))
    t ht

EXIT_CODE=1
OUTPUT_BYTES=757
```

### make check

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 513,
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
… (make check output truncated by lead: 28,000+ lines of architecture JSON; exit 0; full text in tmp/codex/review_189-A01-pressure-regularity.log)
Ran 13 tests in 0.041s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.

EXIT_CODE=0
OUTPUT_BYTES=1159606
```

### git diff --check

```text

EXIT_CODE=0
OUTPUT_BYTES=0
```

### git diff --name-status origin/erenup/integration...HEAD

```text
A	formalization/NSFormalization/Section4/A01/PressureRegularity.lean
M	research/A01/A3_SPLIT.md
A	research/A01/ATTEMPTS_PRESSURE_REGULARITY.md
A	research/A01/REPORT_189.md
A	research/A01/axioms_pressure_regularity.lean
A	research/A01/probes/pressure_supply_pipeline.lean
A	research/A01/probes/rev189_endpoint_htime.lean

EXIT_CODE=0
OUTPUT_BYTES=320
```

### git diff origin/erenup/integration --stat

```text
 NEXT_SESSION.md                                    |   1 -
 PLAN.md                                            |   2 +-
 .../Section4/A01/PressureRegularity.lean           | 475 +++++++++++++++++++++
 logs/AGENT_RUNS.csv                                |   3 -
 logs/LESSONS.md                                    |   1 -
 research/A01/A3_SPLIT.md                           |   5 +-
 research/A01/ATTEMPTS_PRESSURE_REGULARITY.md       | 102 +++++
 research/A01/REPORT_189.md                         |  69 +++
 research/A01/axioms_pressure_regularity.lean       |  51 +++
 research/A01/probes/pressure_supply_pipeline.lean  | 118 +++++
 research/A01/probes/rev189_endpoint_htime.lean     |  78 ++++
 11 files changed, 898 insertions(+), 7 deletions(-)

EXIT_CODE=0
OUTPUT_BYTES=750
```

### Additional hygiene and probe results

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev189_assembly_400k.lean
EXIT_CODE=0
OUTPUT_BYTES=0

$ rg -n '\b(sorry|admit|axiom|native_decide)\b' formalization/NSFormalization/Section4/A01/PressureRegularity.lean research/A01/axioms_pressure_regularity.lean research/A01/probes/pressure_supply_pipeline.lean
(no matches; exit 1)

$ rg -n maxHeartbeats formalization/NSFormalization/Section4/A01/PressureRegularity.lean
395:set_option maxHeartbeats 800000 in

$ git diff --name-only origin/erenup/integration...HEAD -- verification
(no output; exit 0)
```

`make check` passed; the exact full output above includes all architecture and contract-policy results. All eleven production declarations (ten theorems and PressureSupply) have now been audited with exactly `[propext, Classical.choice, Quot.sound]`. The pipeline audit has the same list. Existing `rev189_mutation_Icc.lean` belongs to the superseded first implementation and was preserved, not used as evidence for this revision.

Required fix: replace `PressureRegularity.lean:395` with the commented 400000 setting shown in part 3. The pressure mathematics and all required applicable gates otherwise pass. No production or record fix was applied by this read-only reviewer.
