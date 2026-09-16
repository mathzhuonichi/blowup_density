ACCEPT

## 1. What the lane claims

Reviewed HEAD `9073b3f030d072ed58be8eb935ab6ceef2017fd3` against local `origin/erenup/integration` `37a1199b5b3e1a81d507345c85fcd22ba8119f35`. No fetch or git mutation was performed. Read CLAUDE.md, the lane-review skill, NEXT_SESSION.md, HANDOFF §0, the first 40 LESSONS lines, the brief, REPORT, ATTEMPTS, COMPARISON, RECONCILIATION and Spec.

The claim is conditional Theorem 4.7, with precisely `CompactHomogeneousRealization` as the additional input, not unconditional closure (research/R47/REPORT_258.md:5, :32). The report also claims a full family constructor, five norm helpers, standard axioms, and zero-data examples for zero and one grids (REPORT_258.md:13, :19).

## 2. What is in Lean

1. **Statement fidelity: pass.** Both structure bodies are byte-identical to research/R47/Spec.lean:37 and :169; the final theorem at verification/Bindings/GridAssembly.lean:305 has the token-identical choose conclusion of Spec.lean:176. The helper constructor exists at GridAssembly.lean:199. The five norm theorems exist at verification/Bindings/GridAssemblyNorms.lean:12, :20, :45, :83 and :122. The audit at research/R47/axioms_assembly.lean:8 checks all seven implementation declarations and its API conformance example is at :33.

2. **Field-by-field assembly: pass.** The following cites use GA = verification/Bindings/GridAssembly.lean and GN = verification/Bindings/GridAssemblyNorms.lean.

| Fields | Spec location | Implementation and checked supplier |
|---|---|---|
| center, radius, radius_pos, containingCell | Spec.lean:43, :47, :50, :56 | GA:206, :252; Bindings/GridLemmas.lean:35 chooses one ball after all grids |
| ε₀, eps_pos, force, solution | Spec.lean:61, :65, :70, :76 | GA:217, :227, :256; Bindings/InsertionLifespan.lean:319 supplies both exact velocity and pressure |
| force_mem | Spec.lean:81 | GA:271; Bindings/InsertionLifespan.lean:161 |
| history | Spec.lean:88 | GA:273; Contracts/V1/InsertionFamily.lean:224 |
| forceDifference_compact | Spec.lean:94 | GA:276; Contracts/V1/InsertionFamily.lean:265 |
| velocity_observations | Spec.lean:101 | GA:278; Bindings/ForceCellIntegral.lean:183 |
| force_observations | Spec.lean:109 | GA:282; Bindings/FluxCancellation.lean:289, with the required MemForceR input |
| lifespan | Spec.lean:117 | GA:285; Bindings/InsertionLifespan.lean:228 gives equality, not just a bound |
| energy_convergence | Spec.lean:123 | GA:287; Bindings/MainThresholds.lean:65 squeezes the registered energyRate |
| force_convergence | Spec.lean:133 | GA:228, :238, :241, :291; GN:83 and :122, plus R42 forceConvergence |
| velocity_support | Spec.lean:142 | GA:294; Contracts/V1/InsertionFamily.lean:231 |
| pressure_support | Spec.lean:151 | GA:297 chooses one zero gauge before all times; Contracts/V1/InsertionFamily.lean:255 |
| force_support | Spec.lean:160 | GA:301; Contracts/V1/InsertionFamily.lean:270, full spacetime support |

The cited manuscript was opened with sed: paper/sections/04-whole-space.tex:297–330 requires precisely simultaneous observations on [0,T), exact lifespan, both limits and a common support ball; :32–42 supplies the inherited history and compact difference; :221–228 specifies the three literal force norms. The plain ball containment follows the binding reconciliation, rather than adding the proof's closure/interior strengthening (research/R47/RECONCILIATION.md:12).

3. **Same reference and same ball: pass.** Bindings/InsertionFromData.lean:102 fixes radius 1 and center 0; GA:211 instead invokes the genuine arbitrary-ball constructor Bindings/Correction.lean:142, then GA:215 uses the supplied reference directly. This avoids both an extra ball hypothesis and unnecessary uniqueness transport. GA:217–226 clamps inadmissible scales to a positive admissible scale; GA:250 and :287–293 preserve both limits. This matches the total-family requirement in Spec.lean:70–76.

4. **Non-vacuity and honest hypotheses: pass within the authorized conditional scope.** GA:200 retains the unused `_ha` because it is part of the exact requested statement; it imposes no new restriction. The actual reference, positive T, positive radius and positive ε₀ are used. Observation intervals include zero and admissible scales are inhabited. The stronger supplier inequality in Bindings/InsertionLifespan.lean:324 makes the history window positive. The norm limits remain ENNReal-valued (Contracts/V1/Data.lean:251, :475); no infinite norm is converted to real zero in this lane. The inherited homogeneous conversion explicitly requires finiteness (Bindings/ScalingHomogeneous.lean:118, :123, :130; :202 supplies it). Grid observations use registered positive-width Cartesian grids (Contracts/V1/Data.lean:766, :783), and their suppliers prove actual integral cancellation with integrability (Bindings/ForceCellIntegral.lean:183, :204).

The sole extra predicate is exactly Bindings/ScalingHomogeneous.lean:27: a.e. strong time measurability of the explicit compact homogeneous datum path, for -3/2 < s < 0 and arbitrary smooth compact F. It contains no requested R47 conclusion, no empty time interval and no zero-only restriction. Its use is isolated to GN:45 and :122, then GA:236. This review does not purport to prove that universal input. Both authorized conditional non-vacuity examples, with ν=T=δ=1 and a=g=0, compile at axioms_assembly.lean:17 and :25.

5. **Hygiene and coverage: pass.** No forbidden proof token or heartbeat override in either new implementation module; the audit's `#print axioms` commands are audits, not axiom declarations. All seven audits print exactly the required list. The three-dot diff lists only two added implementation modules, the added audit/report/attempts and the expressly requested COMPARISON update; no existing Lean module, test, contract or Spec was modified. `git diff --check` is empty. The changed-module CI mechanism selects both modules (experiments/build_changed_lean.py:17; .github/workflows/contracts.yml:81).

6. **Substantive negative check: pass.** research/R47/probes/rev258_lifespan.lean:9 changes the main family's exact lifespan conclusion from `ENNReal.ofReal T` to `ENNReal.ofReal (T + 1)`, retaining the family, scale and admissibility argument. The original projection proof fails at :10 with the expected type mismatch below. This is a changed mathematical constant, not a missing-argument error.

## 3. Gaps

No blocking gap relative to the brief.

- The conditional measurability boundary is honestly reported (REPORT_258.md:32; COMPARISON.md:97). Whole-Section4 recursive searches for the predicate name, compactHomogeneousPath and homogeneous measurability found D01/HomogeneousWitness.lean:644, :656, :690: explicit slice construction and a norm identity still requiring the measurable-path hypothesis. R43/ForcePath.lean:58 provides a related map only for nonnegative order, so it does not discharge order -1. The predicate itself is defined in Bindings/ScalingHomogeneous.lean:27, explaining why searching Section4 for its exact name returns no definition.
- Whole-tree searches for mixedLebesgueENorm, order-zero Sobolev names and forceSobolevENorm found useful ingredients, including D01/OrderZeroDatum.lean:103 and A01/DatumPathContinuity.lean:103. These are realization/continuous-linear-map facts, not the claimed general equality between the two registered time norms. No exact bridge was located. The report's narrower claim that this lane does not supply that bridge is correct (COMPARISON.md:105); GN:83 makes it unnecessary here.
- Ordinary Lake build output is not literally empty: it replays existing dependency warnings and prints completion. Neither new module emits diagnostics, both direct checks emit zero output, and REPORT_258.md:42 already discloses this. This satisfies the review brief's “silent for this module” criterion.
- The global architecture report prints pre-existing copied-source admissions and source_hashes_match=false. Its exit status is zero; the new module's transitive axiom audit is independently clean. These global diagnostics are not evidence of an admission in the reviewed dependency closure.

Required fixes: none.

## 4. Commands and results

Environment: sourced `. scripts/lean-env.sh`; LEAN_NUM_THREADS=6; all direct lake commands ran from verification/. Existing package symlink was verified, so no installer or dependency-state reset was needed. Gates ran serially. Only the permitted probe and this new review file were written.

Large outputs below are exact head/tail excerpts (at most 40 lines each), explicitly marked where abbreviated, following logs/LESSONS.md's warning against pasting enormous contract JSON dumps. Empty outputs are explicitly identified. All requested gates were actually rerun; they are not inferred from worker logs.


Command: `cd verification && LEAN_NUM_THREADS=6 lake build Bindings.GridAssembly` — exit 0

```text
⚠ [8778/8981] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9876/10618] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9877/10618] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10272/10618] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:30: Variable name `hB` is not explicitly referenced.
[... middle output omitted ...]
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10571/10618] Replayed NSFormalization.Source.RieszL2Fourier
warning: NSFormalization/Source/RieszL2Fourier.lean:31:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [10572/10618] Replayed NSFormalization.Source.FractionalRealization
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
Build completed successfully (10618 jobs).
```

Command: `cd verification && LEAN_NUM_THREADS=6 lake env lean Bindings/GridAssembly.lean` — exit 0

```text
(zero output)
```

Command: `cd verification && LEAN_NUM_THREADS=6 lake env lean Bindings/GridAssemblyNorms.lean` — exit 0

```text
(zero output)
```

Command: `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R47/axioms_assembly.lean` — exit 0

```text
'BlowupDensity.Bindings.grid_power_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.grid_mixed_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.grid_homogeneous_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.grid_mixed_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.grid_homogeneous_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.rGridFamily_of_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.rGrid_choose_of_realization' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Command: `LEAN_NUM_THREADS=6 make check` — exit 0

```text
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
Warning: truncated output (original token count: 346170)
... 336103 bytes omitted ...

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
[... middle output omitted ...]
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
Ran 13 tests in 0.043s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

Command: `LEAN_NUM_THREADS=6 make test` — exit 0

```text
lake -d verification test
⚠ [8778/8813] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9875/10405] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9876/10405] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10271/10698] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR

Note: This linter can be disabled with `set_option linter.unusedVariables false`
[... middle output omitted ...]
ℹ [10645/10698] Replayed Tests.InsertionFamily
info: Tests/InsertionFamily.lean:19:0: Contract BlowupDensity.Tests.checkedInsertionFamily: checked; standard logical axioms only
ℹ [10649/10698] Replayed Tests.RegularityPartial
info: Tests/RegularityPartial.lean:17:0: Contract BlowupDensity.Tests.checkedRegularityPartial: checked; standard logical axioms only
ℹ [10657/10698] Replayed Tests.BochnerPartial
info: Tests/BochnerPartial.lean:14:0: Contract BlowupDensity.Tests.checkedBochnerPartial: checked; standard logical axioms only
ℹ [10658/10698] Replayed Tests.DatumLemmas
info: Tests/DatumLemmas.lean:14:0: Contract BlowupDensity.Tests.checkedDatumLemmas: checked; standard logical axioms only
ℹ [10660/10698] Replayed Tests.BoundedRepresentative
info: Tests/BoundedRepresentative.lean:14:0: Contract BlowupDensity.Tests.checkedBoundedRepresentative: checked; standard logical axioms only
ℹ [10663/10698] Replayed Tests.CorrectionV2
info: Tests/CorrectionV2.lean:28:0: Contract BlowupDensity.Tests.checkedCorrectionV2: checked; standard logical axioms only
ℹ [10674/10698] Replayed Tests.HomogeneousPartial
info: Tests/HomogeneousPartial.lean:15:0: Contract BlowupDensity.Tests.checkedHomogeneousPartial: checked; standard logical axioms only
ℹ [10675/10698] Replayed Tests.GradientL6
info: Tests/GradientL6.lean:13:0: Contract BlowupDensity.Tests.checkedGradientL6: checked; standard logical axioms only
ℹ [10678/10698] Replayed Tests.GradientL6V2
info: Tests/GradientL6V2.lean:22:0: Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
ℹ [10681/10698] Replayed Tests.EnergyHighPartialV2
info: Tests/EnergyHighPartialV2.lean:30:0: Contract BlowupDensity.Tests.checkedEnergyHighPartialV2: checked; standard logical axioms only
ℹ [10684/10698] Replayed Tests.DatumLemmasV3
info: Tests/DatumLemmasV3.lean:31:0: Contract BlowupDensity.Tests.checkedDatumLemmasV3: checked; standard logical axioms only
ℹ [10685/10698] Replayed Tests.Correction
info: Tests/Correction.lean:19:0: Contract BlowupDensity.Tests.checkedCorrection: checked; standard logical axioms only
ℹ [10686/10698] Replayed Tests.MaximalPartial
info: Tests/MaximalPartial.lean:16:0: Contract BlowupDensity.Tests.checkedMaximalPartial: checked; standard logical axioms only
ℹ [10687/10698] Replayed Tests.Uniqueness
info: Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only
ℹ [10688/10698] Replayed Tests.HomogeneousNorm
info: Tests/HomogeneousNorm.lean:17:0: Contract BlowupDensity.Tests.checkedHomogeneousNorm: checked; standard logical axioms only
ℹ [10693/10698] Replayed Tests.HomogeneousPartialV2
info: Tests/HomogeneousPartialV2.lean:35:0: Contract BlowupDensity.Tests.checkedHomogeneousPartialV2: checked; standard logical axioms only
ℹ [10695/10698] Replayed Tests.MaximalPartialV2
info: Tests/MaximalPartialV2.lean:24:0: Contract BlowupDensity.Tests.checkedMaximalPartialV2: checked; standard logical axioms only
ℹ [10696/10698] Replayed Tests.InsertionLifespanV2
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
ℹ [10697/10698] Replayed Tests.TameProduct
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
ℹ [10698/10698] Replayed Tests.MainThresholds
info: Tests/MainThresholds.lean:15:0: Contract BlowupDensity.Tests.checkedMainThresholds: checked; standard logical axioms only
```

Command: `LEAN_NUM_THREADS=6 scripts/gates.sh Bindings.GridAssembly` — exit 0

```text
== make check
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
Warning: truncated output (original token count: 346849)
... 338819 bytes omitted ...

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
[... middle output omitted ...]
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartial.lean:15:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartial: checked; standard logical axioms only
info: Tests/Packet.lean:14:0: Contract BlowupDensity.Tests.checkedPacket: checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartialV3.lean:41:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV3: checked; standard logical axioms only
info: Tests/DatumLemmasV2.lean:23:0: Contract BlowupDensity.Tests.checkedDatumLemmasV2: checked; standard logical axioms only
info: Tests/CriticalRegularity.lean:20:0: Contract BlowupDensity.Tests.checkedCriticalRegularity: checked; standard logical axioms only
info: Tests/EnergyHighPartial.lean:17:0: Contract BlowupDensity.Tests.checkedEnergyHighPartial: checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartialV2.lean:32:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV2: checked; standard logical axioms only
info: Tests/InsertionLifespan.lean:24:0: Contract BlowupDensity.Tests.checkedInsertionLifespan: checked; standard logical axioms only
info: Tests/CriticalFiniteHorizon.lean:19:0: Contract BlowupDensity.Tests.checkedCriticalFiniteHorizon: checked; standard logical axioms only
info: Tests/InsertionFamily.lean:19:0: Contract BlowupDensity.Tests.checkedInsertionFamily: checked; standard logical axioms only
info: Tests/RegularityPartial.lean:17:0: Contract BlowupDensity.Tests.checkedRegularityPartial: checked; standard logical axioms only
info: Tests/BochnerPartial.lean:14:0: Contract BlowupDensity.Tests.checkedBochnerPartial: checked; standard logical axioms only
info: Tests/DatumLemmas.lean:14:0: Contract BlowupDensity.Tests.checkedDatumLemmas: checked; standard logical axioms only
info: Tests/BoundedRepresentative.lean:14:0: Contract BlowupDensity.Tests.checkedBoundedRepresentative: checked; standard logical axioms only
info: Tests/CorrectionV2.lean:28:0: Contract BlowupDensity.Tests.checkedCorrectionV2: checked; standard logical axioms only
info: Tests/HomogeneousPartial.lean:15:0: Contract BlowupDensity.Tests.checkedHomogeneousPartial: checked; standard logical axioms only
info: Tests/GradientL6.lean:13:0: Contract BlowupDensity.Tests.checkedGradientL6: checked; standard logical axioms only
info: Tests/GradientL6V2.lean:22:0: Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
info: Tests/EnergyHighPartialV2.lean:30:0: Contract BlowupDensity.Tests.checkedEnergyHighPartialV2: checked; standard logical axioms only
info: Tests/DatumLemmasV3.lean:31:0: Contract BlowupDensity.Tests.checkedDatumLemmasV3: checked; standard logical axioms only
info: Tests/Correction.lean:19:0: Contract BlowupDensity.Tests.checkedCorrection: checked; standard logical axioms only
info: Tests/MaximalPartial.lean:16:0: Contract BlowupDensity.Tests.checkedMaximalPartial: checked; standard logical axioms only
info: Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only
info: Tests/HomogeneousNorm.lean:17:0: Contract BlowupDensity.Tests.checkedHomogeneousNorm: checked; standard logical axioms only
info: Tests/HomogeneousPartialV2.lean:35:0: Contract BlowupDensity.Tests.checkedHomogeneousPartialV2: checked; standard logical axioms only
info: Tests/MaximalPartialV2.lean:24:0: Contract BlowupDensity.Tests.checkedMaximalPartialV2: checked; standard logical axioms only
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
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

Command: `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` — exit 0

```text
Warning: truncated output (original token count: 346102)
... 335831 bytes omitted ...

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
[... middle output omitted ...]
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

Negative probe: `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R47/probes/rev258_lifespan.lean` — expected exit 1.

```text
../research/R47/probes/rev258_lifespan.lean:10:2: error: Type mismatch
  F.lifespan ε hε
has type
  maximalLifespanR ν a (F.force ε) = ENNReal.ofReal T
but is expected to have type
  maximalLifespanR ν a (F.force ε) = ENNReal.ofReal (T + 1)
```

Additional checks:

```text
Structure/text comparison:
RGridFamily byte-identical: True
RGridAPI byte-identical: True
choose token-identical: True

python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run
Changed Lean modules: Bindings.GridAssembly, Bindings.GridAssemblyNorms

git diff --name-status origin/erenup/integration...HEAD
A research/R47/ATTEMPTS_ASSEMBLY.md
M research/R47/COMPARISON.md
A research/R47/REPORT_258.md
A research/R47/axioms_assembly.lean
A verification/Bindings/GridAssembly.lean
A verification/Bindings/GridAssemblyNorms.lean

git diff --check
(zero output)
```

Search commands (read-only; matches assessed in parts 2–3):

```sh
rg -n 'sorry|admit|\baxiom\b|native_decide|maxHeartbeats|toReal' verification/Bindings/GridAssembly*.lean
grep -rnE 'CompactHomogeneousRealization|mixedLebesgueENorm|forceSobolevENorm.*0|forceSobolevENorm_zero' formalization/NSFormalization/Section4
grep -rnE 'compactHomogeneousPath|[Hh]omogeneous.*[Mm]easurable|[Mm]easurable.*[Hh]omogeneous|[Ss]obolev.*[Zz]ero|[Zz]ero.*[Ss]obolev' formalization/NSFormalization/Section4
```

The broad hygiene search only matches the English substring “admit” in “admits” at GridAssembly.lean:173; no forbidden Lean command is present.

Verdict: ACCEPT. Fixes: none.

