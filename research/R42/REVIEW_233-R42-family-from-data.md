ACCEPT

## 1. What the lane claims

Reviewed HEAD `adce3327fa3b99512335b40a9a8a812a780ea958`. Read CLAUDE.md, lane-review/SKILL.md, the first 40 LESSONS lines, HANDOFF §0/P10, the fallback worker response and research/R41D/REPORT_233.md (the requested R42 report does not exist), Spec and reconciliation.

The report claims unconditional closure of G1, exact alignment of a/g/T, same-record lifespan/convergence projections, and two concrete non-vacuity witnesses (research/R41D/REPORT_233.md:5,14,18). All are present.

## 2. What is in Lean

1. **Statement fidelity: pass.** verification/Bindings/InsertionFromData.lean:87-94 has exactly the brief's universal quantifier order, positive viscosity/time, initial-class and force membership, strict ENNReal lifespan premise, and existential registered PacketAPI / fully qualified V2 insertion record with all three equalities. No supplier premise is added. The result matches research/R41D/COMPARISON.md:64 and supplies the object in research/R41D/Spec.lean:96. Read the paper with `sed -n '7,70p'` and `sed -n '170,195p'`: the second density arm at paper/sections/04-whole-space.tex:177 calls precisely for this construction; insertion at :32-43 supplies its conclusions. Choosing the unit ball is legitimate for G1, which does not prescribe a ball.

2. **Supply chain: pass.** verification/Bindings/InsertionFromData.lean:96-110 uses the actual registered constructors, not mirrored structures. verification/Bindings/MaximalPartial.lean:195-205 implements strict-lifespan selection; formalization/NSFormalization/Section4/A02/Order.lean:124,135,152 explicitly realizes and halves the margin. The selected strict inequality is retained at the longer horizon. verification/Bindings/Correction.lean:142 accepts exactly open-slab smoothness/divergence/momentum, obtained by restriction from the contract solution. verification/Bindings/Scaling.lean:696 preserves the correction. verification/Bindings/InsertionFamily.lean:189 preserves a and the reference; verification/Bindings/InsertionLifespanV2.lean:81 accepts force membership and regularity through T+margin and retains that family. These cited declarations were opened, not inferred from their names.

3. **Projections and mathematics: pass.** verification/Bindings/InsertionFromData.lean:113-118 gives exact original-data lifespan for epsilon in (0,epsilon0]; :121-131 gives the same force family's full-time ENNReal-norm convergence. Contracts/V1/Thresholds.lean:12-16 fixes the exponent to 2/q-3/2-s, so q=1,2 gives the paper's strict thresholds. Contracts/V1/InsertionLifespan.lean:108-137 and Contracts/V2/InsertionLifespan.lean:117-158 retain admissibility, longer regularity, lifespan, full solution, maximality and blowup. No norm is converted using top.toReal; q.toReal is safe because q is 1 or 2.

4. **Non-vacuity: pass.** research/R41D/axioms_insertion_from_data.lean:17-26 instantiates nu=T=1 and a=g=0 using a horizon-two solution; :31-38 chooses epsilon=epsilon0>0 and obtains actual inserted lifespan one. The source witnesses are formalization/NSFormalization/Section4/A04/ZeroSolution.lean:71,80,93. All six audited declarations compile with exactly the required three axioms. The unused `_ha` at InsertionFromData.lean:95 is honest redundancy, not a vacuity trick: the strict positive lifespan selects an actual solution, with its initial field and Sobolev/divergence data (Contracts/V1/Data.lean:624-658). T and delta are positive, and the epsilon range has an explicit member.

5. **Hygiene and CI: pass.** No forbidden proof tokens or heartbeat overrides in either new Lean deliverable. The three-dot diff contains four new files plus the explicitly requested COMPARISON.md update; no existing Lean module, contract or test changed. Packet assembly at InsertionFromData.lean:37-84 matches the existing witness assembly at verification/Bindings/Packet.lean:108. The standalone new binding is covered by experiments/build_changed_lean.py:17-20,37 and .github/workflows/contracts.yml:77-81; it is not claimed to be in the registered test closure.

## 3. Gaps

No mathematical G1 gap or named hypothesis remains.

The report's disclosed import limitation is real: verification/Bindings/Packet.lean:65 and verification/Bindings/Scaling.lean:58 declare the same fully qualified bridge name. The local packet assembly avoids importing Packet; a downstream file must not jointly import this module and Bindings.Packet until that pre-existing collision is repaired. This is already accurately documented at research/R41D/REPORT_233.md:25-29 and is not a blocking fix under this lane's new-files-only scope.

The lane makes no new “missing lemma” claim. For completeness, searched the **entire** formalization/NSFormalization/Section4 tree for the untouched comparison's G2–G5 shapes using:
```sh
grep -rnE 'MemForceRapid|memForceRapid|initialClassSchwartz|forceSobolevENorm_zero|forceSobolevENorm.*zero' formalization/NSFormalization/Section4
grep -rnEi 'rapid|schwartz.*(initial|class)|force.*(norm.*zero|zero.*norm)' formalization/NSFormalization/Section4
```
The first search returned no matches; the broader search found only B02/LebesgueDatum.lean:344, A04/NonlinearDatum.lean:44, A04/ZeroSolution.lean:18 and D01/SmoothDatum.lean:102, none supplying the missing full force-norm/class interfaces. These searches support no additional G1 obligation; they are not a claim of mathematical impossibility elsewhere.

**Negative checks: pass.** Two probes preserve all hypotheses and proof arguments while changing a mathematical constant. research/R42/probes/rev233_shift_main.lean:13 changes the main G1 alignment to family.T=T+1; the original assembly fails at :29. research/R42/probes/rev233_shift_lifespan.lean:10 changes the exact lifespan conclusion to ofReal(T+1); the original projection proof fails at :11. These are substantive mutations, not argument deletion.

Required fixes: none. No lane code/records or git state were modified by the reviewer; only the authorized new review/probe files were written.

## 4. Commands and results

All Lean commands sourced scripts/lean-env.sh and used LEAN_NUM_THREADS=6. Direct Lake commands ran in verification/; make test uses the repository recipe `lake -d verification test`. The existing shared package symlink was verified; reinstalling was unnecessary for this read-only review. Lake calls were sequential.

- `lake build Bindings.InsertionFromData`: exit 0. Correct target follows the library/module convention (not the Lean declaration namespace). No diagnostic from this module. Dependency warnings are replayed, so the whole command is not literally silent. Exact final line:
```text
Build completed successfully (10004 jobs).
```
- Direct elaboration and main mutation, exact output:
```text
COMMAND: lake env lean Bindings/InsertionFromData.lean EXIT: 0 BYTES: 0
COMMAND: lake env lean ../research/R42/probes/rev233_shift_main.lean EXIT: 1 BYTES: 274
../research/R42/probes/rev233_shift_main.lean:29:78: error: Application type mismatch: The argument
  rfl
has type
  ?m.273 = ?m.273
but is expected to have type
  (InsertionLifespan.insertionLifespanV2API F hg hregLong).family.T = T + 1
in the application
  ⟨rfl, rfl⟩
```
- `lake env lean ../research/R41D/axioms_insertion_from_data.lean`: exit 0, exact output:
```text
'BlowupDensity.Bindings.insertionFromData_packet' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.insertionLifespanV2_of_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.insertionFromData_lifespan' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.insertionFromData_forceConvergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.InsertionFromDataAudit.zero_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.InsertionFromDataAudit.zero_inserted_lifespan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
- `lake env lean ../research/R42/probes/rev233_shift_lifespan.lean`: expected exit 1, exact output:
```text
../research/R42/probes/rev233_shift_lifespan.lean:11:2: error: Type mismatch: After simplification, term
  L.lifespan ε hε
 has type
  maximalLifespanR ν a (L.family.force ε) = ENNReal.ofReal T
but is expected to have type
  maximalLifespanR ν a (L.family.force ε) = ENNReal.ofReal (T + 1)
```
- `git diff --check`: exit 0, no output.
- Forbidden-token/heartbeat search of both new deliverables: no matches.
- `git diff --name-only origin/erenup/integration...HEAD`, exact output:
```text
research/R41D/ATTEMPTS_G1.md
research/R41D/COMPARISON.md
research/R41D/REPORT_233.md
research/R41D/axioms_insertion_from_data.lean
verification/Bindings/InsertionFromData.lean
```

Below are exact head/tail excerpts (35 lines each for long outputs, following LESSONS.md's instruction against pasting 30,000-line JSON), with exit statuses. make check's copied-source admission warning and source_hashes_match=false are pre-existing whole-tree diagnostics; they do not occur in this module's axiom closure. scripts/gates.sh includes test-mutations and compatibility; make test was also run independently because the script filters its output.

```text
COMMAND: make check EXIT: 0 LINES: 30031
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 543,
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
[middle output omitted]
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
.............
----------------------------------------------------------------------
Ran 13 tests in 0.042s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
COMMAND: make test EXIT: 0 LINES: 360
lake -d verification test
⚠ [8778/9365] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9875/10529] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9876/10529] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10271/10680] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.
[middle output omitted]
info: Tests/BochnerPartial.lean:14:0: Contract BlowupDensity.Tests.checkedBochnerPartial: checked; standard logical axioms only
ℹ [10638/10680] Replayed Tests.DatumLemmas
info: Tests/DatumLemmas.lean:14:0: Contract BlowupDensity.Tests.checkedDatumLemmas: checked; standard logical axioms only
ℹ [10640/10680] Replayed Tests.BoundedRepresentative
info: Tests/BoundedRepresentative.lean:14:0: Contract BlowupDensity.Tests.checkedBoundedRepresentative: checked; standard logical axioms only
ℹ [10643/10680] Replayed Tests.CorrectionV2
info: Tests/CorrectionV2.lean:28:0: Contract BlowupDensity.Tests.checkedCorrectionV2: checked; standard logical axioms only
ℹ [10654/10680] Replayed Tests.HomogeneousPartial
info: Tests/HomogeneousPartial.lean:15:0: Contract BlowupDensity.Tests.checkedHomogeneousPartial: checked; standard logical axioms only
ℹ [10655/10680] Replayed Tests.GradientL6
info: Tests/GradientL6.lean:13:0: Contract BlowupDensity.Tests.checkedGradientL6: checked; standard logical axioms only
ℹ [10658/10680] Replayed Tests.GradientL6V2
info: Tests/GradientL6V2.lean:22:0: Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
ℹ [10661/10680] Replayed Tests.EnergyHighPartialV2
info: Tests/EnergyHighPartialV2.lean:30:0: Contract BlowupDensity.Tests.checkedEnergyHighPartialV2: checked; standard logical axioms only
ℹ [10664/10680] Replayed Tests.DatumLemmasV3
info: Tests/DatumLemmasV3.lean:31:0: Contract BlowupDensity.Tests.checkedDatumLemmasV3: checked; standard logical axioms only
ℹ [10665/10680] Replayed Tests.Correction
info: Tests/Correction.lean:19:0: Contract BlowupDensity.Tests.checkedCorrection: checked; standard logical axioms only
ℹ [10666/10680] Replayed Tests.MaximalPartial
info: Tests/MaximalPartial.lean:16:0: Contract BlowupDensity.Tests.checkedMaximalPartial: checked; standard logical axioms only
ℹ [10667/10680] Replayed Tests.Uniqueness
info: Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only
ℹ [10668/10680] Replayed Tests.HomogeneousNorm
info: Tests/HomogeneousNorm.lean:17:0: Contract BlowupDensity.Tests.checkedHomogeneousNorm: checked; standard logical axioms only
ℹ [10673/10680] Replayed Tests.HomogeneousPartialV2
info: Tests/HomogeneousPartialV2.lean:35:0: Contract BlowupDensity.Tests.checkedHomogeneousPartialV2: checked; standard logical axioms only
ℹ [10675/10680] Replayed Tests.MaximalPartialV2
info: Tests/MaximalPartialV2.lean:24:0: Contract BlowupDensity.Tests.checkedMaximalPartialV2: checked; standard logical axioms only
ℹ [10678/10680] Replayed Tests.InsertionLifespanV2
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
ℹ [10679/10680] Replayed Tests.TameProduct
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
ℹ [10680/10680] Replayed Tests.CriticalRegularity
info: Tests/CriticalRegularity.lean:20:0: Contract BlowupDensity.Tests.checkedCriticalRegularity: checked; standard logical axioms only
COMMAND: scripts/gates.sh Bindings.InsertionFromData EXIT: 0 LINES: 30179
== make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 543,
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
[middle output omitted]
info: Tests/Packet.lean:14:0: Contract BlowupDensity.Tests.checkedPacket: checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartialV3.lean:41:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV3: checked; standard logical axioms only
info: Tests/DatumLemmasV2.lean:23:0: Contract BlowupDensity.Tests.checkedDatumLemmasV2: checked; standard logical axioms only
info: Tests/EnergyHighPartial.lean:17:0: Contract BlowupDensity.Tests.checkedEnergyHighPartial: checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartialV2.lean:32:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV2: checked; standard logical axioms only
info: Tests/InsertionLifespan.lean:24:0: Contract BlowupDensity.Tests.checkedInsertionLifespan: checked; standard logical axioms only
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
info: Tests/CriticalRegularity.lean:20:0: Contract BlowupDensity.Tests.checkedCriticalRegularity: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
COMMAND: check_contracts base EXIT: 0 LINES: 29999
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
[middle output omitted]
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
      "Tests.CriticalRegularity"
    ]
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

