REJECT

## 1. What the lane claims

Reviewed lane HEAD `f8cc4fefe1cb80ad0dbc15ec6c3ac547a41e68bc`, read-only except this report and the two permitted `rev212_*.lean` probes. Read `CLAUDE.md`, `.claude/skills/lane-review/SKILL.md`, the first 40 lines of `logs/LESSONS.md`, the brief, `REPORT_212.md`, the requested specification and predecessor reports, and the cited paper passages with `sed -n`.

The lane claims a V2 extension of the frozen regularity API, a positive selected horizon and classical solution with all four regularity clauses, and exactly the owner-approved fixed-force H⁷ lower bound (`research/A01/REPORT_212.md:5`, `:17`, `:32`). It explicitly leaves the H¹/cross-force draft statement open (`research/A01/REPORT_212.md:63`). Those mathematical claims check out. The rejection is a current-base compatibility failure, not a failed Lean proof.

## 2. What is in Lean

- **Statement fidelity:** `verification/Contracts/V2/LocalTheory.lean:148` extends the actual V1 structure at `verification/Contracts/V1/RegularityPartial.lean:138`. The selected horizon/solution/regularity fields are at `:152`, `:156`, `:161`; they preserve the shapes at `research/A01/Spec.lean:277`. The bound at `verification/Contracts/V2/LocalTheory.lean:178` fixes `ν>0`, then `f` and its membership, then finite `K`, then chooses one real `δ>0`, then quantifies over the H⁷ datum ball. There is no extra analytic assumption or placeholder proposition field. The H¹ sentence is only a definition at `:190`, with the draft quantifiers at `research/A01/Spec.lean:338` (apart from qualifying the horizon by `api`).
- **Exact restatements:** programmatic comparison found `ManuscriptLocalRegularity` byte-identical, including its field comments, between `research/A01/Spec.lean:167` and `verification/Contracts/V2/LocalTheory.lean:79`. The bodies of `convectionDivergence`, `HasSymmetricJacobian`, and `IsLerayComplement` are byte-identical at contract lines `:56`, `:62`, `:69`. All four regularity clauses retain their quantifiers, signs, and intervals: smoothness and pressure recovery on `Ico`, projected momentum on `Ioo`, and pressure gauge on `Ico` (`:92`, `:109`, `:126`, `:139`). The accessors exist at `:201`, `:207`, `:213`.
- **Paper checked:** `paper/sections/appendix-a-local-theory.tex:60`–`:77` supplies the common-interval, all-order time regularity; `paper/sections/02-preliminaries.tex:81`, `:90`, `:96` supply the projected equation, pressure complement, and radial potential. The deliberate stronger force-class assumption is disclosed at contract `:153`; `Data.MemForceR` at `verification/Contracts/V1/Data.lean:544` includes global L¹/L² time membership. The H¹ versus H⁷ narrowing is real and owner-authorized; the documentation attribution correction below is still needed.
- **Binding:** the five existing ordinary-definition bridges are at `verification/Bindings/LocalTheoryV2.lean:33`, `:37`, `:41`, `:46`, `:50`. Full structure round trips at `:57` and `:64` use the genuine field-wise conversions `verification/Bindings/Uniqueness.lean:63` and `verification/Bindings/MaximalPartial.lean:73`. Regularity is transported field by field at `:72`; the registered record and V1 projection exist at `:93` and `:109`. The missing bridge for the separately copied H¹ predicate is a small completion item below.
- **Implementation witnesses opened:** `formalization/NSFormalization/Section4/A01/LocalTheoryBundle.lean:274`, `:305`, `:310`, `:342` supply precisely the horizon, carrier, regularity, and H⁷ bound used by the binding. The finite bound is used in `ENNReal.toReal_mono hK hbound` at `:357`, so this is not a `⊤.toReal = 0` loophole. `ClassicalSolutionR.horizon_pos` at `verification/Contracts/V1/Data.lean:630` rules out empty solution intervals. There are no unsupplied named hypotheses on the registered record.
- **Non-vacuity:** `research/A01/axioms_contract_v2.lean:65`, `:68` prove force membership/nonzero; `:105`, `:120`, `:128` prove datum membership/nonzero/finite H⁷ norm. Its two examples at `:136` and `:148` instantiate the actual registered fields at those same nonzero inputs and obtain a strictly positive real horizon and `δ`. These compiled in this review; no additional non-vacuity instance was needed. The force is supported near time 2, so this establishes the required global nonzero-force witness, not necessarily nonzero forcing during the selected short interval.
- **Downstream claims:** opened `formalization/NSFormalization/Section4/A04/RestartFixedForce.lean:15`, `:41` (one bound for all restart times in `Icc 0 S`), `:236` (Grönwall supplier), `formalization/NSFormalization/Section4/A04/ShiftedExtension.lean:229`, `:236`, `:247`, `:256` (gluing and unconditional fixed-force continuation), and `formalization/NSFormalization/Section4/A02/MaximalWiring.lean:14` (per-datum maximal existence). The V2 abstract field alone does not assert uniformity over shifted forces, and the lane correctly says so.
- **Tests and hygiene:** `verification/Tests/LocalTheoryV2.lean:23`, `:26`, `:34`, `:39`, `:46`, `:54`, `:63` check the witness, axioms, all public field types, H¹ definition, and V1 projection. All 16 declarations printed at `research/A01/axioms_contract_v2.lean:157` have exactly `[propext, Classical.choice, Quot.sound]`. Comment-stripped scans found no `sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats` in the four new Lean files. The intentionally invalid strings in `experiments/test_contract_mutations.py:30` and `:34` are negative harness fixtures, not imported axioms.
- **Change scope:** `git diff --name-status origin/erenup/integration...HEAD` shows only new Lean modules, with no existing Lean module or frozen test modified. Existing changes are records/registry and the permitted mutation harness. The registry adds 11 lines, and its serialization exactly equals `json.dumps(..., ensure_ascii=False, indent=2) + "\n"`. `collaboration/work_items.json:63`, `collaboration/tasks/A01.md:27`, and `collaboration/TASKS.md:13` contain the new ID. `git diff --check origin/erenup/integration...HEAD` passes.

## 3. Gaps and required fixes

1. **Blocking — moving integration baseline.** At review start, `origin/erenup/integration` was `02b8932036288084789d93004ce0398ca74c8ed1`: 32 registered contracts, all preserved, plus this lane's A01 entry = 33. The complete gates and explicit base check passed then. During this review another process advanced the ref to `3cca4264e4f7f86e556084d6b3cefeb1e77031ca`, adding `R46.completed_density`. This lane lacks that entry, and the current-base recheck below rejects it. The worker's 32→33 explanation (`research/A01/REPORT_212.md:78`) was accurate for the original base; it is now stale. **Fix:** have the worker/lead integrate the current baseline, preserve `R46.completed_density` alongside `A01.local_theory_v2`, regenerate task views, and rerun the gates and base checker; do not delete a registered contract to meet the obsolete count 30. No git state was changed by this reviewer.
2. **Minor — missing copied-definition bridge.** `verification/Contracts/V2/LocalTheory.lean:190` copies the implementation's open H¹ predicate (`formalization/NSFormalization/Section4/A01/LocalTheoryBundle.lean:372`), but `verification/Bindings/LocalTheoryV2.lean:30`–`:51` has no correspondence for it. The test at `verification/Tests/LocalTheoryV2.lean:54` repeats the contract expression rather than comparing to the implementation. Exact one-line addition in the binding namespace (verified by `research/A01/probes/rev212_h1_bridge.lean:4`): `theorem localTheoryV2_h1_eq : Contracts.V2.LocalTheory.ManuscriptHorizonLowerBoundH1 localTheoryV2 = NSFormalization.Section4.A01.ManuscriptHorizonLowerBoundH1 := rfl`. This proves equality of predicates, not the H¹ predicate.
3. **Minor — paper versus draft attribution.** `verification/Contracts/V2/LocalTheory.lean:20`, `:166` and `verification/contracts.json:364` attribute the cross-force L¹ formulation directly to Appendix A:147–150. Those paper lines actually describe one fixed force bounded into H¹ on `[0,S+1]`; the cross-force L¹ formulation is the draft's elaboration at `research/A01/Spec.lean:315`, `:338`. `research/A01/COMPARISON.md:351` already distinguishes them correctly. Replace each conflating sentence with: **“Appendix A:147–150 uses bounded H¹ restart data and a fixed force bounded into H¹ on [0,S+1]; Spec.lean:338–343 formulates the stronger cross-force H¹/L¹ bound, whereas V2 registers fixed-force H⁷ uniformity.”** Use “draft formulation of the manuscript's H¹ requirement” at contract `:183`–`:187` and comparison `:354` where exact identity is implied. No change to the owner-approved field is needed.
4. **Minor — ‘uninhabited’ overstates an open obligation.** At `research/A01/REPORT_212.md:67` and `verification/contracts.json:364`, replace **“uninhabited definition”** with **“unproved predicate”**. This lane proves neither the predicate nor its negation.

**Whole-tree gap search:** ran `grep -rnE 'HorizonLowerBoundH1|horizon_lower_bound|forced.*H¹|H¹.*(local|theory)|H1.*(local|horizon)|quantitative.*H1' formalization/NSFormalization/Section4`, then broadened to all local/horizon theorem names and `Restart`. Found the unproved definitions at `A01/HorizonUniform.lean:23`, `A01/LocalTheoryBundle.lean:372`, and `A04/Continuation.lean:101`; the actual quantitative suppliers are H⁷ at `A01/HorizonUniform.lean:82`, `:114`, `A01/LocalTheoryBundle.lean:342`, and `A04/RestartFixedForce.lean:41`. Opened their statements. No implementation of the draft H¹/cross-force obligation was found. Existing smooth persistence is not missing generally; the missing combination is an H¹-controlled forced local interval, persistence on that same interval, and compatible uniform horizon selection. Historical gaps in `REPORT_210.md` about absent `LocalSolution.lean` have since been filled and are not treated as current gaps.

**Substantive negative check:** `research/A01/probes/rev212_h1_mutation.lean:7` retains a positive control with the exact H⁷ field. The second example at `:15` changes only `sobolevENorm 7` to `sobolevENorm 1`, widening the datum ball without dropping an argument. Lean rejects line `:19` with the expected H⁷-versus-H¹ type mismatch, reproduced below. This demonstrates the current proof cannot silently supply the stronger field; it is not a disproof of H¹ local theory.

## 4. Commands and results

All Lean shells sourced `. scripts/lean-env.sh`, exported `LEAN_NUM_THREADS=6`, and ran Lake sequentially from `verification/`. The ordinary build also succeeded with replayed dependency warnings and the expected axiom-check message; the quiet/error build below is silent. Direct contract and binding checks are silent; the Tests module intentionally emits its single `checkAxioms` success message. Independently reran `lake test` because `scripts/gates.sh:11` masks a `make test` pipeline failure with `|| true`; that direct run succeeded too.

Outputs below are exact for short commands. For the 35,000-line registry/closure outputs and dependency-warning replay, only the first/last 40 lines are pasted, with explicit omission counts, following the report-size guidance in `logs/LESSONS.md:9`. No missing middle output is represented as a successful check; process exit codes are recorded separately. Current-base failures appear last.

`lake -q --log-level=error build Contracts.V2.LocalTheory Bindings.LocalTheoryV2 Tests.LocalTheoryV2` (cwd `verification`): exit 0.

```text
(zero output)
```

`lake env lean Contracts/V2/LocalTheory.lean` (cwd `verification`): exit 0.

```text
(zero output)
```

`lake env lean Bindings/LocalTheoryV2.lean` (cwd `verification`): exit 0.

```text
(zero output)
```

`lake env lean Tests/LocalTheoryV2.lean` (cwd `verification`): exit 0.

```text
Contract BlowupDensity.Tests.checkedLocalTheoryV2: checked; standard logical axioms only
```

`lake env lean ../research/A01/axioms_contract_v2.lean` (cwd `verification`): exit 0.

```text
'BlowupDensity.Bindings.localTheoryV2_convectionDivergence_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.localTheoryV2_hasSymmetricJacobian_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.localTheoryV2_isLerayComplement_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.localTheoryV2_pressurePotential_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.localTheoryV2_sobolevENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.localTheoryV2_toA02_ofA02' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.localTheoryV2_ofA02_toA02' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.localTheoryV2_regularity_ofA02' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.localTheoryV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.regularityPartial_of_v2' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedLocalTheoryV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane212AxiomAudit.nonzeroForce_memForceR' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane212AxiomAudit.nonzeroForce_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane212AxiomAudit.nonzeroDatum_mem_initialClassR' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane212AxiomAudit.nonzeroDatum_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane212AxiomAudit.nonzeroDatum_H7_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`make check` (cwd `.`): exit 0.

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 550,
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
  "registered_contracts": 33,
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
[... 35323 output lines omitted ...]
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
      "Tests.LocalTheoryV2"
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

`scripts/gates.sh` (cwd `.`): exit 0.

```text
== make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 550,
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
  "registered_contracts": 33,
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
[... 35369 output lines omitted ...]
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
info: Tests/LocalTheoryV2.lean:26:0: Contract BlowupDensity.Tests.checkedLocalTheoryV2: checked; standard logical axioms only
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

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration` (cwd `.`): exit 0.

```text
{
  "registered_contracts": 33,
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
[... 35291 output lines omitted ...]
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
      "Tests.LocalTheoryV2"
    ]
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

`git diff --stat verification/contracts.json` (cwd `.`): exit 0.

```text
(zero output)
```

`git diff --stat origin/erenup/integration...HEAD -- verification/contracts.json` (cwd `.`): exit 0.

```text
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

`lake env lean ../research/A01/probes/rev212_h1_mutation.lean` (cwd `verification`): exit 1.

```text
../research/A01/probes/rev212_h1_mutation.lean:19:2: error: Type mismatch
  checkedLocalTheoryV2.horizon_lower_bound
has type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ (f : SpaceTimeField),
        MemForceR f →
          ∀ (K : ℝ≥0∞),
            K ≠ ∞ → ∃ δ > 0, ∀ a ∈ initialClassR, sobolevENorm 7 a ≤ K → δ ≤ checkedLocalTheoryV2.horizon ν a f
but is expected to have type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ (f : SpaceTimeField),
        MemForceR f →
          ∀ (K : ℝ≥0∞),
            K ≠ ∞ → ∃ δ > 0, ∀ a ∈ initialClassR, sobolevENorm 1 a ≤ K → δ ≤ checkedLocalTheoryV2.horizon ν a f
```

`lake env lean ../research/A01/probes/rev212_h1_bridge.lean` (cwd `verification`): exit 0.

```text
(zero output)
```

`lake test` (cwd `verification`): exit 0.

```text
⚠ [8778/9259] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9875/10246] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9876/10246] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10271/10701] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:30: Variable name `hB` is not explicitly referenced.
[... 285 output lines omitted ...]
ℹ [10649/10701] Replayed Tests.RegularityPartial
info: Tests/RegularityPartial.lean:17:0: Contract BlowupDensity.Tests.checkedRegularityPartial: checked; standard logical axioms only
ℹ [10657/10701] Replayed Tests.BochnerPartial
info: Tests/BochnerPartial.lean:14:0: Contract BlowupDensity.Tests.checkedBochnerPartial: checked; standard logical axioms only
ℹ [10658/10701] Replayed Tests.DatumLemmas
info: Tests/DatumLemmas.lean:14:0: Contract BlowupDensity.Tests.checkedDatumLemmas: checked; standard logical axioms only
ℹ [10660/10701] Replayed Tests.BoundedRepresentative
info: Tests/BoundedRepresentative.lean:14:0: Contract BlowupDensity.Tests.checkedBoundedRepresentative: checked; standard logical axioms only
ℹ [10663/10701] Replayed Tests.CorrectionV2
info: Tests/CorrectionV2.lean:28:0: Contract BlowupDensity.Tests.checkedCorrectionV2: checked; standard logical axioms only
ℹ [10674/10701] Replayed Tests.HomogeneousPartial
info: Tests/HomogeneousPartial.lean:15:0: Contract BlowupDensity.Tests.checkedHomogeneousPartial: checked; standard logical axioms only
ℹ [10675/10701] Replayed Tests.GradientL6
info: Tests/GradientL6.lean:13:0: Contract BlowupDensity.Tests.checkedGradientL6: checked; standard logical axioms only
ℹ [10678/10701] Replayed Tests.GradientL6V2
info: Tests/GradientL6V2.lean:22:0: Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
ℹ [10681/10701] Replayed Tests.EnergyHighPartialV2
info: Tests/EnergyHighPartialV2.lean:30:0: Contract BlowupDensity.Tests.checkedEnergyHighPartialV2: checked; standard logical axioms only
ℹ [10684/10701] Replayed Tests.DatumLemmasV3
info: Tests/DatumLemmasV3.lean:31:0: Contract BlowupDensity.Tests.checkedDatumLemmasV3: checked; standard logical axioms only
ℹ [10687/10701] Replayed Tests.LocalTheoryV2
info: Tests/LocalTheoryV2.lean:26:0: Contract BlowupDensity.Tests.checkedLocalTheoryV2: checked; standard logical axioms only
ℹ [10688/10701] Replayed Tests.Correction
info: Tests/Correction.lean:19:0: Contract BlowupDensity.Tests.checkedCorrection: checked; standard logical axioms only
ℹ [10689/10701] Replayed Tests.MaximalPartial
info: Tests/MaximalPartial.lean:16:0: Contract BlowupDensity.Tests.checkedMaximalPartial: checked; standard logical axioms only
ℹ [10690/10701] Replayed Tests.Uniqueness
info: Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only
ℹ [10691/10701] Replayed Tests.HomogeneousNorm
info: Tests/HomogeneousNorm.lean:17:0: Contract BlowupDensity.Tests.checkedHomogeneousNorm: checked; standard logical axioms only
ℹ [10696/10701] Replayed Tests.HomogeneousPartialV2
info: Tests/HomogeneousPartialV2.lean:35:0: Contract BlowupDensity.Tests.checkedHomogeneousPartialV2: checked; standard logical axioms only
ℹ [10698/10701] Replayed Tests.MaximalPartialV2
info: Tests/MaximalPartialV2.lean:24:0: Contract BlowupDensity.Tests.checkedMaximalPartialV2: checked; standard logical axioms only
ℹ [10699/10701] Replayed Tests.InsertionLifespanV2
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
ℹ [10700/10701] Replayed Tests.TameProduct
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
ℹ [10701/10701] Replayed Tests.MainThresholds
info: Tests/MainThresholds.lean:15:0: Contract BlowupDensity.Tests.checkedMainThresholds: checked; standard logical axioms only
```

`python3 ../experiments/test_contract_mutations.py --skip-build` (cwd `verification`): exit 0.

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

Current-base recheck `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` (ref observed immediately before rechecks: `3cca4264e4f7f86e556084d6b3cefeb1e77031ca`; shared ref may advance): exit 1.

```text
Traceback (most recent call last):
  File "/data_8T/ping/blowup_density/.claude/worktrees/212-A01-contract-v2/experiments/check_contracts.py", line 153, in <module>
    print(json.dumps(check(base=args.base_ref), indent=2))
                     ^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/data_8T/ping/blowup_density/.claude/worktrees/212-A01-contract-v2/experiments/check_contracts.py", line 143, in check
    check_compatibility(root, base, contracts)
  File "/data_8T/ping/blowup_density/.claude/worktrees/212-A01-contract-v2/experiments/check_contracts.py", line 62, in check_compatibility
    assert (root / path).is_file(), f'Removed stable specification: {path}'
           ^^^^^^^^^^^^^^^^^^^^^^^
AssertionError: Removed stable specification: verification/Contracts/V1/CompletedDensity.lean
```

Current-base recheck `scripts/gates.sh` (ref observed immediately before rechecks: `3cca4264e4f7f86e556084d6b3cefeb1e77031ca`; shared ref may advance): exit 1.

```text
== make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 550,
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
  "registered_contracts": 33,
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
[... 35375 output lines omitted ...]
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
info: Tests/LocalTheoryV2.lean:26:0: Contract BlowupDensity.Tests.checkedLocalTheoryV2: checked; standard logical axioms only
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
Traceback (most recent call last):
  File "/data_8T/ping/blowup_density/.claude/worktrees/212-A01-contract-v2/experiments/check_contracts.py", line 153, in <module>
    print(json.dumps(check(base=args.base_ref), indent=2))
                     ^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/data_8T/ping/blowup_density/.claude/worktrees/212-A01-contract-v2/experiments/check_contracts.py", line 143, in check
    check_compatibility(root, base, contracts)
  File "/data_8T/ping/blowup_density/.claude/worktrees/212-A01-contract-v2/experiments/check_contracts.py", line 62, in check_compatibility
    assert (root / path).is_file(), f'Removed stable specification: {path}'
           ^^^^^^^^^^^^^^^^^^^^^^^
AssertionError: Removed stable specification: verification/Contracts/V1/CompletedDensity.lean
```

The shared integration ref advanced again during the rechecks. Final compatibility check pinned to the observed immutable commit:

`python3 experiments/check_contracts.py --base-ref ee6660ec1564e5f478f3e96276ec6c96f5a12e54`: exit 1.

```text
Traceback (most recent call last):
  File "/data_8T/ping/blowup_density/.claude/worktrees/212-A01-contract-v2/experiments/check_contracts.py", line 153, in <module>
    print(json.dumps(check(base=args.base_ref), indent=2))
                     ^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/data_8T/ping/blowup_density/.claude/worktrees/212-A01-contract-v2/experiments/check_contracts.py", line 143, in check
    check_compatibility(root, base, contracts)
  File "/data_8T/ping/blowup_density/.claude/worktrees/212-A01-contract-v2/experiments/check_contracts.py", line 62, in check_compatibility
    assert (root / path).is_file(), f'Removed stable specification: {path}'
           ^^^^^^^^^^^^^^^^^^^^^^^
AssertionError: Removed stable specification: verification/Contracts/V1/CompletedDensity.lean
```

Final `git status --short`: only this new review and `research/A01/probes/rev212_h1_bridge.lean`, `research/A01/probes/rev212_h1_mutation.lean` are untracked. No tracked file or lane HEAD was changed by the reviewer.
