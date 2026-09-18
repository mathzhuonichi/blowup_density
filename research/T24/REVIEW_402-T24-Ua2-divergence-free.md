ACCEPT

## 1. What the lane claims

Reviewed commit `1fdd3a17` on `erenup/402-T24-Ua2-divergence-free`. `research/T24/REPORT_402.md:5` claims the following exact theorem, present at `formalization/NSFormalization/Section3/T24/AffineDivergence.lean:23`:

```lean
theorem divergence_free {U : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain)
    (hdivergence : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
      spatialDivergence U t x = 0) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
        spatialDivergence (affineVelocity U b) t x = 0
```

The report claims only Ua2, not the full API (`research/T24/REPORT_402.md:37`). Its status update at `research/T24/T24_SPLIT.md:94` accurately marks this unit done.

## 2. What is in Lean

1. **Statement fidelity: pass.** Read with `sed -n` the paper's `paper/sections/03-torus.tex:668-696`, especially the admissible solenoidal perturbation at line 671, velocity sum at line 673 and divergence assertion at line 681. The conclusion matches `research/T24/Spec.lean:1038-1040` after the required raw-field substitution. The Spec docstring's 673/679 references locate the velocity formula/proof opening; the explicit divergence sentence is at 681. This inherited citation imprecision does not change the claim.
2. **Raw hypotheses: pass.** The raw packet is `vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean:92`; smoothness is at 94 and divergence at 104. Its divergence clause agrees after replacing the field variable by U and resolving the explicit spatialDivergence namespace qualification. The theorem is token-identical to the registered raw-clause spelling after that field substitution. The registered counterparts are `verification/Contracts/V1/Packet.lean:202` and `:231`. `verification/Bindings/Packet.lean:104` constructs an actual packet using `formalization/NSFormalization/Source/ViscosityPacket.lean:131`, forwarding these clauses at lines 120 and 128. The brief's suggested `Source/Packet.lean` does not exist; these are the actual sources.
3. **Proof and honest inputs: pass.** `vendor/NavierStokesAndEuler/NavierStokes/ResidualCalculus.lean:55-63` requires differentiability of both spatial slices. The proof obtains it from raw smoothness and admissibility at `AffineDivergence.lean:31-39`, then uses both divergence clauses at line 40. Thus retaining smoothness is justified by the vendor lemma, as recorded in `research/T24/ATTEMPTS_UA2.md:19`. No named input or circular premise is introduced.
4. **Vocabulary and non-vacuity: pass.** The canonical definitions at `formalization/NSFormalization/Section3/T24/AffineBasics.lean:22-34` agree with `research/T24/Spec.lean:962-983`. The probe's three definitional bridges are at `research/T24/probes/affine_divergence_closes.lean:34-44`; its selected-packet field application is at 49-57 and its b=0 admissibility/conclusion instance at 61-79. This genuinely supplies the requested non-vacuity instance (specialize ν=1). The time interval is the nonempty [0,1), including t=0; `preSingularDomain` is exactly that slab at `vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:42`. Cylinder parameters occur in admissibility, and the theorem holds for all cylinders; no empty-cylinder premise is imposed. There is no ENNReal/toReal expression or unused dummy hypothesis.
5. **Hygiene: pass.** The only new production declaration is the theorem above. Its module imports AffineBasics at line 1, with no copied definitions, forbidden proof tokens, heartbeat overrides or modified existing Lean modules. The axiom audit at `research/T24/axioms_ua2.lean:5` prints exactly the required list. The only modified existing file is the explicitly requested Ua2 status line in T24_SPLIT.md. The committed module is selected by `experiments/build_changed_lean.py:16-19`, invoked by `.github/workflows/contracts.yml:81`; the dry run confirms inclusion.
6. **Substantive negative check: pass.** `research/T24/probes/rev402_divergence_one.lean:29` changes only the conclusion's constant from 0 to 1 (and updates the `change` spelling at line 36 to that same target). Every hypothesis and the original additivity/rewrite proof are retained. Lean fails with the terminal goal `0 = 1`, not an argument-count error. Exact error below.

## 3. Gaps

No Ua2 gap, blocking finding, or required fix.

The worker's remaining-unit statement (`research/T24/REPORT_402.md:37-39`) is a scope boundary, not a claim that all corresponding mathematics is absent from the tree. Nevertheless I searched the entire Section4 tree using `grep -rnE 'AffineVariationAPI|affineVelocity|affineForce|infinite_dimensional|nonisolated|energy_finite|speed_unbounded|force_smooth|force_support' formalization/NSFormalization/Section4`. There were only five matches: `Section4/D01/ForceClass.lean:351,415,420,421` and `Section4/I01/Quiet.lean:60`. I opened them with sed: they concern compact force membership or the original packet, not an affine API assembly. A broader recursive search including momentum found many PDE lemmas; those are not evidence that Ua3-Ua9 are absent. No blanket “not in the tree” assertion is accepted or made.

Verification was untouched in the requested three-dot diff. Therefore the user's additional conditional gates (`scripts/gates.sh` and explicit `check_contracts.py --base-ref origin/erenup/integration-section3`) are not applicable. All listed Ua2 gates were rerun. Existing package symlinks and the working toolchain made installation unnecessary; no installer or git mutation was performed.

## 4. Commands and results

All Lean commands source `scripts/lean-env.sh`, run Lake only from `verification/`, and set `LEAN_NUM_THREADS=6`. Module build: exit 0, with only Lake's summary `Build completed successfully (3007 jobs).` and no module diagnostics. Module/probe elaboration: exit 0, zero output. Axiom audit: exit 0, exact standard axioms. `make check`: exit 0; its existing informational admission/hash notices are not new module diagnostics.

The full exact stdout/stderr of the gates is retained below as requested, including the very large informational JSON from make check. The capture reruns those gates solely to preserve their complete output without tool-output truncation.

`git diff --name-only origin/erenup/integration-section3...HEAD` (exit 0):
```text
formalization/NSFormalization/Section3/T24/AffineDivergence.lean
research/T24/ATTEMPTS_UA2.md
research/T24/REPORT_402.md
research/T24/T24_SPLIT.md
research/T24/axioms_ua2.lean
research/T24/probes/affine_divergence_closes.lean
```

`rg -n '\\b(sorry|admit|axiom|native_decide)\\b|maxHeartbeats' formalization/NSFormalization/Section3/T24/AffineDivergence.lean research/T24/probes/affine_divergence_closes.lean research/T24/axioms_ua2.lean`: no output (no matches).

`python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration-section3 --dry-run` (exit 0):
```text
Changed Lean modules: NSFormalization.Section3.T16.Assembly, NSFormalization.Section3.T24.AffineDivergence
```
The dry-run utility uses a two-dot comparison; the additional Assembly entry is not a lane edit in the requested three-dot diff.



<details>
<summary>. scripts/lean-env.sh; cd verification; LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.AffineDivergence — exit 0</summary>

```text
Build completed successfully (3007 jobs).
```

</details>

<details>
<summary>. scripts/lean-env.sh; cd verification; LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T24/AffineDivergence.lean — exit 0</summary>

```text
```

</details>

<details>
<summary>. scripts/lean-env.sh; cd verification; LEAN_NUM_THREADS=6 lake env lean ../research/T24/probes/affine_divergence_closes.lean — exit 0</summary>

```text
```

</details>

<details>
<summary>. scripts/lean-env.sh; cd verification; LEAN_NUM_THREADS=6 lake env lean ../research/T24/axioms_ua2.lean — exit 0</summary>

```text
'NSFormalization.Section3.T24.divergence_free' depends on axioms: [propext, Classical.choice, Quot.sound]
```

</details>

<details>
<summary>. scripts/lean-env.sh; cd verification; LEAN_NUM_THREADS=6 lake env lean ../research/T24/probes/rev402_divergence_one.lean — exit 1</summary>

```text
../research/T24/probes/rev402_divergence_one.lean:29:58: error: unsolved goals
U : VelocityField
c : Space
r τ₀ τ₁ : ℝ
hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain
hdivergence : ∀ t ∈ Ico 0 1, ∀ (x : Space), spatialDivergence U t x = 0
b : VelocityField
hb : AffineAdmissible c r τ₀ τ₁ b
t : ℝ
ht : t ∈ Ico 0 1
x : Space
hU_slice : ContDiff ℝ ∞ fun y => U (t, y)
hb_slice : ContDiff ℝ ∞ fun y => b (t, y)
⊢ 0 = 1
```

</details>

<details>
<summary>. scripts/lean-env.sh; LEAN_NUM_THREADS=6 make check — exit 0</summary>

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 628,
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
  "registered_contracts": 42,
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
      "NavierStokes.ActualCopySliceRegularity",
      "NavierStokes.ActualCoreSupport",
      "NavierStokes.ActualCurrentCarrierJets",
      "NavierStokes.ActualCurrentParticularAssembly",
      "NavierStokes.ActualCurrentParticularBounds",
      "NavierStokes.ActualCurrentParticularPhysical",
      "NavierStokes.ActualCurrentWaveSupport",
      "NavierStokes.ActualCycleAssembly",
      "NavierStokes.ActualCycleCoherence",
      "NavierStokes.ActualCycleExcluded",
      "NavierStokes.ActualCycleGeometry",
      "NavierStokes.ActualCycleParameters",
      "NavierStokes.ActualCyclePeriodicity",
      "NavierStokes.ActualCyclePreservation",
      "NavierStokes.ActualCycleResidualBounds",

[... 47289 lines of embedded build/log output elided by the lead at merge time; the full text is in tmp/codex/review_402-T24-Ua2-divergence-free.log ...]

      "NavierStokes.PhaseJetBounds",
      "NavierStokes.PhysicalClassBounds",
      "NavierStokes.PhysicalCoordinateBounds",
      "NavierStokes.PhysicalCopyBounds",
      "NavierStokes.PhysicalCurlCovariance",
      "NavierStokes.PhysicalGraphBounds",
      "NavierStokes.PhysicalHeatCoordinates",
      "NavierStokes.PhysicalMeanDomain",
      "NavierStokes.PhysicalMeanJetBounds",
      "NavierStokes.PhysicalParticularWave",
      "NavierStokes.PhysicalResidualBridge",
      "NavierStokes.PhysicalResidualJetBounds",
      "NavierStokes.PhysicalResidualNaturality",
      "NavierStokes.PhysicalResidualTZ",
      "NavierStokes.PhysicalSignedWave",
      "NavierStokes.PhysicalStageBounds",
      "NavierStokes.PhysicalStageSupport",
      "NavierStokes.PhysicalWaveSum",
      "NavierStokes.PolarCharts",
      "NavierStokes.PositiveAxisExistence",
      "NavierStokes.PositiveAxisSystem",
      "NavierStokes.PositiveOrderMoments",
      "NavierStokes.PositiveRepresentatives",
      "NavierStokes.PositiveTimeCopyFamily",
      "NavierStokes.PositiveTimeSignedData",
      "NavierStokes.PositiveTimeSignedLocalization",
      "NavierStokes.PowerMomentMatrix",
      "NavierStokes.PreparedOutgoing",
      "NavierStokes.PressureDatum",
      "NavierStokes.PressureStream",
      "NavierStokes.PrimaryCopyBounds",
      "NavierStokes.PrimaryCopyBridge",
      "NavierStokes.PrimaryCovarianceBounds",
      "NavierStokes.PrimaryFieldAssembly",
      "NavierStokes.PrimaryGeometryAssembly",
      "NavierStokes.PrimaryMaterialDefect",
      "NavierStokes.PrimaryODE",
      "NavierStokes.PrimaryPulseBounds",
      "NavierStokes.PrimaryRepresentatives",
      "NavierStokes.PrimaryResidualClass",
      "NavierStokes.PrimaryTargetBounds",
      "NavierStokes.ProblemStatement",
      "NavierStokes.ProfileHistories",
      "NavierStokes.ProfileSpectralCone",
      "NavierStokes.PulseAmplitude",
      "NavierStokes.PulseCone",
      "NavierStokes.PulseCovariance",
      "NavierStokes.PulseEnergyHistory",
      "NavierStokes.PulseGrowth",
      "NavierStokes.PulseLag",
      "NavierStokes.R3.CompactEnergy",
      "NavierStokes.R3.CompactForceBound",
      "NavierStokes.R3.CompactSchwartz",
      "NavierStokes.R3.CompactTimeIntegral",
      "NavierStokes.R3.ComparisonCutoffs",
      "NavierStokes.R3.ComparisonFourierSetup",
      "NavierStokes.R3.ComparisonSetup",
      "NavierStokes.R3.ConservativeDifference",
      "NavierStokes.R3.FourierTestDerivatives",
      "NavierStokes.R3.ProblemStatement",
      "NavierStokes.R3.ScalarEnergyBound",
      "NavierStokes.R3.SchwartzCompactApproximation",
      "NavierStokes.R3.SmoothSobolevL6",
      "NavierStokes.R3.WeakFourierUniqueness",
      "NavierStokes.R3ActualCandidate",
      "NavierStokes.R3CompactCandidate",
      "NavierStokes.R3CompactIntegration",
      "NavierStokes.R3ConvolutionYoung",
      "NavierStokes.RadialAlias",
      "NavierStokes.RadialFluxResidual",
      "NavierStokes.RadialHeatProfile",
      "NavierStokes.RadialModulation",
      "NavierStokes.RadialPullback",
      "NavierStokes.RadialSchedule",
      "NavierStokes.RankStateBounds",
      "NavierStokes.RankStateCoherence",
      "NavierStokes.ReferenceBounds",
      "NavierStokes.ReferenceJetBounds",
      "NavierStokes.ReferencePath",
      "NavierStokes.ReleaseMoments",
      "NavierStokes.RenormalizedHeatMoment",
      "NavierStokes.RepairConeBounds",
      "NavierStokes.ReservedPatches",
      "NavierStokes.ResetEnergyBounds",
      "NavierStokes.ResidualCalculus",
      "NavierStokes.ResidualPolarGraph",
      "NavierStokes.ResidualRegularity",
      "NavierStokes.ResidualStability",
      "NavierStokes.ScalarParticularSupport",
      "NavierStokes.ScaledActualParticularControl",
      "NavierStokes.ScaledParticularFrameJets",
      "NavierStokes.ScaledTangentTransport",
      "NavierStokes.Scaling",
      "NavierStokes.SchedulePressure",
      "NavierStokes.ScheduledProfileChoice",
      "NavierStokes.ShapeTransition",
      "NavierStokes.ShapedWaitBounds",
      "NavierStokes.SignedCopyBounds",
      "NavierStokes.SignedCovariance",
      "NavierStokes.SignedCrossDefectClass",
      "NavierStokes.SignedMeanGain",
      "NavierStokes.SignedPhysicalSumCalculus",
      "NavierStokes.SignedStressPrimitive",
      "NavierStokes.SignedWaveUpdate",
      "NavierStokes.SimilarityApproach",
      "NavierStokes.SimilarityCoordinates",
      "NavierStokes.SimilarityHomogeneity",
      "NavierStokes.SimilarityProfile",
      "NavierStokes.SlotColoring",
      "NavierStokes.SlotGeometry",
      "NavierStokes.SlowBaseEndpoint",
      "NavierStokes.SlowBorelBase",
      "NavierStokes.SlowDivergence",
      "NavierStokes.SlowExpansionResidual",
      "NavierStokes.SlowFirstOrderEdge",
      "NavierStokes.SlowRecursion",
      "NavierStokes.SlowResidualMatching",
      "NavierStokes.SlowStressSupport",
      "NavierStokes.SmoothCovariance",
      "NavierStokes.SmoothCutoffs",
      "NavierStokes.SmoothFamilyTorusInverse",
      "NavierStokes.SmoothFourierData",
      "NavierStokes.SmoothLoop",
      "NavierStokes.SmoothMomentRepair",
      "NavierStokes.SmoothParameterIntegral",
      "NavierStokes.SmoothPathFamily",
      "NavierStokes.SolenoidalDiagonal",
      "NavierStokes.SpacetimeEndpoint",
      "NavierStokes.SpacetimeGluing",
      "NavierStokes.SpatialBorelExtension",
      "NavierStokes.SpatialCurl",
      "NavierStokes.SpatialLocalization",
      "NavierStokes.SquaredPartition",
      "NavierStokes.StateMomentBalances",
      "NavierStokes.StateReindex",
      "NavierStokes.StressActivation",
      "NavierStokes.StressAlgebra",
      "NavierStokes.SubcoverPeriodicity",
      "NavierStokes.TailCone",
      "NavierStokes.TailEnergyBounds",
      "NavierStokes.TailGaugePotential",
      "NavierStokes.TangentODE",
      "NavierStokes.TangentProjection",
      "NavierStokes.TemporalMeanUpdate",
      "NavierStokes.TemporalStateCoherence",
      "NavierStokes.TerminalCompensation",
      "NavierStokes.TerminalCone",
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
      "Tests.Localization"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.052s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

</details>

Verdict: ACCEPT. Fixes: none.
