ACCEPT

## 1. What the lane claims

Reviewed HEAD `76a235548bf2e23a6fe23e304b3fb13246be8298` against the existing `origin/erenup/integration` ref, without fetching or changing git state. Read CLAUDE.md, the lane-review skill, LESSONS top 40 lines, NEXT_SESSION.md, HANDOFF §0/P7, Spec, REPORT_207, REVIEW_207 §3, REPORT_208 and ATTEMPTS_LOCAL_SOLUTION. Used the existing installed toolchain/package symlink without rerunning the installer in this read-only review.

`research/A01/REPORT_208.md:5` claims original-datum identification, the initial-class carrier bridge, existential positive local existence, and shared total horizon/solution data. Each exists with the claimed scope. This accepts lane 208's solution field, not the entire LocalTheoryAPI. The registration table at `research/A01/A3_SPLIT.md:392` accurately leaves 209/210/211 pending.

Below `LS` means `formalization/NSFormalization/Section4/A01/LocalSolution.lean`; other A01 filenames refer to that directory.

## 2. What is in Lean

1. **Datum identification and transport.** LS:39 retains positive viscosity, positive S, force membership, the smooth solenoidal carrier, and an actual H⁷ base mild solution with its full Duhamel identity. These are honest fixed-horizon inputs; LS:69 supplies that base solution on an existential horizon rather than assuming arbitrary-time existence. `CylinderWiring.lean:36` gives U and `U 0 = a.toLp` (:43); `JointRepresentative.lean:552` supplies all slice a.e. identities and joint smoothness on Ico. LS:59–64 specializes at zero and composes with `SmoothL2Field.toLp_ae` (`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:44`). Both continuity facts are valid: `D01/DatumToJets.lean:366` composes slab smoothness with x ↦ (0,x), requiring 0 ∈ Ico 0 S, established by hS; `a.smooth.continuous` is the other side. Mathlib `MeasureTheory/Measure/OpenPos.lean:142`, `Continuous.ae_eq_iff_eq`, applies to volume on Euclidean space. There is no unjustified two-sided time differentiability at zero.

   LS:20–23 changes only the datum index and initial proof. Structure-update syntax reuses velocity, pressure, horizon_pos, both smoothness proofs, divergence, momentum, sobolev, and pressure_gradient unchanged. `ConstructorAssembly.lean:259` supplies the old structure with datum velocity(0,·); LS:65 transports precisely that structure. No weaker replacement field is introduced. `axioms_local_solution.lean:34` additionally checks velocity/pressure preservation by rfl.

2. **Initial class and all orders.** The contract at `verification/Contracts/V1/Data.lean:495,509` says exactly:

   ```lean
   def MemHInfty (a : SpatialField) : Prop :=
     ContDiff ℝ ∞ a ∧ ∀ m : ℕ, ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) a A
   def initialClassR : Set SpatialField := {a | MemHInfty a ∧ IsSolenoidal a}
   ```

   `IsSolenoidal` (:504) is pointwise zero spatial divergence. This realizes H^∞ ∩ L²_σ, not arbitrary L² equivalence classes. LS:26 calls `D01/DatumToJets.lean:306`; its carrier is literally `⟨z, hz, memHInfty_jets hz hA⟩`, with field equality rfl. `memHInfty_jets` (:287) supplies **every n : ℕ**, using the order-n datum, including n=0. `SmoothL2Field` (`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31`) retains all these jets. LS:32–36 rewrites the field identity and converts trace divergence to the identical coordinate sum in ha.2. No order or divergence hypothesis is dropped.

3. **All nine declarations and the exact interface.** LS:20 transport_initial; :26 smoothL2_of_initialClassR; :39 solution_of_base; :69 exists_localSolution_smooth (0<S≤Smax); :82 exists_localSolution (positive S and Nonempty solution with datum a); :92 localHorizon; :99 localHorizon_spec; :107 localHorizon_pos; :112 localSolution are exactly the reported objects. LS:94 chooses under the conjunction of the three contract hypotheses and returns 1 otherwise. LS:103 uses that same choice; LS:115 extracts data on that same horizon. There is no independently chosen downstream horizon or solution.

   After substituting `horizon := localHorizon`, the binder order and premises are exactly `∀ ν a f, 0 < ν → a ∈ initialClassR → MemForceR f → ClassicalSolutionR ν a f (localHorizon ν a f)` (`research/A01/Spec.lean:297`). Literally the module uses A02's structure, so it is not the canonical inductive type without conversion. This is the repository-required exception, correctly bridged by `BlowupDensity.Bindings.maximalPartial_ofA02` (`verification/Bindings/MaximalPartial.lean:73`), reusing all ten fields. `research/A01/axioms_local_solution.lean:25` checks the canonical contract type with no extra hypothesis. A comment/whitespace-stripped token comparison of the two ClassicalSolutionR structure declarations returned True (`Data.lean:624`, `A02/SolutionClass.lean:114`). The brief's location in Restrict is historical: `A02/Restrict.lean:1,32` explicitly imports and documents relocation to SolutionClass. No new restatement was added.

4. **Paper fidelity and non-vacuity.** Opened the paper with sed: `paper/sections/02-preliminaries.tex:1–23,105–120`, `appendix-a-local-theory.tex:60–77,147–153`. The initial class is eq:Rinitial (:12); the common all-order interval is Appendix A:66–76. The lane proves the requested qualitative local-existence component. The force restriction to MemForceR is already explicit in Spec:289 and matches eq:Rclasses; this lane adds none. Strict positivity prevents empty intervals, and LS contains no ENNReal.toReal conversion. All named analytic work is supplied internally in LS:51–58, not left as an added external premise. The existing zero-data/zero-force witness at `research/A01/axioms_local_solution.lean:21` compiles and inhabits the chosen positive-horizon solution type; :39 checks fallback 1. Thus the requested non-vacuity instance is already present. This is a satisfiability test, not a substitute for the general proof.

5. **Hygiene.** The production module has nine named declarations, zero `example`, zero sorry/admit/axiom/native_decide tokens, and no maxHeartbeats settings. The conformance file deliberately has four examples, including the requested zero-input example; “zero example” is satisfied as that non-vacuity check, while production has none. All nine axiom outputs are exactly the required list. The merge-base diff adds one Lean module and the conformance file; no existing Lean module or verification file is changed. The sole modified existing record is the explicitly requested A3_SPLIT addition. `git diff --check` passes.

## 3. Gaps

No blocking finding or required fix.

Before accepting REPORT_208:28–31, searched the **whole** `formalization/NSFormalization/Section4` tree with `grep -rnE 'ManuscriptLocalRegularity|horizon_lower_bound|HOne|H1|uniform.*horizon|LocalTheoryAPI'`. The closest candidates were opened. `ProjectedEquation.lean:40` already supplies the projected clause for any classical solution; `PressureGauge.lean:200` already supplies radial-potential gauge equivalence; `CylinderWiring.lean:56` provides all-order time paths before choice. Thus pending regularity means assembly for the selected data, not absence of all its ingredients. `Continuation.lean:249` and `ContinuationInvariant.lean:156` give uniform restart for an order-(q+1) cylinder bound with q≥6, not the requested H¹-ball bound. No full LocalTheoryAPI assembly or H¹ lower bound for localHorizon was found. Registration is explicitly deferred in `research/A01/A3_SPLIT.md:399`.

The worker's horizon warning is conditional and correct: qualitative choice from an H⁷ existence theorem does not prove H¹ uniformity (Appendix A:147–150; Spec's horizon_lower_bound). If 210 proves a lower bound for this very choice, 209's work stays applicable. If 210 replaces the base horizon/solution, the old dependent regularity statement must be transported or re-established for that replacement; a fresh analytic proof is not automatically necessary if generic regularity lemmas apply. This is a coordination risk only if the choice changes, not a defect in lane 208.

Negative check: `research/A01/probes/rev208_negative.lean:7` reverses `0 < localHorizon ν a f` to `localHorizon ν a f < 0`, retaining all hypotheses and the original proof. Lean rejects it with the expected type mismatch below. The control restores only the inequality and typechecks with zero output. This is a substantive sign mutation, not a dropped argument.

## 4. Commands and results

All Lean commands sourced `. scripts/lean-env.sh`, exported `LEAN_NUM_THREADS=6`, and ran Lake only from verification/. Only one Lake process was run at a time. `make test` was run separately because gates.sh filters its output and can mask its exit status. Although verification/ was untouched, the full gates script and explicit base-ref contract check were also run. Build diagnostics are replayed dependency warnings plus the success banner; none originate in LocalSolution. Direct module elaboration has exactly zero output.

Raw command output below is limited to the first and last 40 lines per command. Full transient logs are `/tmp/rev208_*.log`; they are not added to the repository.

`cd verification && lake build NSFormalization.Section4.A01.LocalSolution` — exit 0; 219 lines, 12820 bytes.

First 40 lines:

```text
⚠ [8927/9428] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [10096/10281] Replayed Formal.R3LerayFrequencySymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean:43:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10116/10281] Replayed NSFormalization.Source.RealSobolev
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
```

139 middle lines omitted. Last 40 lines:

```text
⚠ [10157/10281] Replayed Formal.R3LerayComplexFiberSymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
ℹ [10172/10281] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10177/10281] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [10180/10281] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10194/10281] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
⚠ [10244/10281] Replayed NSFormalization.Section4.A01.AprioriFamily
warning: NSFormalization/Section4/A01/AprioriFamily.lean:148:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10245/10281] Replayed NSFormalization.Section4.A01.MildGronwall
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (10281 jobs).
```

`cd verification && lake env lean ../formalization/NSFormalization/Section4/A01/LocalSolution.lean` — exit 0; 0 lines, 0 bytes.

No output (0 bytes).

`cd verification && lake env lean ../research/A01/axioms_local_solution.lean` — exit 0; 9 lines, 982 bytes.

```text
'NSFormalization.Section4.A01.transport_initial' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.smoothL2_of_initialClassR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.solution_of_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.exists_localSolution_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.exists_localSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.localHorizon' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.localHorizon_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.localHorizon_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.localSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`make check` — exit 0; 28234 lines, 1159606 bytes.

First 40 lines:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 525,
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
```

28154 middle lines omitted. Last 40 lines:

```text
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
Ran 13 tests in 0.040s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

`make test` — exit 0; 344 lines, 21755 bytes.

First 40 lines:

```text
lake -d verification test
⚠ [8778/9336] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9875/10455] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9876/10455] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
ℹ [10241/10455] Replayed Tests.Thresholds
info: Tests/Thresholds.lean:13:0: Contract BlowupDensity.Tests.checkedThresholds: checked; standard logical axioms only
⚠ [10248/10573] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR
```

264 middle lines omitted. Last 40 lines:

```text

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
ℹ [10548/10573] Replayed Tests.GradientL6V2
info: Tests/GradientL6V2.lean:22:0: Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
ℹ [10553/10573] Replayed Tests.EnergyHighPartialV2
info: Tests/EnergyHighPartialV2.lean:30:0: Contract BlowupDensity.Tests.checkedEnergyHighPartialV2: checked; standard logical axioms only
ℹ [10556/10573] Replayed Tests.DatumLemmasV3
info: Tests/DatumLemmasV3.lean:31:0: Contract BlowupDensity.Tests.checkedDatumLemmasV3: checked; standard logical axioms only
ℹ [10557/10573] Replayed Tests.Correction
info: Tests/Correction.lean:19:0: Contract BlowupDensity.Tests.checkedCorrection: checked; standard logical axioms only
ℹ [10558/10573] Replayed Tests.MaximalPartial
info: Tests/MaximalPartial.lean:16:0: Contract BlowupDensity.Tests.checkedMaximalPartial: checked; standard logical axioms only
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

`scripts/gates.sh NSFormalization.Section4.A01.LocalSolution` — exit 0; 28496 lines, 1176904 bytes.

First 40 lines:

```text
== make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 525,
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
```

28416 middle lines omitted. Last 40 lines:

```text
info: Tests/Thresholds.lean:13:0: Contract BlowupDensity.Tests.checkedThresholds: checked; standard logical axioms only
info: Tests/Scaling.lean:18:0: Contract BlowupDensity.Tests.checkedScaling: checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartial.lean:15:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartial: checked; standard logical axioms only
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
info: Tests/EnergyAbsorptionV4.lean:18:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionV4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
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

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration` — exit 0; 28202 lines, 1158635 bytes.

First 40 lines:

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
```

28122 middle lines omitted. Last 40 lines:

```text
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
      "Tests.GradientL6V2"
    ]
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

`cd verification && lake env lean ../research/A01/probes/rev208_negative.lean` — exit 1; 6 lines, 198 bytes.

```text
../research/A01/probes/rev208_negative.lean:7:30: error: Type mismatch
  (localHorizon_spec hν ha hf).left
has type
  0 < localHorizon ν a f
but is expected to have type
  localHorizon ν a f < 0
```

`cd verification && lake env lean ../research/A01/probes/rev208_control.lean` — exit 0; 0 lines, 0 bytes.

No output (0 bytes).

`git diff --name-only origin/erenup/integration...HEAD` — exit 0; 5 lines, 194 bytes.

```text
formalization/NSFormalization/Section4/A01/LocalSolution.lean
research/A01/A3_SPLIT.md
research/A01/ATTEMPTS_LOCAL_SOLUTION.md
research/A01/REPORT_208.md
research/A01/axioms_local_solution.lean
```

`git diff --check` — exit 0; 0 lines, 0 bytes.

No output (0 bytes).

No tracked source, pre-existing record, index or ref was changed by this review. New workspace files are this report and the two permitted rev208 probes. Fixes: none.
