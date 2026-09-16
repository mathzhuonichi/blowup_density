ACCEPT-WITH-NOTES

## 1. What the lane claims

Reviewed HEAD `f0dd0acfc46bc1fcb95c4ee917fbc89b29b1869b`. This accepts the brief's explicitly permitted arbitrary-constructor-output fallback, **not** a completed regularity theorem for lane 208's chosen `localSolution`.

`research/A01/REPORT_209.md:5` claims all four manuscript fields on one horizon; :16 claims pressure recovery for any admissibly forced classical solution, including zero; :21 claims a full constructor audit and zero instance. These claims are supported. The precise main hypotheses (`formalization/NSFormalization/Section4/A01/ManuscriptRegularity.lean:247`) are:
```lean
{ν S : ℝ} {a : SpatialField} {f : SpaceTimeField}
(w : ClassicalSolutionR ν a f S) (hf : D01.MemForceR f)
(U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
(hslice : ∀ t : Icc (0 : ℝ) S,
  (fun x : Space => w.velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
(hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
  ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
  ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
```
Conclusion: `ManuscriptLocalRegularity ν a f S w`. There is no pressure-construction equality or hidden analytic predicate.

Read CLAUDE.md, the lane-review skill, NEXT_SESSION.md, LESSONS.md's first 40 lines, HANDOFF §0/P7, the worker report/attempts, and the lane-207 review (its numbered finding 5 and remaining-scope discussion; there is no heading “§5”).

## 2. What is in Lean

Here M abbreviates `formalization/NSFormalization/Section4/A01/ManuscriptRegularity.lean`.

1. **Exact specification.** M:25–87 is byte-identical, including comments, to `research/A01/Spec.lean:167–229` (Python substring equality returned True). M:20 copies Spec:143's three-clause `IsLerayComplement`: L², symmetric Jacobian, solenoidality of the difference. The four field types therefore agree token-for-token. Read the cited paper with sed: `paper/sections/02-preliminaries.tex:29–32,75–100,105–119` and `paper/sections/appendix-a-local-theory.tex:60–107`. They prescribe precisely the common all-order interval, projected equation, gradient recovery and radial potential/gauge represented here.

2. **Sobolev smoothness.** M:104 chooses the j=0 path, then M:112–115 uses `D01.isSobolevDatum_unique` (`D01/ForceClass.lean:286`) to identify every finite-order witness on Icc. M:107 transports datum by `IsSobolevDatum.congr_field` using the correctly reversed a.e. slice identity. M:110 uses Mathlib `contDiffOn_infty` (`Mathlib/Analysis/Calculus/ContDiff/Defs.lean:549`): `ContDiffOn 𝕜 ∞ f s ↔ ∀ n : ℕ, ContDiffOn 𝕜 n f s`. This is smoothness, not analytic order ω. Restriction to Ico is at M:109. No invalid exchange of ∀j and ∃G occurs.

3. **Decisive pressure endpoint: passes.** M:182 defines H=(f−advection u)−∇p. Spatial differentiation preserves slab smoothness by M:130–143 (parameter-dependent differentiation in spatial univ only); M:184–190 applies this to **w.pressure_smooth**. Thus gradient continuity at zero is actually supplied by the classical solution's slab pressure smoothness (`A02/SolutionClass.lean:124`), not assumed separately. M:191–193 obtains smooth H from hf and velocity/pressure smoothness. M:199–225 proves div H=0 only on Ioo: projected momentum, `D01/DivergenceTime.lean:131` (explicit Ioo hypothesis), and M:157's div Δu=0. The latter uses `C01/EnstrophyIdentityRaw.lean:48` and the exact Laplacian bridge `C01/MomentumCarrierB.lean:185`. M:226–235 extends the **spatial divergence's** zero identity by continuity and `Set.EqOn.of_subset_closure`; `closure_Ioo w.horizon_pos.ne` supplies zero in the closure. M:237–240 adds w.pressure_gradient and Hessian symmetry at every Ico time. No ambient temporal derivative is evaluated at zero. No lane-194 complement equality is needed: the proof establishes the specification's Helmholtz characterization directly for arbitrary w.

4. **Projected sign: passes.** M:118–127 invokes `A01/ConvectionDivergence.lean:127`, whose proof unfolds the residual and uses divergence-free tensor/advection equality (:114). The exact residual is ∂tu+advection−ν•Δu+∇p (`vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean:57`). Its rearrangement has **minus** ν•Δu on the left, with real scalar action and no viscosity coercion issue.

5. **Pressure potential: passes for arbitrary w.** M:259 invokes `A01/PressureGauge.lean:200`. That theorem supplies smooth gradient slices and symmetric Hessian (:117,:132). Its core (:167–194) sets Q to the radial potential, proves ∇Q=∇p by `pressureGradient_pressurePotential` (:180), obtains differentiability of Q (:184), then applies `is_const_of_fderiv_eq_zero` on the whole real vector space (:190). The time gauge is explicitly p(t,0)−Q(t,0) (:176). This matches `A02/SolutionClass.lean:109` and includes zero; it does not require w.pressure to have been constructed radially.

6. **Honest inputs/non-vacuity.** `A02/SolutionClass.lean:120` forces S>0, so Ico and Ioo are nonempty. No toReal or infinity conversion appears in M. `CylinderWiring.lean:36–57` exports exactly hpaths on one U; `ConstructorAssembly.lean:259–286` exports exactly hslice for w. The actual composition in `research/A01/axioms_manuscript_regularity.lean:21–59` typechecks, including general smooth solenoidal data, not only zero. Its :73–79 zero-force/data example yields 0<S≤1 and actual manuscript regularity. The initial datum in these audit constructors is honestly velocity(0,·), not a claim that this audit identifies it with the supplied a.field. No additional non-vacuity assumption is smuggled in.

7. **Hygiene.** Nine module declarations plus two audit theorems all print exactly the three standard axioms. Whole-word prohibited-token scan of the two new Lean files has no hits. The sole maxHeartbeats override is 400000 at M:173, declaration-local, explained at :172. The merge-base diff adds only the new module/audit/report/attempts and modifies `research/A01/A3_SPLIT.md:392`; no existing Lean module or verification file is modified. The required row is at A3_SPLIT:396. Direct Lean checking is silent. Standard lake build replays inherited warnings but none from this module; the quiet build is silent.

## 3. Gaps and exact fixes

**N1 — documentation/interface note, not a rejection of the authorized fallback.** Lane 208's branch is available at `c85d1331f151c1ee29286429e1306539eb20eb00` even though its file is absent from this checkout. I read its exact source through git show and replayed it in `research/A01/probes/rev209_interface.lean`. Its solution_of_base discards the exported slice witness (:58 in the probe), exists_localSolution keeps only Nonempty, and localSolution uses Classical.choice of that bare Nonempty (:113–116). It therefore cannot directly instantiate M:247 from its current public interface. The replay fails with the substantive remaining U, hslice and hpaths obligations below. This is an integration/export task; the successful full constructor audit establishes that lane 209's inputs are available before lane 208 discards them. Future wiring must preserve witnesses/regularity through selection, or separately prove regularity for the already chosen solution; choosing a different solution is insufficient.

**Exact one-line fix:** append after `research/A01/REPORT_209.md:32`: “The available lane-208 chosen-solution interface exports only Nonempty ClassicalSolutionR, so direct application still needs U/hslice/hpaths retained through selection or a separate transfer theorem; this lane proves the authorized constructor-output fallback.”

No mathematical fix to M is requested. The separate H¹-uniform bound/API registration are correctly out of scope (REPORT:33). Whole-Section4 `grep -rnE` searches for `localSolution|localHorizon`, `LocalTheoryAPI`, and `horizon_lower_bound|uniform.*horizon|H¹` returned 14, 16, and 14 matches respectively. Existing `A02/Maximal.lean:157` and `A02/Order.lean:56` consume a supplied local solution; they do not export the missing witnesses. `A01/Horizon.lean:44–68` distinguishes its high-order cylinder horizon from the required H¹ bound; `A01/ContinuationInvariant.lean:156` is a higher-order restart result. Thus “outside this delivery” is warranted, without claiming no useful ingredients exist. The manuscript's H¹ restart claim is at Appendix A:147–150. There is no other “not in the tree” analytic-gap claim in REPORT_209.

## 4. Commands and results

All Lake commands used sourced `scripts/lean-env.sh`, cwd `verification/`, and `LEAN_NUM_THREADS=6`. Existing shared packages were confirmed by the packages symlink; no installation, git-state change, or source fix was performed. Only permitted review/probe files were written. Outputs below are exact, with at most the first/last 40 lines of a command retained.

### `lake build NSFormalization.Section4.A01.ManuscriptRegularity`

Exit 0. 

```text
⚠ [8925/9631] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [10203/10384] Replayed Formal.R3LerayFrequencySymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean:43:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10223/10384] Replayed NSFormalization.Source.RealSobolev
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
[... middle omitted ...]
warning: ../vendor/HeliCorgi/Formal/R3DivergencePointwise.lean:25:19: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10262/10384] Replayed Formal.R3LerayL2Operator
warning: ../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean:34:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: ../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean:61:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10263/10384] Replayed Formal.R3LerayFourierBridge
warning: ../vendor/HeliCorgi/Formal/R3LerayFourierBridge.lean:73:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10264/10384] Replayed Formal.R3LerayComplexFiberSymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
ℹ [10279/10384] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10284/10384] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [10287/10384] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10301/10384] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
Build completed successfully (10384 jobs).
```

### `lake -q --log-level=error build NSFormalization.Section4.A01.ManuscriptRegularity`

Exit 0. Zero output.

### `lake env lean ../formalization/NSFormalization/Section4/A01/ManuscriptRegularity.lean`

Exit 0. Zero output.

### `lake env lean ../research/A01/axioms_manuscript_regularity.lean`

Exit 0. 

```text
'NSFormalization.Section4.A01.IsLerayComplement' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.ManuscriptLocalRegularity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.sobolev_smooth_of_pipeline' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.projected_of_classicalSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.contDiffOn_spatial_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.contDiffOn_spatialDivergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.spatialLaplacian_solenoidal' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.pressure_recovery_of_classicalSolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.manuscriptLocalRegularity_of_pipeline' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.regular_constructor_of_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.regular_constructor_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `make check`

Exit 0. 

```text
EXIT 0 LINES 28234
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
[... middle omitted ...]
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
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
.............
----------------------------------------------------------------------
Ran 13 tests in 0.041s

OK
```

### `bash scripts/gates.sh NSFormalization.Section4.A01.ManuscriptRegularity`

Exit 0. 

```text
EXIT 0 LINES 28482
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
[... middle omitted ...]
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
.............
----------------------------------------------------------------------
Ran 13 tests in 0.040s

OK
```

### `lake env lean ../research/A01/probes/rev209_sign.lean`

Exit 1. 

```text
../research/A01/probes/rev209_sign.lean:27:2: error: Type mismatch
  (navierStokesResidual_eq_iff_projected ν w.velocity w.pressure t x (f (t, x))
        (ContDiff.differentiable (contDiff_slice w.velocity_smooth ⟨LT.lt.le ht.left, ht.right⟩)
          (of_eq_true
            (Eq.trans (congrArg Not (Eq.trans WithTop.coe_eq_zero._simp_1 ENat.top_ne_zero._simp_1)) not_false_eq_true))
          x)
        (w.divergence t ⟨LT.lt.le ht.left, ht.right⟩ x)).mp
    (w.momentum t ht x)
has type
  temporalDerivative w.velocity t x - ν • spatialLaplacian w.velocity t x =
    f (t, x) - convectionDivergence w.velocity t x - pressureGradient w.pressure t x
but is expected to have type
  temporalDerivative w.velocity t x + ν • spatialLaplacian w.velocity t x =
    f (t, x) - convectionDivergence w.velocity t x - pressureGradient w.pressure t x
```

### `lake env lean ../research/A01/probes/rev209_interface.lean`

Exit 1. 

```text
../research/A01/probes/rev209_interface.lean:123:91: error: unsolved goals
case hslice
ν : ℝ
a : A02.SpatialField
f : A02.SpaceTimeField
hν : 0 < ν
ha : a ∈ A02.initialClassR
hf : D01.MemForceR f
⊢ ∀ (t : ↑(Set.Icc 0 (localHorizon ν a f))),
    (fun x => (localSolution ν a f hν ha hf).velocity (↑t, x)) =ᵐ[MeasureTheory.volume] ↑↑(?U t)

case hpaths
ν : ℝ
a : A02.SpatialField
f : A02.SpaceTimeField
hν : 0 < ν
ha : a ∈ A02.initialClassR
hf : D01.MemForceR f
⊢ ∀ (j m : ℕ),
    ∃ G,
      ContDiffOn ℝ (↑j) G (Set.Icc 0 (localHorizon ν a f)) ∧
        ∀ (t : ↑(Set.Icc 0 (localHorizon ν a f))), D01.IsSobolevDatum (↑m) (↑↑(?U t)) (G ↑t)

case U
ν : ℝ
a : A02.SpatialField
f : A02.SpaceTimeField
hν : 0 < ν
ha : a ∈ A02.initialClassR
hf : D01.MemForceR f
⊢ C(↑(Set.Icc 0 (localHorizon ν a f)), ↥EulerMeanSolenoidal.L2)
```

The sign probe copies the projected theorem's proof unchanged and changes only the left-hand Laplacian sign (:23); failure is the expected mathematical type mismatch, not a missing argument. The interface probe separately records missing exports and is not counted as the substantive mutation.

The gates script also ran `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` (scripts/gates.sh:15), with base_compatibility_checked=true, plus contract tests and mutations. No verification files changed, so these were additional checks. The architecture log's legacy BoundaryCorollary admission and source_hashes_match=false are pre-existing repository diagnostics, not admissions in this module; its eleven transitive audits are clean.

`git diff --check`: exit 0, no output. `git diff --name-only origin/erenup/integration...HEAD`:
```text
formalization/NSFormalization/Section4/A01/ManuscriptRegularity.lean
research/A01/A3_SPLIT.md
research/A01/ATTEMPTS_MANUSCRIPT_REGULARITY.md
research/A01/REPORT_209.md
research/A01/axioms_manuscript_regularity.lean
```

Prohibited-token/heartbeat scan:
```text
formalization/NSFormalization/Section4/A01/ManuscriptRegularity.lean:173:set_option maxHeartbeats 400000 in
```

Final disposition: ACCEPT-WITH-NOTES; only the exact one-line REPORT_209 interface clarification in part 3 is requested.

