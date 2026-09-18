ACCEPT-WITH-NOTES

## 1. What the lane claims

Reviewed HEAD `c4be85b0a867d5a0fbf253c2370c554943090c8b` on `erenup/394-T17-UCAN-canonical-correction`. This review supersedes the earlier untracked rejection report already present when this review started. The three earlier reviewer probes were also present and have not been edited. No lane code, records, or git state was changed; only this requested review report was rewritten.

Read CLAUDE.md, .claude/skills/lane-review/SKILL.md, the top 40 lines of logs/LESSONS.md, the supplied brief, research/T17/REPORT_394.md including its continuation, Spec, SPEC_ISSUES, T17/T18 split notes, T15 REPORT_384, and the T16 canonical template/probe.

`research/T17/REPORT_394.md:5` claims the canonical 45-field API and existential statement; :21 claims literal Spec copying and bidirectional adapters; :26 claims vocabulary bridges and U3–U6 checks. Its continuation adds the canonical periodized force-profile identity. The scope remains a statement layer and concrete-data conformance checks, not construction of an entire CorrectionAPI.

## 2. What is in Lean

1. **Statement fidelity passes.** `formalization/NSFormalization/Section3/T17/Correction.lean:71` contains all 45 fields of `research/T17/Spec.lean:752`, in order. Mechanical comparison removed comments/whitespace and made only the authorized substitutions `P.velocity → u`, bare `place.x₀ place.T`, and registered `alpha → alphaT`: all field types match. The probe structure at `research/T17/probes/correction_canonical.lean:753` is literally identical to the Spec structure. Every field retains a paper-line docstring; some prose is shortened without changing its meaning. `Correction.lean:294` retains the existential shape with raw parameters. This is a definition, not an unconditional existence theorem.

2. **Paper fidelity passes.** Opened with `sed -n` the cited `paper/sections/03-torus.tex:2`, :22, :102, :176–285, and `paper/sections/01-introduction.tex:143`. The five force terms, signs and interior scale powers match paper :219/:264 and `ForceProfile.lean:83`. Derivative exponents `2*j+m` and `2+m` match paper :226 and `Correction.lean:199`/:214. Energy, mixed and Sobolev rates match paper :234/:235/:239 and `Correction.lean:239`/:257/:276. Open support ball/time interval and fixed closed profile cylinder are retained; constants precede scale quantifiers.

3. **Conversions and theorem checks pass.** `research/T17/probes/correction_canonical.lean:1004`/:1026 supply placement adapters; :1057/:1067 cutoff adapters; :1083/:1115 local-potential adapters; :1147/:1156 localization adapters. The ten vocabulary bridges start at :1167. Both correction adapters explicitly map all 45 fields (:1219/:1271); :1323/:1329 prove both round trips. U3 checks start at :1345, U4 at :1396, U5 at :1454, U6 at :1477. All compile silently.

4. **The former blocker is resolved.** `research/T17/probes/force_profile_canonical.lean:29` proves precisely `Correction.lean:155` specialized to `correctionData`, with the genuine canonical `correctionForce` on the left. Its premises (:33–38) are global smoothness hv plus preceding API data: potential, positive radius, chart inclusion and reference periodicity. There is no assumed desired identity. The proof derives `2*r<1` (:52–57), transports force (:58–64), proves single-copy support (:65–83), places the closed-cylinder chart point strictly inside the ball (:85–95), and collapses the lattice lift (:96–100). Opened and checked its suppliers: `Section3/T13/LocalizationKernel.lean:171`, `Section3/T17/Transport.lean:222`/:281, `Section3/T16/LatticeLift.lean:139`, and `Section3/T17/ForceProfile.lean:252`. The old `rev394_field_conformance.lean` tries to use the chart theorem directly and is obsolete as a completion test; the new proof supplies the missing bridge. The new theorem and its exact three-axiom guard (:109) compile silently.

5. **Hypotheses are honest.** `Correction.lean:23` explicitly leaves G1 to assembly and adds no reference_smooth field. U3/U4 smoothness and compact-support premises come from potential; their uniform bounds retain ε₀≤1. U5/U6 checks specialize to concrete correctionData with explicit separation/scale premises, exactly as `Section3/T17/CorrectionDeriv.lean:47` and `ForceDeriv.lean:50`. Opened the Paper1 sources `CorrectionForceProfile.lean:57`, :75, :185, :204: their smoothness, support, rescaling and uniform-bound statements agree with the restored U4 transport.

6. **No vacuity escape found.** `Correction.lean:79` carries LocalPotentialAPI, whose `Section3/T16/LocalPotential.lean:123` and :130 require positive cylinder radius and scale threshold. Norm bounds remain ENNReal-valued; p.toReal/q.toReal occur in reciprocal exponents, not as a conversion of a possibly infinite norm to zero. `research/T17/probes/rev394_nonvacuity.lean:8` constructs an actual T16 zero-reference witness with K={0}, r=1/4 and T=δ=1, proves its scale interval and fixed cylinder nonempty, and :21/:23 check a smooth constant reference and a nonzero-scale chart identity. It compiles silently. This checks the domains and premises; it does not claim the full API inhabitant that this brief defers.

7. **Hygiene passes.** The new T17 modules/probes contain no sorry/admit/axiom/native_decide declarations or maxHeartbeats setting. The keyword scan only finds the prose “axiom audit” at `research/T17/axioms_ucan.lean:4`; Contracts imports occur only in the allowed probe. The three-dot diff lists only added formalization modules, including inherited lane 384 Scaling. The modified existing files are the requested split records, not existing Lean modules. No verification/ files changed. The earlier stale ForceProfile source references have been repaired at `ForceProfile.lean:46` and :248.

## 3. Gaps and exact one-line fixes

No mathematical blocker remains for this lane. Full API assembly and G1 remain explicitly deferred (`Correction.lean:23`; `research/T17/REPORT_394.md:35`). The conformance theorem is presently in a research probe, as reported; downstream production assembly must import or relocate its proof appropriately.

Two documentation fixes:

1. `research/T17/ATTEMPTS_UCAN.md:48`: replace the row with:
   ``| 19 | `force_profile_identity` | bare chart/profile helpers | Closed at concrete correctionData by force_profile_identity_canonical in probes/force_profile_canonical.lean, under G1 hv |``
2. `research/T17/probes/correction_canonical.lean:1217`: replace the heading with `/-! ## All forty-five fields, in both directions -/`.

**Whole-Section4 gap audit.** For each category below ran `grep -rnE '<pattern>' formalization/NSFormalization/Section4` over the entire tree, then opened relevant positive hits. The report describes later support/volume/energy/mixed/Sobolev units as outside this lane, not absent mathematics.

| Category | Pattern | Relevant result |
|---|---|---|
| Assembly/G1 | reference_smooth\|exists_local_truncation\|CorrectionAPI | `Section4/I02/Reference.lean:68`: local truncation assumes smoothness on a time slab times all Space; not a completed canonical T17 assembly. |
| Periodized identity | force_profile_identity\|force_eq\|singleCopy\|single_copy | No exact canonical T17 bridge found there; current lane supplies it in its new probe. |
| Support/volume | force_support\|force_spatial_volume\|force_time_length\|spatial_support_volume\|temporal_support_length | `Section4/I02/Support.lean:43`/:53 are Euclidean projection bounds; torus transport still matters. |
| Energy | correction_energy_bound\|energyEssSup_le\|energyGradient_le | `Section4/I02/Energy.lean:103`/:140 provide Euclidean energy bounds. |
| Mixed | force_mixed_bound\|exists_slicePath | `Section4/I02/Mixed.lean:107` provides a Euclidean Lp slice path. |
| Sobolev | force_sobolev_bound\|forceSobolev\|correction.*[Ss]obolev | Existing norm infrastructure, e.g. `Section4/A01/ForceCap.lean:117`, not the exact canonical torus correction bound. |

No blanket “not in the tree” claim is accepted merely from a missing identifier.

## 4. Commands and results

Every Lake invocation ran after `. scripts/lean-env.sh`, from verification/, with LEAN_NUM_THREADS=6; one Lake process at a time. The installed environment worked, so no installation or git mutation was performed.

### Build

`LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.Correction`: exit 0, no diagnostics from this lane's modules. Exact output (dependency diagnostics are replayed):
```text
⚠ [8778/8947] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9819/9999] Replayed NSFormalization.Paper1.PeriodicSobolevHilbert
info: NSFormalization/Paper1/PeriodicSobolevHilbert.lean:60:55: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
warning: NSFormalization/Paper1/PeriodicSobolevHilbert.lean:60:51: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9820/9999] Replayed NSFormalization.Paper1.PeriodicH2Embedding
warning: NSFormalization/Paper1/PeriodicH2Embedding.lean:148:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: NSFormalization/Paper1/PeriodicH2Embedding.lean:263:23: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper1/PeriodicH2Embedding.lean:268:9: Variable name `k` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _k

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9830/9999] Replayed NSFormalization.Paper1.LocalizationBoundary
warning: NSFormalization/Paper1/LocalizationBoundary.lean:355:36: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Paper1/LocalizationBoundary.lean:361:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
⚠ [9839/9999] Replayed Formal.EndpointSafeTwoSpacePicard
warning: ../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:126:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: ../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:627:18: `continuousOn_iff_continuous_restrict` has been deprecated: Use `continuousOn_iff_continuous_domRestrict` instead
warning: ../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:766:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: ../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:768:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: ../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:839:21: `continuousOn_iff_continuous_restrict` has been deprecated: Use `continuousOn_iff_continuous_domRestrict` instead
⚠ [9841/9999] Replayed NSFormalization.Paper1.PeriodicWeightShift
warning: NSFormalization/Paper1/PeriodicWeightShift.lean:23:10: Unused tactic linter: `ring` does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
warning: NSFormalization/Paper1/PeriodicWeightShift.lean:23:10: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
⚠ [9863/10015] Replayed NSFormalization.Source.RealSobolev
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
⚠ [9867/10015] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9874/10015] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9877/10015] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9887/10015] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9890/10015] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
ℹ [9903/10015] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [9920/10015] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
⚠ [9953/10015] Replayed NSFormalization.Paper1.PeriodicScalarForceEndpoints
warning: NSFormalization/Paper1/PeriodicScalarForceEndpoints.lean:156:5: `continuous_finset_sum` has been deprecated: Use `continuous_finsetSum` instead
⚠ [9957/10015] Replayed NSFormalization.Paper1.PeriodicForceConvergence
warning: NSFormalization/Paper1/PeriodicForceConvergence.lean:53:13: This simp argument is unused:
  Pi.neg_apply

Hint: Omit it from the simp argument list.
  [apply] simp only [mul_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9958/10015] Replayed NSFormalization.Paper1.PeriodicInsertionSupport
warning: NSFormalization/Paper1/PeriodicInsertionSupport.lean:129:13: Variable name `hr` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hr

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9960/10015] Replayed NSFormalization.Paper1.PeriodicPacketEndpointRates
warning: NSFormalization/Paper1/PeriodicPacketEndpointRates.lean:45:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper1/PeriodicPacketEndpointRates.lean:72:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9961/10015] Replayed NSFormalization.Paper1.PeriodicCorrectionEndpointRates
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:43:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:44:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:69:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper1/PeriodicCorrectionEndpointRates.lean:70:28: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9969/10015] Replayed NSFormalization.Paper1.PeriodicDensityFiber
warning: NSFormalization/Paper1/PeriodicDensityFiber.lean:85:5: Variable name `hT` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hT

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicDensityFiber.lean:118:5: Variable name `hT` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hT

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9973/10015] Replayed NSFormalization.Paper1.PeriodicLocalLifespan
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:100:23: Variable name `U` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _U

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:325:24: Variable name `V` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _V

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:335:24: Variable name `V` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _V

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:400:26: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:587:13: Variable name `hS` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hS

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9989/10015] Replayed NSFormalization.Section3.T16.Assembly
warning: NSFormalization/Section3/T16/Assembly.lean:327:12: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: NSFormalization/Section3/T16/Assembly.lean:332:11: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Section3/T16/Assembly.lean:362:11: `if_pos` has been deprecated: Use `ite_eq_left` instead
Build completed successfully (10015 jobs).
```

### Direct Lean checks

Each following command exited 0 with output exactly empty:

```text
LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T17/Correction.lean
LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T17/ForceProfile.lean
LEAN_NUM_THREADS=6 lake env lean ../research/T17/probes/correction_canonical.lean
LEAN_NUM_THREADS=6 lake env lean ../research/T17/probes/force_profile_canonical.lean
LEAN_NUM_THREADS=6 lake env lean ../research/T17/probes/rev394_nonvacuity.lean
```

`LEAN_NUM_THREADS=6 lake env lean ../research/T17/axioms_ucan.lean`: exit 0, full exact output:
```text
'NSFormalization.Section3.T17.rescaledReference' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.rescaledForceProfile' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.spatialDerivative_rescaledReference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.rescaledReference_spatialDerivative_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.rescaledForceProfile_eq_forceProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.force_profile_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.force_profile_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.forceProfileConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.forceProfileConst_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.force_profile_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.inverseScale_correctionChartPoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.physicalForce_eq_rescaledForceProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.torusSpaceTimeLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.torusSpatialSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.torusTemporalSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.CorrectionAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.correctionStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Every printed axiom set is exactly [propext, Classical.choice, Quot.sound]. The additional concrete canonical theorem is audited by the silent #guard_msgs in its own probe.

### Repository checks

`make check`: exit 0. Its enormous repository-wide JSON output was tool-truncated; the following is the exact final excerpt, not the complete output:
```text
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```
The plan output also reports pre-existing source_hashes_match=false and copied-source admission inventory; these are not lane diagnostics or make check failures. No verification/ changes were present, so the user's conditional scripts/gates.sh and base-aware check_contracts.py gates do not apply.

`git diff --check origin/erenup/integration-section3...HEAD`: exit 0, output only:
```text
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 2fe4fb7581c09baf402f6001b716da116701b279
```

`git diff --name-only origin/erenup/integration-section3...HEAD`: exit 0, exact output:
```text
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 2fe4fb7581c09baf402f6001b716da116701b279
formalization/NSFormalization/Section3/T15/Scaling.lean
formalization/NSFormalization/Section3/T17/Correction.lean
formalization/NSFormalization/Section3/T17/ForceProfile.lean
research/T15/ATTEMPTS_UCAN.md
research/T15/REPORT_384.md
research/T15/T15_SPLIT.md
research/T15/axioms_ucan.lean
research/T15/probes/scaling_canonical.lean
research/T17/ATTEMPTS_UCAN.md
research/T17/REPORT_394.md
research/T17/T17_SPLIT.md
research/T17/axioms_ucan.lean
research/T17/probes/correction_canonical.lean
research/T17/probes/force_profile_canonical.lean
```
The matching --name-status check marks all three formalization modules A; only T15_SPLIT.md and T17_SPLIT.md are M.

Mechanical comparison output:
```text
Spec/probe literal structure identical: True
All normalized field types identical: True
Field count: 45
```

### Substantive negative checks

Reused the existing scratch file `research/T17/probes/rev394_mutation.lean:8`/:14. It changes chart time coefficient 1→2 and the main temporal-volume bound 4→2, retaining all arguments. `LEAN_NUM_THREADS=6 lake env lean ../research/T17/probes/rev394_mutation.lean`: expected exit 1, full exact output:
```text
../research/T17/probes/rev394_mutation.lean:11:2: error: Type mismatch
  inverseScale_correctionChartPoint x₀ T ε hε z
has type
  (NSFormalization.Paper1.CorrectionProfile.inverseScale ε) (correctionChartPoint x₀ T ε z - (T, x₀)) = z
but is expected to have type
  (NSFormalization.Paper1.CorrectionProfile.inverseScale ε) ((T + 2 * ε ^ 2 * z.1, x₀ + ε • z.2) - (T, x₀)) = z
../research/T17/probes/rev394_mutation.lean:20:2: error: Type mismatch
  h.force_time_length ε hε
has type
  volume (torusTemporalSupport (correctionForce ν v D ε)) ≤ ENNReal.ofReal (4 * ε ^ 2)
but is expected to have type
  volume (torusTemporalSupport (correctionForce ν v D ε)) ≤ ENNReal.ofReal (2 * ε ^ 2)
```

These are statement mutations with the expected type mismatches, not missing-argument failures. The non-vacuity probe passes independently.

Required fixes: update ATTEMPTS_UCAN row 19 to mark the canonical bridge closed; correct “forty” to “forty-five” in the conversion heading.
