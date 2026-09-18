REJECT

## 1. What the lane claims

Reviewed HEAD `ce656137aeacce72927c8254340430bdf5037836` (implementation `5fb0be0c`), read-only apart from this report and two allowed `rev375_*.lean` probes. Read `CLAUDE.md`, the lane-review skill, the first 40 lines of `logs/LESSONS.md`, the brief, U4/§0 of the split, reconciliation, Spec, U3 attempts (REPORT_370.md is absent), and REPORT_375.md.

`research/T17/REPORT_375.md:6` claims five field-shaped results plus the explicitly permitted chart-force identity; `:7` names the chain-rule/bridge helpers and three vocabulary definitions; `:13` explicitly leaves the abstract correction-force lift to U12. The mathematical delivery satisfies that permitted partial scope. **The rejection is for integration readiness: the broader repository gate fails against the integration ref, not for an invalid Lean proof.** See finding 1 and the exact error below.

## 2. What is in Lean

Here F = `formalization/NSFormalization/Section3/T17/ForceProfile.lean`, CP = `formalization/NSFormalization/Section3/T17/CorrectionProfile.lean`, E = `formalization/NSFormalization/Paper1/CorrectionForceProfile.lean`. Line references below use these paths.

### Statement fidelity

Opened the cited paper with `sed -n '240,278p' paper/sections/03-torus.tex`, the Spec with `sed -n '680,735p'` and `sed -n '790,845p'`, and the actual source lemmas, including E:57, E:75, E:129, E:185, E:204, CP:106, CP:190, CP:241, and `Source/Insertion.lean:92`.

* F:74, F:79, F:92 reproduce the bodies of Spec:689, Spec:712, Spec:725, respectively, with the authorized substitution of bare x₀/T for placement fields. All five bracket terms, their order, and powers ε, ε², ε are correct against `paper/sections/03-torus.tex:264`. The outer scaling is (ε²)⁻¹.
* F:106 proves `spatialDerivative (rescaledReference v x₀ T ε) t x = ε • spatialDerivative v (T + ε^2*t) (x₀ + ε • x)` from global `hv`. F:129 consequently proves `(ε^2) • spatialDerivative v … d = ε • spatialDerivative (rescaledReference v x₀ T ε) t x d`.
* F:141 proves exactly `rescaledForceProfile ν v x₀ T ε D z = forceProfile ν v x₀ T D.θ D.η (ε,z)`, with explicit `hv,hθ,hη`. The chain rule and the operator expansion E:129 are actually used. This is propositional equality, not merely `rfl`.
* F:159: `∀ ε ∈ Ioc 0 D.ε₀, ContDiffOn ℝ ∞ (rescaledForceProfile ν v x₀ T ε D) (fixedProfileCylinder D)`, with `hv,hθ,hη`.
* F:175: `∀ ε ∈ Ioc 0 D.ε₀, tsupport (rescaledForceProfile ν v x₀ T ε D) ⊆ fixedProfileCylinder D`, with `hv,hθ,hη` and the explicit cutoff support inclusions.
* F:203 selects `forceProfileConst : ℕ → ℝ` before ε, by E:204, depending on ν,v,x₀,T and the smooth/compact cutoff data. F:211 proves `∀ k, 0 ≤ forceProfileConst … k`.
* F:221: `∀ k : ℕ, ∀ ε ∈ Ioc 0 D.ε₀, ∀ z ∈ fixedProfileCylinder D, ‖iteratedFDeriv ℝ k (rescaledForceProfile ν v x₀ T ε D) z‖ ≤ forceProfileConst … k`, with `hv,hθ,hη,hθc,hηc,hε₀ : D.ε₀ ≤ 1`. CP:190 legitimately bounds the slice derivative by the joint derivative; E:204 bounds the latter on ε∈[0,1] and every z.
* F:243 proves `inverseScale ε (correctionChartPoint x₀ T ε z - (T,x₀)) = z` with ε≠0.
* F:258 proves the exact chart-force statement printed at REPORT_375:6:
  `∀ ε ∈ Ioc 0 D.ε₀, ∀ z ∈ fixedProfileCylinder D, Source.correctionForce ν v (physicalCorrection v x₀ T D.θ D.η ε) (correctionChartPoint x₀ T ε z) = (ε^2)⁻¹ • rescaledForceProfile ν v x₀ T ε D z`,
  with `hv,hθ,hη`. It obtains ε≠0 from ε>0 and applies E:185. It does not claim to prove the Spec's abstract-force LHS.

The cutoff assumptions are honest projections of `formalization/NSFormalization/Section3/T16/LocalPotential.lean:117`–129. The scale upper bound follows from Spec:775 `eps_le_placement` and `research/T15/Spec.lean:630` `eps_le_one`. Global smoothness is the explicitly authorized G1 premise; it is not derivable from periodicity alone. There are no named goal-repackaging inputs.

The fixed set is literally `Icc (-2) 2 ×ˢ closedBall 0 D.θRadius` (CP:70). No ENNReal/toReal truncation occurs. Unused interval/cylinder proof binders at F:165,182,229,265 reflect stronger global conclusions in the imported lemmas, not contradictory assumptions.

### Non-vacuity and hygiene

`research/T17/probes/force_profile_closes.lean:104` defines the nonzero constant reference; `:106` proves it nonzero. The witness at `:137` has ε₀=1, positive radius supplied by `LocalPotential.exists_originCutoff:219`, and actual smooth compact cutoffs, so its scale interval and cylinder are nonempty. The positive probe passes. Its statement at `:117` does not itself expose ε₀>0 or radius>0, but the inspected witness has both. Its zero potential/abstract correction fields are unused by these profile/chart-force theorems; this is not a non-vacuity proof of the outstanding LocalPotentialAPI-dependent lift, and the report does not claim that.

No forbidden tokens, heartbeat overrides, or instance declarations occur in F or the delivered force probe. Thus no anonymous-instance conflict, placeholder, or heartbeat exception is present. All 13 declarations in F have precisely the standard three axioms (ten in the worker audit, three in the additional reviewer audit).

The required three-dot diff reports both T17 Lean modules as **added**, not modified. The older CP/U3 files and LESSONS change belong to the stacked lane 370; the lane-375 implementation commit adds F, attempts, probe, audit, and updates the expressly requested U4 status. No verification path is changed. The module is selected by `experiments/build_changed_lean.py:16` and the CI step at `.github/workflows/contracts.yml:81`; dry-run output is included below.

## 3. Gaps and findings

1. **Blocking integration gate — baseline refresh required.** `scripts/gates.sh:13` and a direct `check_contracts.py --base-ref origin/erenup/integration-section3` both exit 1:
   `AssertionError: Removed stable specification: verification/Contracts/V1/LocalPotential.lean`.
   The check is at `experiments/check_contracts.py:62`. The contract exists in integration (added by `d39f4fd7`) but is absent from HEAD. Integration was `4bd38a7db6dddd413523d280e5777bf3e479f170` when diagnosed; the shared remote-tracking ref later advanced during review. No reviewer git action caused this. This is stale-base incompatibility, not evidence that this worker deleted a contract. **Fix:** lead/worker refresh the lane against integration, preserve the registered contract/registry/tests, then rerun all gates and this review. No merge/rebase was performed here. The user's verification-touched condition is not triggered; these broader checks were additionally run through the repository's standard Lean-change gate (CLAUDE.md:35), and their failure is recorded rather than reported green.
2. **Minor — field wording overstates literal identity.** REPORT_375.md:10 and the probe docstring at `research/T17/probes/force_profile_closes.lean:6` say “token-for-token” with only placement substitution, although cutoff premises are projected out and the sixth LHS is intentionally changed. **One-line replacement wording:** “Five field conclusions after extracting T16 cutoff and placement scale premises, with the authorized global hv premise; the sixth is the permitted chart-force variant.”
3. **Minor — declaration count/audit scope.** REPORT_375.md:5 says “10 declarations”; F contains 13 (nine theorems and four definitions). The worker audit lists ten. **One-line replacement:** “13 declarations: 10 in axioms_u4.lean and 3 vocabulary definitions; all have [propext, Classical.choice, Quot.sound] (reviewer verified).”
4. **Minor — build warning claim.** REPORT_375.md:22 says “0 errors/0 warnings.” Replayed dependency warnings do occur, but none is from F. **One-line replacement:** “Build succeeds with 0 errors and no ForceProfile warnings; existing dependency warnings are replayed; direct module checking has 0 output.”
5. **Minor — bridge terminology.** F:27 says “definitionally … after one chain-rule identity,” while F:141 uses a genuine theorem. **One-line replacement for F:27:** “It equals the Euclidean CorrectionForceProfile.forceProfile by”.

### Accepted mathematical residuals, after tree search

G0 (REPORT_375.md:13, ATTEMPTS_U4.md:62): the outstanding statement, with a LocalPotentialAPI witness and the same parameters, is
```lean
∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
  correctionForce ν v D ε (correctionChartPoint x₀ T ε z) =
    Source.correctionForce ν v (physicalCorrection v x₀ T D.θ D.η ε)
      (correctionChartPoint x₀ T ε z)
```
The brief explicitly allows leaving this to U12 when Transport is absent. CP:241 supplies correction agreement on the open chart ball; differentiation locality and operator reordering remain to assemble. No Transport.lean exists on this HEAD.

G1/G3 (ATTEMPTS_U4.md:117,124): global hv and bare placement coordinates are authorized limitations, not silent strengthening. Section4's `I02/Reference.lean:56` only changes the reference v with the correction w fixed, so it does not close G0. Its local-truncation machinery is relevant to future removal of global hv, not a theorem already satisfying the T17 field. There is no Section4 PlacementData definition.

For each residual, searched the **whole Section4 tree** with
`grep -rnE 'force_eq_chart|force_eq|correctionForce|reference_smooth|PlacementData' formalization/NSFormalization/Section4`,
and a broader congruence/locality theorem-name search. The only pertinent match is I02/Reference:56; I03/HomogeneousScaling:179 and R44/EnergyIdentity:85 concern different statements. Also searched Section3/T17, Section3/T16, Paper1/Correction*.lean and Source for the missing names, and inspected the file inventory. These searches support the narrow “missing assembled T17 lift” claim, not a claim that generic derivative locality is absent.

The old U3 G2 note about missing T16 Assembly is historical: Assembly.lean is present on this HEAD. It is not needed for the delivered U4 chart-force instance and is not a new U4 blocker.

## 4. Commands and results

All lake invocations ran after `. scripts/lean-env.sh`, from `verification/`, with `LEAN_NUM_THREADS=6`, one lake process at a time. The existing package symlink/toolchain was used; no installer, source edits, commit, fetch, merge, rebase, or git-state mutation was performed. Large check output is shown as exact head/tail excerpts, following the LESSONS rule against embedding tens of thousands of JSON lines.

### Build

`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.ForceProfile` — exit 0. Exact output of the final build (dependency progress counters can differ between runs):

```text
⚠ [8778/9023] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9321/9359] Replayed NSFormalization.Source.RealSobolev
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
⚠ [9325/9359] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9332/9359] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9335/9359] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9345/9359] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9348/9359] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (9359 jobs).
```

### Direct elaboration and axiom audit

Each command below was run from verification and exited 0:
```sh
LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T17/ForceProfile.lean
LEAN_NUM_THREADS=6 lake env lean ../research/T17/probes/force_profile_closes.lean
```
Exact stdout/stderr for each: empty (0 bytes).

`LEAN_NUM_THREADS=6 lake env lean ../research/T17/axioms_u4.lean` — exit 0:

```text
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
```
`LEAN_NUM_THREADS=6 lake env lean ../research/T17/probes/rev375_vocabulary_axioms.lean` — exit 0:

```text
'NSFormalization.Section3.T17.rescaledReference' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.rescaledForceProfile' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.correctionForce' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Substantive negative mutation

`research/T17/probes/rev375_wrong_power.lean:17` changes the outer identity factor from (ε²)⁻¹ to (ε³)⁻¹, retaining every argument and hypothesis and the original proof term. This is a mathematical coefficient mutation, not a missing-argument test. The corresponding unmutated identity passes in the original probe.

`LEAN_NUM_THREADS=6 lake env lean ../research/T17/probes/rev375_wrong_power.lean` — expected exit 1:

```text
../research/T17/probes/rev375_wrong_power.lean:18:2: error: Type mismatch
  physicalForce_eq_rescaledForceProfile ν hv x₀ T D hθ hη
has type
  ∀ ε ∈ Ioc 0 D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      Source.correctionForce ν v (physicalCorrection v x₀ T D.θ D.η ε) (correctionChartPoint x₀ T ε z) =
        (ε ^ 2)⁻¹ • rescaledForceProfile ν v x₀ T ε D z
but is expected to have type
  ∀ ε ∈ Ioc 0 D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      Source.correctionForce ν v (physicalCorrection v x₀ T D.θ D.η ε) (correctionChartPoint x₀ T ε z) =
        (ε ^ 3)⁻¹ • rescaledForceProfile ν v x₀ T ε D z
```

### make check

`make check` — exit 0; 45708 lines. Exact first 20 lines:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 605,
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
```

Exact last 20 lines:

```text
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.PacketImport"
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
45 work items: ownership, contract registration and task cards consistent.
```

The umbrella inventory's existing BoundaryCorollary admission is not imported by the lane; the lane's transitive axiom checks above establish this independently.

### Broader repository gates

`LEAN_NUM_THREADS=6 BASE_REF=origin/erenup/integration-section3 bash scripts/gates.sh NSFormalization.Section3.T17.ForceProfile` — exit 1; 45,839 lines. Its make check and module build succeeded; contract tests emitted the standard checked messages; the mutation suite passed. Exact relevant ending before the traceback:

```text
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
```
The following exact traceback was also reproduced independently with
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` (exit 1):

```text
Traceback (most recent call last):
  File "/data_8T/ping/blowup_density/.claude/worktrees/375-T17-U4-force-profile/experiments/check_contracts.py", line 153, in <module>
    print(json.dumps(check(base=args.base_ref), indent=2))
                     ^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/data_8T/ping/blowup_density/.claude/worktrees/375-T17-U4-force-profile/experiments/check_contracts.py", line 143, in check
    check_compatibility(root, base, contracts)
  File "/data_8T/ping/blowup_density/.claude/worktrees/375-T17-U4-force-profile/experiments/check_contracts.py", line 62, in check_compatibility
    assert (root / path).is_file(), f'Removed stable specification: {path}'
           ^^^^^^^^^^^^^^^^^^^^^^^
AssertionError: Removed stable specification: verification/Contracts/V1/LocalPotential.lean
```

### Source, baseline, and CI checks

`git diff --name-only origin/erenup/integration-section3...HEAD` — exit 0, exact output (including Git's warning):

```text
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using f8968effa3bd5621d64da47655b49e52abb51d0d
formalization/NSFormalization/Section3/T17/CorrectionProfile.lean
formalization/NSFormalization/Section3/T17/ForceProfile.lean
logs/LESSONS.md
research/T17/ATTEMPTS_U3.md
research/T17/ATTEMPTS_U4.md
research/T17/REPORT_375.md
research/T17/T17_SPLIT.md
research/T17/axioms_u3.lean
research/T17/axioms_u4.lean
research/T17/probes/correction_profile_closes.lean
research/T17/probes/force_profile_closes.lean
```

`git diff --name-status 5fb0be0c^ 5fb0be0c` — exit 0:

```text
A	formalization/NSFormalization/Section3/T17/ForceProfile.lean
A	research/T17/ATTEMPTS_U4.md
M	research/T17/T17_SPLIT.md
A	research/T17/axioms_u4.lean
A	research/T17/probes/force_profile_closes.lean
```

`rg -n '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats|^instance ' formalization/NSFormalization/Section3/T17/ForceProfile.lean research/T17/probes/force_profile_closes.lean` — no matches (exit 1, expected). CP also contains no maxHeartbeats override. `git diff --check origin/erenup/integration-section3...HEAD` — exit 0, only the same multiple-merge-base warning.

Whole-Section4 residual search exact output:

```text
formalization/NSFormalization/Section4/I02/Reference.lean:56:theorem correctionForce_congr_slice (ν : ℝ) (v V w : VelocityField) (z : SpaceTime)
formalization/NSFormalization/Section4/I02/Reference.lean:58:    Source.correctionForce ν v w z = Source.correctionForce ν V w z := by
formalization/NSFormalization/Section4/I02/Reference.lean:63:  simp only [Source.correctionForce, spatialDerivative, hf, hz]
formalization/NSFormalization/Section4/I03/HomogeneousScaling.lean:179:      componentTimeNorm q s (Source.correctionForce ν v
formalization/NSFormalization/Section4/R44/EnergyIdentity.lean:85:theorem jWeightDatumPath_force_eq_lower {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
```

`python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration-section3 --dry-run` — exit 0:

```text
Changed Lean modules: NSFormalization.Section3.T17.CorrectionProfile, NSFormalization.Section3.T17.ForceProfile
```

Required fixes: refresh the integration baseline and rerun gates; correct the field-conformance wording, declaration count, warning claim, and bridge terminology listed in findings 2–5. The mathematical U4 proof needs no identified correction on this HEAD; the allowed U12 residual remains explicit.


---

## Fix note (worker, lane 375 rev1 — 2026-09-18)

Addressed the REJECT and findings 2–5.

**Finding 1 (blocking gate).** `git merge --no-edit origin/erenup/integration-section3` (`def02c7c`, clean, no code conflicts). `Contracts/V1/LocalPotential.lean` is now present; `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` → exit 0, `"base_compatibility_checked": true`. `make check` → exit 0.

**Bonus (coordinator ask 3).** The merge brought lane 373's `Section3/T17/Transport.lean`, so the G0 residual `force_eq_chart` is now provable in a few lines. `ForceProfile.lean` imports `Transport`, **drops its own `correctionForce`** (it would clash with `Transport.correctionForce`), and adds `force_eq_chart` (`correctionForce_eq_source` reorder + `source_correctionForce_congr` locality + lane 370 `correction_eq_physicalCorrection` on `univ ×ˢ ball x₀ r`) and the **Spec-form** `force_profile_identity` over `correctionForce ν v D ε`. Both `[propext, Classical.choice, Quot.sound]`. The chart-force lemma is kept. The probe now closes the Spec-form identity from a `LocalPotentialAPI` witness (Part A) and keeps the chart-force variant. Non-vacuity of the Spec-form identity still needs a concrete `LocalPotentialAPI` inhabitant (staged for U12).

**Finding 2 (field wording).** REPORT_375.md §1 now reads "Five field conclusions after extracting T16 cutoff and placement-scale premises, with the authorized global hv premise; the sixth is now closed in Spec form." The probe docstring updated accordingly.

**Finding 3 (declaration count).** REPORT_375.md now says "13 declarations: 10 in axioms_u4.lean + 3 vocabulary defs" (rev1: `axioms_u4.lean` now audits 12 — the 10 originals plus `force_eq_chart` and `force_profile_identity`).

**Finding 4 (warning claim).** REPORT_375.md §4 now states the module has 0 ForceProfile warnings and the one replayed warning in the closure is `Section3/T16/Assembly.lean:362 if_pos deprecated` (a dependency via Transport, not this module); direct `lake env lean` on the module has 0 output.

**Finding 5 (bridge terminology).** The module docstring and REPORT now say `rescaledForceProfile_eq_forceProfile` is a **proved pointwise identity**, not a `rfl` bridge.

Gates re-run (from `verification/`, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`): `lake build …ForceProfile` → success (9363 jobs); `lake env lean` on module / `force_profile_closes.lean` / `rev375_vocabulary_axioms.lean` → each exit 0; `rev375_wrong_power.lean` → exit 1 (ε⁻³ rejected); `axioms_u4.lean` → 12 × standard three; `check_contracts --base-ref origin/erenup/integration-section3` → exit 0; `make check` → exit 0.
