ACCEPT

## 1. What the lane claims

Reviewed HEAD `8d00fa88bf5b0db8552eb234f488adadaa3ff64b` against `origin/erenup/integration` (`fa1a9a4fb829ff0bc8f38ca344fa5da531a99809`), read-only except this new report and the permitted mutation probe.

`research/R41D/REPORT_235.md:5` claims Theorem 4.1(i), for every admissible initial datum, and the if direction of (ii). The precise hypotheses are ν,T>0, q∈{1,2}, and s<2/q.toReal−3/2. These match the paper, opened with `sed -n '8,12p'` and `sed -n '176,181p' paper/sections/04-whole-space.tex`. The report expressly does not claim the iff, compact/rapid variants, or the stronger research record (`REPORT_235.md:24`).

## 2. What is in Lean

1. **Statement fidelity — pass.** `verification/Bindings/DensityFromInsertion.lean:30` has exactly the requested universally quantified statement, using `Data.BreakdownDenseR`; `:53` is exactly its zero-initial-data specialization. `:17` proves the claimed zero-force norm identity for every q,s. All three claimed implementation declarations exist.
2. **Definitions and threshold — pass.** `verification/Contracts/V1/Data.lean:672`, `:678`, `:702`, and `:707` define breakdown membership and relative density with the same force class, lifespan, force difference, and arbitrary positive ENNReal radius. The norm is the full-time measurable-path norm at `:225`, without taking its real part. `verification/Contracts/V1/Thresholds.lean:12` gives the formula used at `DensityFromInsertion.lean:42`. The only `.toReal` here is q.toReal with q=1 or 2, so no top-to-zero loophole exists.
3. **Two cases — pass.** `DensityFromInsertion.lean:35` returns g when its lifespan is ≤T; `:37` uses the genuinely zero norm, proved using `formalization/NSFormalization/Section4/D01/SmoothDatum.lean:246`. Otherwise `:39` obtains a single aligned record from `verification/Bindings/InsertionFromData.lean:87`; its convergence and lifespan adapters are at `:121` and `:113`. The exact upstream convergence is `verification/Contracts/V1/InsertionFamily.lean:323`. The positive ε₀ window and nontrivial right-neighborhood filter yield an actual ε at `DensityFromInsertion.lean:45`, not an empty-interval implication. Membership follows from `verification/Bindings/InsertionLifespan.lean:161`, and the exact lifespan yields the required ≤T at `DensityFromInsertion.lean:50`. No named analysis supplier or hidden hypothesis is added.
4. **Non-vacuity — pass.** `research/R41D/axioms_density.lean:13`, `:19`, and `:23` give density and actual approximants at ν=T=1, a=g=0, q=1, s=0, including radius 1. The admissibility facts are proved at `formalization/NSFormalization/Section4/A04/ZeroSolution.lean:71` and `:80`; both were opened. All positivity and subcriticality hypotheses have concrete proofs. Lane 233's unused `_ha` (`InsertionFromData.lean:95`) does not make this vacuous: reference existence already supplies initial regularity, and no extra premise was inserted.
5. **Hygiene — pass.** The forbidden-token/maxHeartbeats search in both new binding modules and the density audit returned no matches. There are no heartbeat overrides. The three-dot diff contains only new Lean modules; its sole modified existing file is the expressly requested comparison record. All five printed axiom lists are exactly the required three. The new module is selected by `experiments/build_changed_lean.py:17`, invoked in `.github/workflows/contracts.yml:81`; dry-run output is reproduced below. It need not be in an existing registered contract closure to receive CI compilation.

## 3. Gaps and negative check

No blocking findings or required fixes.

The scope limits are honest. `research/R41D/COMPARISON.md:99` distinguishes plain density from `research/R41D/Spec.lean:121`'s stronger record, which retains branch and insertion witnesses; those fields are not falsely claimed as constructed. The draft force-class restriction is at `Spec.lean:77`.

Before accepting the absence claims, ran whole-tree searches:
```sh
grep -rnE 'not_breakdownDenseR|MemForceRapid|initialClassSchwartz|forceSobolevENorm.*zero|RDensityAPI|memForceRapid' formalization/NSFormalization/Section4
grep -rnEi 'MemForceRapid|forceClassRapid|initialClassSchwartz|RDensityAPI|R42InsertedWitness|breakdownDenseR|memForce.*rapid|schwartz.*subset' formalization/NSFormalization/Section4
```
Only the q=1 density-obstruction declarations matched: `formalization/NSFormalization/Section4/R41/NonDensityL1.lean:78,105,106,116,117`. No q=2 obstruction, rapid-class bridge, Schwartz-class inclusion, or packaged RDensityAPI was found in this tree. Read-only `git show erenup/232-R41-nondensity-both:formalization/NSFormalization/Section4/R41/NonDensityL2.lean` confirms the sibling q=2 result exists there. G2–G4 remaining outside this lane is consistent with this search. G5 is explicitly closed by `DensityFromInsertion.lean:17`, as the comparison's new status at `:96` says. Existing compact-difference support is real: `verification/Contracts/V1/DatumLemmas.lean:381`; the earlier regularity-margin interface is at `verification/Contracts/V1/MaximalPartial.lean:200,209`.

The inherited import caveat is accurately identified by duplicate declarations at `verification/Bindings/Packet.lean:65` and `verification/Bindings/Scaling.lean:58`, documented in `InsertionFromData.lean:27`. No repair is required in this lane.

**Substantive mutation:** copied the main proof into `research/R41D/probes/rev235_threshold.lean`, retaining every argument and changing only its hypothesis bound from s<2/q−3/2 to s<2/q−1/2 (`:32`). This widens the claimed subcritical interval by one. The original proof fails precisely when trying to supply the true convergence threshold:
```text
../research/R41D/probes/rev235_threshold.lean:42:6: error: Type mismatch: After simplification, term
  hs
 has type
  s < 2 / q.toReal - 1 / 2
but is expected to have type
  s < 2 / q.toReal - 3 / 2
```
Exit 1, six output lines, 199 bytes. This is a statement mutation, not a dropped argument.

## 4. Commands and results

Read `CLAUDE.md`, the lane-review skill, `NEXT_SESSION.md`, HANDOFF §0/§2 P10, top 40 LESSONS lines, brief references, worker report, attempts, comparison, and lane 233 report. Used the existing installed environment; did not run the installer or make git state changes. Every Lean shell sourced `scripts/lean-env.sh` and exported `LEAN_NUM_THREADS=6`. Direct lake commands ran from `verification/`; repository make targets use `lake -d verification`.

Long outputs below are exact excerpts with omissions marked, limited to at most the first/last 40 lines rather than copying ~30,000-line closure inventories.

| Command | Result |
|---|---|
| `lake build Bindings.DensityFromInsertion` | exit 0; only existing dependency diagnostics, no module diagnostics |
| `lake env lean Bindings/DensityFromInsertion.lean` | exit 0; exactly 0 lines / 0 bytes |
| `lake env lean ../research/R41D/axioms_density.lean` | exit 0; five standard axiom lists below |
| `lake env lean ../research/R41D/probes/rev235_threshold.lean` | expected exit 1, exact error above |
| `make check` | exit 0; 30,031 lines / 1,234,065 bytes |
| `make test` | exit 0; 360 lines / 22,793 bytes |
| `bash scripts/gates.sh Bindings.DensityFromInsertion` | exit 0; 30,179 lines / 1,244,616 bytes; includes mutation suite |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | exit 0; 29,999 lines / 1,233,094 bytes |
| `git diff --check` | exit 0; no output |
| forbidden-token / maxHeartbeats `rg` | exit 1; no matches |

Exact audit output:
```text
'BlowupDensity.Bindings.density_forceSobolevENorm_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.breakdownDenseR_of_subcritical' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.breakdownDenseR_zero_of_subcritical' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.DensityAudit.zero_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.DensityAudit.zero_reference' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exact `make check` tail:
```text
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
Its earlier inventory reports `source_hashes_match: false` and an existing copied `Paper1.BoundaryCorollary` sorry. These are repository-wide inventory diagnostics, not admissions reachable from the audited density theorems; the gate exits 0 and their transitive axiom audits pass.

Exact `git diff --name-only origin/erenup/integration...HEAD`:
```text
research/R41D/ATTEMPTS_DENSITY.md
research/R41D/ATTEMPTS_G1.md
research/R41D/COMPARISON.md
research/R41D/REPORT_233.md
research/R41D/REPORT_235.md
research/R41D/axioms_density.lean
research/R41D/axioms_insertion_from_data.lean
verification/Bindings/DensityFromInsertion.lean
verification/Bindings/InsertionFromData.lean
```
`git diff --name-status` marks only COMPARISON as M and all other paths A.

Exact CI selection command/output:
```text
$ python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run
Changed Lean modules: Bindings.DensityFromInsertion
```

Build output (exact first/last 40 lines):
```text
⚠ [9292/10016] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9876/10016] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9877/10016] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9886/10016] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9889/10016] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]
[... middle omitted ...]
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9924/10016] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
ℹ [9976/10016] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [9980/10016] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
⚠ [9987/10016] Replayed NSFormalization.Source.BoundedViscosityUniqueness
warning: NSFormalization/Source/BoundedViscosityUniqueness.lean:21:28: This simp argument is unused:
  one_smul

Hint: Omit it from the simp argument list.
  [apply] simp only [smul_smul, h₂, smul_add, smul_sub]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (10016 jobs).

```

make test output (exact captured first/last 40 lines):
```text
COMMAND make test: exit=0; lines=360; bytes=22793
lake -d verification test
⚠ [8778/8849] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9876/10680] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9877/10680] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10271/10680] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR

Note: This linter can be disabled with `set_option linter.unusedVariables false`
[... middle omitted ...]
ℹ [10625/10680] Replayed Tests.InsertionFamily
info: Tests/InsertionFamily.lean:19:0: Contract BlowupDensity.Tests.checkedInsertionFamily: checked; standard logical axioms only
ℹ [10629/10680] Replayed Tests.RegularityPartial
info: Tests/RegularityPartial.lean:17:0: Contract BlowupDensity.Tests.checkedRegularityPartial: checked; standard logical axioms only
ℹ [10637/10680] Replayed Tests.BochnerPartial
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
```

scripts/gates.sh output (exact captured first/last 40 lines):
```text
COMMAND gates: exit=0; lines=30179; bytes=1244616
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
    "I01.packet": [
      "Bindings.Packet",
      "Contracts.V1.Packet",
      "NSFormalization.Paper1.ScalarEnergy",
      "NSFormalization.Section4.I01.Energy",
[... middle omitted ...]
info: Tests/Scaling.lean:18:0: Contract BlowupDensity.Tests.checkedScaling: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:18:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionV4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
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
```

base compatibility output (exact captured first/last 40 lines):
```text
COMMAND contracts: exit=0; lines=29999; bytes=1233094
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
      "NavierStokes.ActualCandidateAssembly",
      "NavierStokes.ActualCandidateConstruction",
      "NavierStokes.ActualCarrierGeometry",
      "NavierStokes.ActualCarrierTransport",
      "NavierStokes.ActualCarrierTransportBase",
[... middle omitted ...]
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
      "Tests.CriticalRegularity"
    ]
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

Fixes: none.

