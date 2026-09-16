ACCEPT

## 1. What the lane claims

Reviewed HEAD `807e728e4eb1f7a63176c32cded5790ddcf374fc` against
`origin/erenup/integration = 417c0cc76354503ee78930bafda89553aa865339`.
The working tree was initially clean. Read CLAUDE.md, the lane-review skill,
the top 40 LESSONS lines, the brief, REPORT_259, ATTEMPTS_CLOSURE,
RECONCILIATION, COMPARISON, Spec, and the requested suppliers.

`research/R46/REPORT_259.md:3` claims the two literal Spec conclusions,
conditional only on `I03.CompactHomogeneousRealization`; `:7` claims seven
supporting lemmas, both zero specializations, and the scaling powers 3/2 and
1/2. `:14` explicitly excludes a new mixed-Lebesgue/Sobolev bridge.
These claims are accurate within that stated scope.

## 2. What is in Lean

1. **Statement fidelity — pass.** The conclusions at
   `verification/Bindings/CompletedClosure.lean:124` and `:199` are
   byte-identical (including whitespace after the declaration separator) to
   `research/R46/Spec.lean:130` and `:103`, respectively. The only preceding
   binder is the permitted realization assumption (`:123`, `:198`).
   All five pins, the positive viscosity/time/margin, raw reference,
   per-scale force membership, exact lifespan, full solution witness, energy
   limit, and simultaneous three-term force limit are preserved.
   Paper lines were opened with `sed -n '218,296p'` and `sed -n '31,43p'`.
   The density matches `paper/sections/04-whole-space.tex:219`; the homogeneous
   estimates match `:264`–`:272`, with source power 1/2 and correction
   power 3/2. The literal mixed-norm qualification is recorded in part 3.

2. **Supporting declarations — pass.** All seven exist with the statements
   used by the main proofs: pairability (`CompletedClosure.lean:16`),
   subtraction (`:26`), addition (`:37`), norm identification (`:51`),
   triangle inequality (`:62`), homogeneous convergence (`:79`), and
   compact relative homogeneous density (`:173`).
   Pairability supplies the integrability premises of
   `formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:583`;
   uniqueness at `:443` identifies the infimum, rather than assuming that an
   arbitrary representative attains it.

3. **Construction — pass.** The strong theorem constructs directly from R
   (`CompletedClosure.lean:154`), so the global pressure/velocity pins are
   reflexive, not a misuse of slab uniqueness. The supplied lifespan and solution
   lemmas were opened at `verification/Bindings/InsertionLifespan.lean:228`
   and `:319`. Energy convergence is the squeeze theorem at
   `verification/Bindings/MainThresholds.lean:65`; Sobolev convergence is the
   registered `verification/Contracts/V1/InsertionFamily.lean:323` at the two
   strictly subcritical pairs. The homogeneous triangle and powers use
   `verification/Bindings/ScalingHomogeneous.lean:134` and `:192`.
   The density proof uses B02's actual completed compact approximation
   (`verification/Contracts/V2/HomogeneousPartial.lean:190`,
   `verification/Bindings/HomogeneousPartialV2.lean:99`,
   `formalization/NSFormalization/Section4/B02/ApproxCompact.lean:229`),
   then the lifespan split and lane 233 record
   (`verification/Bindings/InsertionFromData.lean:87`).
   Compactness follows from `verification/Bindings/CompactClassDensity.lean:31`.
   Path addition and the strict half-radius triangle close the completed
   conclusion at `CompletedClosure.lean:211`–`:222`.
   Also read lane 256's CompletedSobolevDensity via `git show`.

4. **Non-vacuity and hypotheses — pass, conditional as requested.**
   `verification/Contracts/V1/Data.lean:732` quantifies every finite measurable
   datum and positive radius and demands an actual force and measurable
   homogeneous path. Its norm is ENNReal-valued (`:390`), as is energy
   (`:475`); no norm is erased through top.toReal.
   The scaling supplier's conversions require finite constants
   (`ScalingHomogeneous.lean:121`, `:145`, `:200`).
   T > 0 avoids empty energy intervals; `InsertionFamily.lean:160`
   gives A.ε₀ > 0 and the right-hand limit filter is nontrivial.
   The unused `_ha` in `CompletedClosure.lean:149` is an inherited Spec
   premise, not an added restrictive hypothesis: R already supplies the
   reference data. The sole named input is precisely measurability of the
   canonical compact homogeneous path for all smooth compact fields
   (`ScalingHomogeneous.lean:27`); it imposes no artificial zero-field or
   inconsistent horizon restriction. Its global truth is not proved here.
   The accepted examples are `CompletedClosure.lean:225` (a=b=0, ν=T=1)
   and `research/R46/axioms_closure.lean:20` (a=g=0, ν=T=δ=1, actual zero
   classical reference). They retain the expressly authorized hreal condition;
   they are not a proof of that condition.

5. **Build, axioms, hygiene, and CI — pass.** Direct Lean checking emitted zero
   bytes. Every one of the nine named declarations printed exactly the standard
   three axioms. No prohibited proof token or heartbeat override occurs in either
   delivered Lean file. The three-dot diff contains only the four new files and
   the explicitly requested COMPARISON update; no existing Lean module/test was
   modified. Build diagnostics all belong to suppliers, not this module.
   `experiments/build_changed_lean.py:19` selects new verification modules;
   its dry run selects Bindings.CompletedClosure, and
   `.github/workflows/contracts.yml:81` runs it. This module is therefore
   covered by changed-module CI even though it is not a new registered contract.

6. **Substantive negative check — pass.**
   `research/R46/probes/rev259_lifespan_mutation.lean:16` changes the strong
   theorem's specialized exact-lifespan conclusion from ofReal 1 to ofReal 2.
   Reference time, solution horizon, viscosity, all other conjuncts, and every
   proof argument remain unchanged. Lean exits 1 at `:26` with Type mismatch:
   the theorem supplies lifespan 1 but the goal demands lifespan 2.
   The unmutated zero example passes in the audit. This is a changed constant,
   not a missing-argument test. The probe is intentionally failing and is outside
   the production build.

## 3. Gaps

No blocking gap or required fix for the two requested conditional Spec fields.

- **Disclosed vocabulary boundary:** `REPORT_259.md:16`,
  `ATTEMPTS_CLOSURE.md:56`, and `COMPARISON.md:99` correctly distinguish
  `forceSobolevENorm 1 0` from the paper's literal L¹L² term
  (`paper/sections/04-whole-space.tex:224`).
  The definitions at `Data.lean:225` and `:251` use different carriers.
  This review accepts the explicitly mandated verbatim Spec, not a newly
  established equality with mixedLebesgueENorm.
- **External realization:** the permitted assumption remains external in this
  checked tree. Whole-Section4 searches found norm measurability at
  `I03/HomogeneousScaling.lean:304`, which is weaker than path measurability,
  and a conditional path result at `D01/HomogeneousWitness.lean:692`.
  `verification/Bindings/ScalingHomogeneous.lean:262` proves the zero case,
  not the universal input. The report does not claim otherwise.
- **“Not in the tree” verification:** ran `grep -rn` across the entire
  `formalization/NSFormalization/Section4` tree for
  `isHomogeneousPath_add|[Hh]omogeneous.*[Aa]dd|mixedLebesgueENorm|CompactHomogeneousRealization`,
  then the broader
  `homogeneous.*(path|slice).*(add|sub)|mixed.*(sobolev|lebesgue)|sobolev.*mixed|compact.*homogeneous.*realization`.
  No unrestricted homogeneous path-addition theorem was found, supporting
  `ATTEMPTS_CLOSURE.md:40`. The search does find the integrability-qualified
  subtraction at `D01/HomogeneousWitness.lean:583` and its wrapper at
  `B02/LebesgueDatum.lean:446`; these are the relevant available results.
  Mixed results at `I02/Mixed.lean:108` and `I03/Mixed.lean:162` concern
  Lebesgue slice paths/scaling, not the claimed missing Sobolev equality.
  Both files were opened. A further search for
  `approxCompactHomogeneous|[Hh]omogeneous.*[Cc]onvergence|homogeneous_time_scaling_epsilon`
  found B02 approximation at `B02/ApproxCompact.lean:229` and homogeneous
  scaling at `I03/HomogeneousScaling.lean:69`. Thus the historical open
  dependency bullets at `COMPARISON.md:60` are superseded exactly as its
  lane update explicitly says at `:81`; they are not current gaps.
- **Build output qualification:** raw lake build is not silent because Lake
  replays supplier diagnostics. There are zero diagnostics from CompletedClosure.
  This matches `REPORT_259.md:25` and the review requirement of silence
  for this module. No supplier edits are required.

## 4. Commands and results

Lake was run one invocation at a time, from verification/, after sourcing
scripts/lean-env.sh, with LEAN_NUM_THREADS=6. The existing environment was ready;
no installer or git mutation was run. For make test and gates, an exported Bash
function translated the existing make recipe's `lake -d verification test`
to an actual invocation from verification/. The commands were:

```bash
. scripts/lean-env.sh
export LEAN_NUM_THREADS=6
lake() {
  if [ "$1" = "-d" ] && [ "$2" = "verification" ]; then
    shift 2
    (cd verification && command lake "$@")
  else
    command lake "$@"
  fi
}
export -f lake
export MAKEFLAGS='SHELL=/bin/bash'
make test
scripts/gates.sh Bindings.CompletedClosure
python3 experiments/check_contracts.py --base-ref origin/erenup/integration
```

The standalone make test exit was checked independently because gates.sh filters
its output and masks its status. Both it and the explicit base-ref check exited 0.
For the very large architecture JSON and replay logs, exact head/tail excerpts
are shown with omissions marked, following LESSONS.md's report-size guidance.
No omitted text is represented as empty output.

Statement comparison (Python extracted each Spec field after its colon and each
theorem after the hreal binder, stopping before the proof):

```text
completedHomogeneousDensity: byte-identical=True
strongTrajectoryClosure: byte-identical=True
```

`git diff --name-only origin/erenup/integration...HEAD` (exit 0):

```text
research/R46/ATTEMPTS_CLOSURE.md
research/R46/COMPARISON.md
research/R46/REPORT_259.md
research/R46/axioms_closure.lean
verification/Bindings/CompletedClosure.lean
```

`rg -n '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats' verification/Bindings/CompletedClosure.lean research/R46/axioms_closure.lean`:
exit 1, zero output (no matches).
`git diff --check origin/erenup/integration...HEAD`: exit 0, zero output.

`python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run`
(exit 0):

```text
Changed Lean modules: Bindings.CompletedClosure
```

`cd verification && LEAN_NUM_THREADS=6 lake build Bindings.CompletedClosure` — exit 0; exact head/tail:

```text
⚠ [8778/9155] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9876/10629] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9877/10629] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10272/10629] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:30: Variable name `hB` is not explicitly referenced.
[middle omitted]
⚠ [10516/10629] Replayed NSFormalization.Section4.A01.AprioriFamily
warning: NSFormalization/Section4/A01/AprioriFamily.lean:148:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10517/10629] Replayed NSFormalization.Section4.A01.MildGronwall
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10573/10629] Replayed NSFormalization.Source.FractionalRealization
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
Build completed successfully (10629 jobs).
```

`cd verification && LEAN_NUM_THREADS=6 lake env lean Bindings/CompletedClosure.lean` — exit 0, **0 bytes output**.

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R46/axioms_closure.lean` — exit 0; full output:

```text
'BlowupDensity.Bindings.closure_pairable' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.closure_path_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.closure_path_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.closure_norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.closure_norm_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.closure_homogeneousConvergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.strongTrajectoryClosure_of_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.closure_relativeHomogeneous' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.completedHomogeneousDensity_of_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Standalone `make check` — captured status and exact head/tail:

```text
COMMAND: make check
EXIT: 0 
LINES: 33680
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
[middle omitted]
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
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

Standalone `make test` — exit 0, 364 output lines; first line and final four lines (middle omitted):

```text
lake -d verification test
[middle omitted]
ℹ [10697/10698] Replayed Tests.TameProduct
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
ℹ [10698/10698] Replayed Tests.MainThresholds
info: Tests/MainThresholds.lean:15:0: Contract BlowupDensity.Tests.checkedMainThresholds: checked; standard logical axioms only
```

Required gates, including mutation suite — captured status and exact head/tail:

```text
COMMAND: scripts/gates.sh Bindings.CompletedClosure
EXIT: 0
LINES: 34024
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
[middle omitted]
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

Explicit base-ref check — captured status and exact head/tail:

```text
COMMAND: python3 experiments/check_contracts.py --base-ref origin/erenup/integration
EXIT: 0
LINES: 33648
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
      "NavierStokes.ActualCarrierGeometry",
      "NavierStokes.ActualCarrierTransport",
      "NavierStokes.ActualCarrierTransportBase",
[middle omitted]
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

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R46/probes/rev259_lifespan_mutation.lean` — expected exit 1; full output:

```text
../research/R46/probes/rev259_lifespan_mutation.lean:26:2: error: Type mismatch
  strongTrajectoryClosure_of_realization hreal 0 A04.zero_mem_initialClassR 1
    (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
      (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl false))
    1
    (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
      (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl false))
    0 A04.memForceR_zero 1
    (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
      (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl false))
    (maximalPartial_ofA02
      (A04.zeroSol 1 (1 + 1)
        (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
          (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl false))
        (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
          (Mathlib.Meta.NormNum.isNat_add (Eq.refl HAdd.hAdd) (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
            (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl 2))
          (Eq.refl false))))
has type
  ∃ P A,
    A.a = 0 ∧
      A.scaling.correction.T = 1 ∧
        A.scaling.correction.g = 0 ∧
          A.scaling.correction.v = (maximalPartial_ofA02 (A04.zeroSol 1 (1 + 1) ⋯ ⋯)).velocity ∧
            A.scaling.correction.π = (maximalPartial_ofA02 (A04.zeroSol 1 (1 + 1) ⋯ ⋯)).pressure ∧
              (∀ ε ∈ Ioc 0 A.ε₀,
                  MemForceR (A.force ε) ∧
                    maximalLifespanR 1 0 (A.force ε) = ENNReal.ofReal 1 ∧
                      ∃ U, U.velocity = A.velocity ε ∧ U.pressure = A.pressure ε) ∧
                Tendsto
                    (fun ε =>
                      energyENorm 1 fun z =>
                        A.velocity ε z - (maximalPartial_ofA02 (A04.zeroSol 1 (1 + 1) ⋯ ⋯)).velocity z)
                    (𝓝[>] 0) (𝓝 0) ∧
                  Tendsto
                    (fun ε =>
                      ((forceSobolevENorm 1 0 fun z => A.force ε z - 0 z) +
                          forceSobolevENorm 2 (-1) fun z => A.force ε z - 0 z) +
                        forceHomogeneousENorm 2 (-1) fun z => A.force ε z - 0 z)
                    (𝓝[>] 0) (𝓝 0)
but is expected to have type
  ∃ P A,
    A.a = 0 ∧
      A.scaling.correction.T = 1 ∧
        A.scaling.correction.g = 0 ∧
          A.scaling.correction.v = 0 ∧
            A.scaling.correction.π = 0 ∧
              (∀ ε ∈ Ioc 0 A.ε₀,
                  MemForceR (A.force ε) ∧
                    maximalLifespanR 1 0 (A.force ε) = ENNReal.ofReal 2 ∧
                      ∃ U, U.velocity = A.velocity ε ∧ U.pressure = A.pressure ε) ∧
                Tendsto (fun ε => energyENorm 1 fun z => A.velocity ε z - 0) (𝓝[>] 0) (𝓝 0) ∧
                  Tendsto
                    (fun ε =>
                      ((forceSobolevENorm 1 0 fun z => A.force ε z - 0) +
                          forceSobolevENorm 2 (-1) fun z => A.force ε z - 0) +
                        forceHomogeneousENorm 2 (-1) fun z => A.force ε z - 0)
                    (𝓝[>] 0) (𝓝 0)
```

The architecture check reports pre-existing copied-source admissions and a source-hash mismatch; it nevertheless exits 0. These are not additions by this lane, and the lane's direct nine-declaration kernel axiom audit contains no admission axiom.

Only this new review and the permitted rev259 probe were written. No source, record, index, branch, or commit was changed.

Verdict: ACCEPT. Required fixes: none.

