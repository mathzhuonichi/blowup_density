ACCEPT

## 1. What the lane claims

Reviewed HEAD `62d4ac2838b1e050f98b231f40735350d91a9fcb`, lane 227-R44-endpoint. The worker claims the S2–S6 assembly conditional only on S1, not an unconditional Proposition 4.4 or a registered API (`research/R44/REPORT_227.md:5`, `:49`).

The paper was opened with `sed -n '136,175p' paper/sections/04-whole-space.tex`: its statement at :137–143 uses zero datum, the global inhomogeneous negative-half L² force norm, a universal radius c ν^(3/2) exp(-CνS), and strict lifespan beyond S. The implementation matches these choices. Spec fields were read at `research/R44/Spec.lean:183`, `:224`, `:237`, `:266`, and `:300`; the brief's :169–230 range ends before the actual conclusion fields, so these later lines were also checked.

## 2. What is in Lean

All paths abbreviated as Endpoint below mean `formalization/NSFormalization/Section4/R44/Endpoint.lean`.

- The norm abbreviation is at Endpoint:18; constants and positivity are at :22–41; strict radius arithmetic is at :43. They are universal, fixed before ν,S,f, and the exponent is real 3/2. These substantiate the explicit constants in the report.
- The sole analytic input is `RCritical2Differential` at Endpoint:57–66. Its differential inequality matches the S1 display in `research/R44/R44_SPLIT.md:61` and the paper :161–163, with one derivative function and local interval integrability. The unused proof binder `_hf` is explicit and honest: it indexes the interface but contributes no hidden condition. The structure contains neither a conclusion nor an unrelated regularity assumption.
- G3 is proved at Endpoint:69, :83, :97: continuity, exact datum-path infimum identification, and prefix-square control. The force path is obtained from MemForceR, not assumed separately.
- S2 is Endpoint:132–182, with the stronger bound Y ≤ theta*ν/2 on Icc 0 b, b<T and b≤S. It invokes the actual scalar theorem `R44/Pieces.lean:153` and radius lemma `:76`. The projIcc extension affects only a scalar auxiliary function and its derivative is transferred by eventual equality inside Ioo; it does not impose extra PDE regularity.
- S3 is Endpoint:185 and :198, using the homogeneous-to-inhomogeneous comparison and `R43/Pieces.lean:112`'s ENNReal absorption gate.
- Maximal transfer and the claimed explicit H² budget are Endpoint:220 and :234–249. The reused `R43/MaximalEndpoint.lean:15–36` supplies the open-terminal integral by shorter classical windows; it does not evaluate a singular terminal velocity. Endpoint:252 converts the power spelling using `R43/Pieces.lean:62`.
- The endpoint theorem is exactly Endpoint:271–296, including positivity, MemForceR, the sole differential provider, and the strict smallness premise. The unconditional A02/A04 statements were opened at `A02/MaximalWiring.lean:14` and `A04/ShiftedExtension.lean:247`. The contradiction uses a positive finite maximal lifespan L, constructs SolvesBelow, and obtains L<L.
- The requested explicitly conditional instantiation skeleton is Endpoint:300–308. The Data-vocabulary conformance theorems are `research/R44/axioms_endpoint.lean:91` and `:106`. Their concluding binders match Spec.main and Spec.nonDensityBallZero, using the lifespan bridge rather than silently identifying two solution structures. Data's actual norm, lifespan and breakdown definitions were read at `verification/Contracts/V1/Data.lean:225`, `:235`, `:657`, `:686`.
- Non-vacuity is already substantive enough for this brief: Endpoint:311 constructs E'=0 for A04.zeroSol; `axioms_endpoint.lean:39` proves strict smallness for zero force; :54 proves S1 for every zero-force classical solution by uniqueness; :83 invokes the endpoint without an assumed provider. These passed. Taking ν=S=1 gives a positive horizon, not an empty interval.
- No top-toReal loophole: force finiteness is proved at Endpoint:104–105 and :128, :153–157; slice finiteness at :210–213. Maximal-lifespan finiteness is established before toReal at :280–285. The canonical Y/Z/B are the physical datum norms (`R44/JWeight.lean:121–129`).
- Hygiene: the authored module and axioms file have no forbidden proof token or heartbeat override. No existing Lean module changed. The only existing files changed by the worker are the two expressly requested Markdown records. The changed-module checker includes this new module in the build selection.

The negative probe `research/R44/probes/rev227_negative.lean:137` copies the module and changes only the S2 conclusion to Y ≤ -(theta*ν/2). The original proof fails at :182 with the expected sign mismatch (and produces a downstream mismatch at :207). No argument was dropped. This mutation is actually false at t=0 for the zero solution with ν>0.

## 3. Gaps

No blocking finding or required fix.

The remaining S1c/S1d derivation and local derivative-integrability assembly are accurately disclosed (`research/R44/REPORT_227.md:49`; Endpoint:57). Whole-tree searches were run before accepting this gap:

```sh
grep -rnE 'RCritical2Differential|Rcritical2|nonlinear.*(bound|le)|trilinear.*(bound|le)|S1c|S1d' formalization/NSFormalization/Section4
grep -rnE 'advectionJPairing|RCritical2Differential|critical2.*[Dd]ifferential|J.*[Aa]bsorb' formalization/NSFormalization/Section4
```

They locate the new conditional interface, scalar Pieces, and the existing energy identity, but no provider of the R44 differential input. The current R44 directory contains Pieces, JWeight, EnergyIdentity, and Endpoint only. `R44/EnergyIdentity.lean:286` supplies the unabsorbed identity, not the missing nonlinear inequality. Other nonlinear results found in A04/C01/R43 do not supply this Ju estimate. In particular, a reference to lane 220's advectionJPairing in `EnergyIdentity.lean:285` is a comment, not its presence in this checkout. The fixed constants' compatibility with the eventual nonzero S1 proof remains that supplier's obligation; this lane makes no claim to have discharged it.

The historical absence tables in COMPARISON and R44_SPLIT are explicitly marked historical; their current update describes the present closure. No full contract registration is claimed. The build's dependency warnings and make check's broad source-manifest diagnostics are pre-existing scope diagnostics; the new module is silent and its transitive axiom audit is clean.

## 4. Commands and results

Lean environment: sourced `scripts/lean-env.sh`; every lake command ran from `verification/` with `LEAN_NUM_THREADS=6`, one at a time. Existing packages symlink was verified, so no installation/bootstrap mutation was needed. No git state changes were made.

Build, exit 0 (exact first/last 40 lines below; omitted middle consists of dependency replay diagnostics):

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R44.Endpoint
⚠ [8781/9300] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9869/10548] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9870/10548] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10265/10548] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:30: Variable name `hB` is not explicitly referenced.
[... middle dependency replay omitted ...]
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10515/10548] Replayed NSFormalization.Source.RieszL2Fourier
warning: NSFormalization/Source/RieszL2Fourier.lean:31:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [10516/10548] Replayed NSFormalization.Source.FractionalRealization
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
Build completed successfully (10548 jobs).

```

Direct check, exit 0, exactly zero output:

```sh
LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/R44/Endpoint.lean
```

Axioms/conformance check, exit 0; exact complete output:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/R44/axioms_endpoint.lean
'NSFormalization.Section4.R44.forceSobolevENormL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.theta' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.C₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.C₃' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.theta_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.C₂_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.C₃_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radiusCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radiusRate' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radius' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radiusCoefficient_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radiusRate_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radiusCoefficient_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.RCritical2Differential' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.forceB_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.force_norm_eq_path' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.forceB_prefix_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.Y_bound_of_differential' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.velocity_dot_le_sobolev' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.absorption_of_differential' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.maximal_absorption_of_differential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.maximal_h2TimeIntegral_of_differential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.maximal_squaredHTwoIntegral_of_differential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.rcritical2_endpoint_of_differential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.rcritical2_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.zeroSol_differential' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndpointConformance.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'EndpointConformance.nonDensityBallZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'zero_force_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'zero_force_differential' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Mutation, exit 1 as expected; exact complete output:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/R44/probes/rev227_negative.lean
../research/R44/probes/rev227_negative.lean:182:2: error: Type mismatch: After simplification, term
  hbound t ht
 has type
  Y (C01.slice w.velocity t) ≤ theta * ν / 2
but is expected to have type
  Y (C01.slice w.velocity t) ≤ -(theta * ν / 2)
../research/R44/probes/rev227_negative.lean:207:31: error: Type mismatch
  this
has type
  theta * ν / 2 ≤ theta * ν
but is expected to have type
  -(theta * ν / 2) ≤ theta * ν
```

`make check`: exit 0. Exact first/last 40 lines of captured stdout followed by stderr (large closure JSON omitted):

```text
exit: 0
FIRST 40 LINES:
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 542,
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
LAST 40 LINES:
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
Ran 13 tests in 0.040s

OK
```

Other checks:

```text
$ git diff --name-status origin/erenup/integration...HEAD
A	formalization/NSFormalization/Section4/R44/Endpoint.lean
A	research/R44/ATTEMPTS_ENDPOINT.md
M	research/R44/COMPARISON.md
M	research/R44/R44_SPLIT.md
A	research/R44/REPORT_227.md
A	research/R44/axioms_endpoint.lean

$ python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run
Changed Lean modules: NSFormalization.Section4.R44.Endpoint
```

`git diff --check`: exit 0, zero output. Forbidden-token/maxHeartbeats scan of the two authored Lean files: zero matches. `git diff --name-only origin/erenup/integration...HEAD -- verification`: zero output. Consequently the user-required conditional `scripts/gates.sh` and `check_contracts.py --base-ref origin/erenup/integration` gates are not applicable. The worker's optional lake test and contract-mutation runs are not represented here as reviewer reruns.

Reviewer additions are only this report and the permitted negative probe. Fixes: none.

