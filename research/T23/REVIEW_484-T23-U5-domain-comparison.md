ACCEPT

## 1. What the lane claims

The worker claims one exact U5 field theorem, three supporting comparison/slice
lemmas, and five definition bridges (`research/T23/REPORT_484.md:5-39`).  The
main claim is a two-sided comparison of the time-integrated restriction norm of
the actual difference `force ε - g` with the norm of its literal zero extension,
with one positive `C` chosen after `s` and before `ε`
(`research/T23/REPORT_484.md:10-22`).

This is the mathematics requested by the manuscript.  The paper defines the
restriction quotient norm and its order-zero interpretation at
`paper/sections/03-torus.tex:601-607`, states the fixed-compact two-sided
zero-extension estimate at `paper/sections/03-torus.tex:608-625`, and explicitly
requires the constant to be independent of the shrinking scale and the compact
support to remain fixed through time at `paper/sections/03-torus.tex:626-630`.
The boundary corollary asks for the corresponding time-integrated force norm and
comparison at `paper/sections/03-torus.tex:647-651`, while its proof says that
the difference supports, including after `T`, lie in one fixed compact interior
ball and that the comparison is applied after time integration
(`paper/sections/03-torus.tex:661-664`).

The split assigns precisely this unit to U5 and approves the same route:
fixed `K = closure B`, `C` before time and `ε`, `ENNReal` integration without
finiteness, and explicit U3/U4 inputs (`research/T23/T23_SPLIT.md:111-126`).
Per the lead note, those upstream inputs are required threaded hypotheses, not
gaps or named placeholders.

## 2. What is in Lean

### Exact statements and proof content

The production theorem exists at
`formalization/NSFormalization/Section3/T23/DomainComparison.lean:67-114`.
Its conclusion at lines 78-83 is token-for-token the canonical
`BoundaryInsertionAPI.domain_zeroExt_comparison` field at
`formalization/NSFormalization/Section3/T23/Boundary.lean:428-434` and the
historical target at `research/T23/Spec.lean:983-989`.  The exact-type closure
probe applies it directly at
`research/T23/probes/T23-U5-domain-comparison_closes.lean:201-220`.

The inputs are honest and isolated:

- `hforce` at `DomainComparison.lean:73-74` is exactly U3's
  `forceDifference_mem` field at `Boundary.lean:222-223`.
- `hsupport` at `DomainComparison.lean:75-77` is exactly U4's all-real-time
  `forceDifference_spatialSupport` field at `Boundary.lean:375-377`.
- `hΩ`, `hR`, and `hball` at `DomainComparison.lean:71-72` are the open-domain,
  positive chart-radius, and prescribed interior-ball facts supplied by
  `Boundary.lean:146`, `Placement.lean:52-56`, and `Boundary.lean:165-166`.

There is no conclusion-shaped `Prop`, arbitrary named input, or unused binder.
Every premise is consumed in the proof: compactness and the T22 specialization
are at `DomainComparison.lean:85-90`; U3 slice regularity and U4 support are used
at lines 93-97; both inequalities are integrated at lines 98-114.  The constant
is obtained at lines 88-91 before `ε` is introduced at line 92.  The upper
integral is factored by `lintegral_const_mul'` with the finite constant
`ENNReal.ofReal C` at lines 102-114, so no finite-norm assumption or
`⊤.toReal = 0` device occurs.

The support bridge is the literal zero-extension statement needed by T22
(`DomainComparison.lean:23-35`).  Positive-time force membership yields a smooth
spatial slice from the actual `forceClassOmega` definition
(`DomainSolution.lean:74-86`) via the slab-slice lemma
(`DomainComparison.lean:37-44`).  The order-zero theorem then invokes the actual
T22 field on the difference slice (`DomainComparison.lean:46-61`), matching the
canonical implementation at `Section3/T22/OrderZero.lean:217-221`.

The T22 API used is the canonical three-field record at
`formalization/NSFormalization/Section3/T22/Domain.lean:58-77`.  Its comparison
field matches the registered contract at
`verification/Contracts/V1/BoundedDomainNorm.lean:109-116`, and its proved
implementation has the same statement at
`formalization/NSFormalization/Section3/T22/ZeroExtensionComparison.lean:26-35`.
The historical and registered fieldwise adapters and their round trips are
checked at `T23-U5-domain-comparison_closes.lean:83-149`.

All five norm definitions in the canonical interface
(`Boundary.lean:56-91`) match the historical definitions
(`research/T23/Spec.lean:612-647`).  The five production `rfl` bridges are at
`formalization/NSFormalization/Section3/T23/DomainNorms.lean:22-52`, and their
exact statement probes are at
`T23-U5-domain-comparison_closes.lean:153-182`.

### Non-vacuity and negative mutation

Although the standalone comparison theorem is harmlessly more general in
`ε₀`, any enclosing `BoundaryInsertionAPI` has `0 < ε₀`
(`Boundary.lean:169-173`).  The reviewer probe explicitly witnesses
`ε₀ ∈ Ioc 0 ε₀` from that fact
(`research/T23/probes/rev484_domain_comparison.lean:23-24`).  It also constructs
a nonzero smooth force with compact temporal support inside `(0,∞)`
(`rev484_domain_comparison.lean:35-72`) and applies the main theorem on the open
unit ball, fixed closed half-ball, and nonempty scale interval `(0,1]`
(`rev484_domain_comparison.lean:74-111`).  Thus the hypotheses are jointly
inhabited by a nonzero example; neither an empty interval nor a zero field is
being used to certify the result.

The substantive mutation reverses the first main inequality while leaving all
hypotheses and the upper inequality unchanged
(`rev484_domain_comparison.lean:117-135`).  A direct proof attempt failed as
expected:

```text
../research/T23/probes/rev484_domain_comparison.lean:43:2: error: Type mismatch
  domain_zeroExt_comparison norms hΩ hR hball hforce hsupport
has type
  ∀ (s : ℝ),
    ∃ C,
      0 < C ∧
        ∀ ε ∈ Ioc 0 ε₀,
          ((domainForceSobolevENorm Ω s fun z => force ε z - g z) ≤
              zeroExtForceSobolevENorm Ω s fun z => force ε z - g z) ∧
            (zeroExtForceSobolevENorm Ω s fun z => force ε z - g z) ≤
              ENNReal.ofReal C * domainForceSobolevENorm Ω s fun z => force ε z - g z
but is expected to have type
  ∀ (s : ℝ),
    ∃ C,
      0 < C ∧
        ∀ ε ∈ Ioc 0 ε₀,
          ((zeroExtForceSobolevENorm Ω s fun z => force ε z - g z) ≤
              domainForceSobolevENorm Ω s fun z => force ε z - g z) ∧
            (zeroExtForceSobolevENorm Ω s fun z => force ε z - g z) ≤
              ENNReal.ofReal C * domainForceSobolevENorm Ω s fun z => force ε z - g z
```

The retained probe uses `fail_if_success` for this exact mutation and itself
checks with zero output (`rev484_domain_comparison.lean:126-135`).

## 3. Gaps and hygiene

There is no U5 mathematical gap.  The worker's only assembly note is that U9
must supply the already assigned U3 and U4 fields
(`research/T23/REPORT_484.md:56-61`); those formulas are exactly the upstream
field types cited above and are the lead-approved parallel-lane pattern.  They
are not conclusions of U5 and do not restate the desired comparison.  The
worker makes no "not in the tree" claim for a missing U5 lemma, so the required
whole-`Section4` missing-lemma grep condition has no instance to check.

The delivered U5 production files, closure probe, axiom file, and reviewer
probe contain no `sorry`, `admit`, `axiom`, or `native_decide`, no
`maxHeartbeats`, and no import of `Paper1/BoundaryCorollary`.  The same scan over
all Lean paths in the branch diff found only three prose mentions of `sorry` in
the inherited lane-480 research probe (`boundary_api_on_canonical.lean:19,94,542`),
not Lean tokens.  No heartbeat override occurs anywhere in that diff.

`git diff --name-status origin/erenup/integration-section3...HEAD -- formalization`
reports only additions, including the two U5 modules; no existing Lean module
is modified.  The command warns that the branch has multiple merge bases and
uses `b9eab7ff...`, but its formalization entries are all `A`.  This agrees with
the brief's stated lane-480 parent.  `git diff --check` is clean.  No file under
`verification/` is changed.  The pre-existing untracked
`collaboration/briefs/484-T23-U5-domain-comparison.md` was present before review
and was left untouched; this review adds only the permitted reviewer probe and
this required report.

All nine production declarations listed at
`research/T23/axioms_T23-U5-domain-comparison.lean:3-11` have exactly
`[propext, Classical.choice, Quot.sound]`.

## 4. Commands and results

All Lean/Lake commands sourced `scripts/lean-env.sh`; all Lake invocations were
run from `verification/` with `LEAN_NUM_THREADS=6`.

### Builds

The dependency closure and both requested targets exited 0.  Lake replayed
pre-existing dependency linter warnings; neither new U5 module emitted a
warning.  Exact first/last excerpts:

```text
$ lake build NSFormalization.Section3.T23.Boundary
⚠ [8778/8829] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
...
Hint: Omit it from the simp argument list.
  [apply] simp only [smul_smul, h₂, smul_add, smul_sub]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (10087 jobs).
```

```text
$ lake build NSFormalization.Section3.T23.DomainNorms
⚠ [8778/9194] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
...
Hint: Omit it from the simp argument list.
  [apply] simp only [smul_smul, h₂, smul_add, smul_sub]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (10088 jobs).
```

```text
$ lake build NSFormalization.Section3.T23.DomainComparison
⚠ [8778/9077] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
...
Hint: Omit it from the simp argument list.
  [apply] simp only [smul_smul, h₂, smul_add, smul_sub]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (10097 jobs).
```

### Direct Lean checks and axioms

Each command below exited 0 with exactly zero output:

```text
lake env lean ../formalization/NSFormalization/Section3/T23/DomainNorms.lean
lake env lean ../formalization/NSFormalization/Section3/T23/DomainComparison.lean
lake env lean ../research/T23/probes/T23-U5-domain-comparison_closes.lean
lake env lean ../research/T23/probes/rev484_domain_comparison.lean
```

The axiom audit exited 0 with exact output:

```text
'NSFormalization.Section3.T23.domainEnergyEssSup_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainEnergyGradient_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainEnergyENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainForceSobolevENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.zeroExtForceSobolevENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.tsupport_zeroExtension_subset_of_pointwise_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.contDiffOn_slice_of_memForceOmega' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.domainForceDifference_orderZero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.domain_zeroExt_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Repository gates

`make check` exited 0.  Because its raw output is large, the exact first and last
portions are quoted:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 733,
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
...
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

The historical copied-umbrella admission and `source_hashes_match: false` are
reported repository state, not a failure of `make check`, and that module is not
in the U5 import chain.

`BASE_REF=origin/erenup/integration-section3 scripts/gates.sh` exited 0.  Its
exact final gate output was:

```text
info: Tests/BoundedDomainNorm.lean:28:0: Contract BlowupDensity.Tests.checkedBoundedDomainNorm: checked; standard logical axioms only
info: Tests/BoundedDomainNorm.lean:33:0: Contract BlowupDensity.Tests.checkedBoundedDomainNormStatement: checked; standard logical axioms only
info: Tests/PeriodicInsertion.lean:15:0: Contract BlowupDensity.Tests.checkedPeriodicInsertion: checked; standard logical axioms only
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
info: Tests/TorusNonDensity.lean:24:0: Contract BlowupDensity.Tests.checkedTorusNonDensity: checked; standard logical axioms only
info: Tests/TorusMain.lean:21:0: Contract BlowupDensity.Tests.checkedTorusMain: checked; standard logical axioms only
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

No `verification/` path was touched, but the explicit contract check requested
for that case was also run and exited 0:

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
{
  "registered_contracts": 54,
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
...
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.MultipleRegions"
    ]
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

The targeted forbidden-token, heartbeat, and unsafe-import scan on the U5 files
had zero output.  `git diff --check` also had zero output.

Fixes required: none.
