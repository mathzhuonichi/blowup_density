ACCEPT-WITH-NOTES

## 1. What the lane claims

`REPORT_423.md:5-19` claims that the three already-closed fields are assembled
as `boundedDomainNorm`, that `T04.bounded_domain_norm` is registered, and that
the contract vocabulary is copied from the reconciled specification.  This is
the requested U-REG scope.  The paper passage actually says that the domain
norm is the restriction quotient (`paper/sections/03-torus.tex:600-605`), that
order zero is the restricted `L²` norm (`paper/sections/03-torus.tex:606-607`),
and gives the compact interior-support zero-extension comparison
(`paper/sections/03-torus.tex:608-625`), including the fixed cutoff and
constant uniformity (`paper/sections/03-torus.tex:615-629`).

The three API fields are exactly the accepted Spec fields: `orderZero` at
`research/T22/Spec.lean:125-128`, `cutoffMultiplier` at
`research/T22/Spec.lean:140-144`, and `zeroExtensionComparison` at
`research/T22/Spec.lean:160-167`.  Their canonical theorem statements
are present at `formalization/NSFormalization/Section3/T22/OrderZero.lean:219-221`,
`formalization/NSFormalization/Section3/T22/CutoffMultiplierField.lean:329-333`,
and `formalization/NSFormalization/Section3/T22/ZeroExtensionComparison.lean:28-35`.
No `⊤.toReal`, empty interval, or weakened conclusion is introduced.  The
`ContDiffOn` hypothesis in the zero-extension field is from the accepted Spec;
the proof happens not to use it
(`formalization/NSFormalization/Section3/T22/ZeroExtensionComparison.lean:40-50`), but it
does not make the field vacuous and is not silently added.

The non-vacuity claim in `REPORT_423.md:14-16` is genuine: the construction is
`Ω = ball 0 1`, `K = closedBall 0 (1/2)`, and a radius-`1/4`/`1/2`
`ContDiffBump` times `coordinateVector 0` at
`formalization/NSFormalization/Section3/T22/Assembly.lean:36-45`; openness,
compactness, containment, smoothness, support, and nonzero value are proved at
`formalization/NSFormalization/Section3/T22/Assembly.lean:46-88`, and the
existential witness is assembled at
`formalization/NSFormalization/Section3/T22/Assembly.lean:91-98`.

## 2. What is in Lean

The canonical assembly is exactly the requested record literal at
`formalization/NSFormalization/Section3/T22/Assembly.lean:24-32`.  The seven
bounded-domain definitions in the contract (`DomainTest`, `DomainFunctional`,
`restrictDatum`, `domainSobolevENorm`, `restrictField`, `zeroExtension`, and
`IsCutoffDatum`) are at
`verification/Contracts/V1/BoundedDomainNorm.lean:27-58` and match the
corresponding Spec declarations at `research/T22/Spec.lean:48-104` (same
binders, constants, integrals, infimum, and transpose graph; a normalized
token comparison ignoring comments/whitespace was identical).  The three
record fields and quantifier order are at
`verification/Contracts/V1/BoundedDomainNorm.lean:63-116` and match
`research/T22/Spec.lean:114-167`.

Every restated definition has a whole-definition `rfl` bridge at
`verification/Bindings/BoundedDomainNorm.lean:23-49`.  The independently
declared Prop structures are transported fieldwise, with `rfl` round trips and
statement equivalence at
`verification/Bindings/BoundedDomainNorm.lean:51-78`; the canonical witness and
statement proof are at `verification/Bindings/BoundedDomainNorm.lean:80-90`.
The test exposes both checked declarations and the required
axiom commands at `verification/Tests/BoundedDomainNorm.lean:24-33`, repeats the
Spec-shaped order-zero field at `verification/Tests/BoundedDomainNorm.lean:37-42`,
and applies the full comparison to the concrete nonzero bump at
`verification/Tests/BoundedDomainNorm.lean:46-74`.

The registry entry is additive and honest at
`verification/contracts.json:467-475`: parent `T04`, version `1`, the three
modules, the checked declaration, the closed multiplier constant, and the
`Mathlib.Geometry.Manifold.PartitionOfUnity` closure are all named.  The lane
commit modifies no pre-existing `Contracts/V*` or `Tests/*` file: its parent
diff has only the two new files in those directories.  Searches over the lane
implementation Lean additions found no declaration-level `sorry`, `admit`,
`axiom`, `native_decide`, placeholder `True`, or `maxHeartbeats` (the separate
audit file intentionally contains `#print axioms` commands).

## 3. Gaps and notes

1. **Warning-clean gate note (minor).**  The required `lake env lean` check is
   not literally silent.  The exact lane-owned diagnostic is:

   ```text
   ../formalization/NSFormalization/Section3/T22/Assembly.lean:24:0: warning: Definition `boundedDomainNorm` is a proposition; use `theorem` instead of `def`
   Note: This linter can be disabled with `set_option linter.defProp false`
   ```

   `lake build Tests.BoundedDomainNorm` additionally reports the same linter
   warning for `toCanonical`, `ofCanonical`, and the contract witness at
   `verification/Bindings/BoundedDomainNorm.lean:54-62` and
   `verification/Bindings/BoundedDomainNorm.lean:80-86`.  These
   `def`s are required by the deliverable and are not proof errors, but the
   report's “all required gates pass” at `REPORT_423.md:32-40` should either
   record the warnings or suppress them with a local
   `set_option linter.defProp false in` on each required Prop-valued `def`.

2. **Axiom audit exception (minor/documentation).**  The actual audit contains
   two expected axiom-free type declarations:
   `BoundedDomainNormAPI` and `boundedDomainNormStatement`, as recorded in
   `REPORT_423.md:23-27` and `REPORT_423.md:107-108`.  All other 37 printed declarations
   have exactly `[propext, Classical.choice, Quot.sound]`.  A structure type
   and a `Nonempty` type alias cannot acquire a meaningful dependency on those
   axioms without an artificial dependency, so the worker was right not to
   manufacture one.  The report should phrase this as an explicit structural
   exception rather than saying the literal “every declaration” requirement is
   met.

3. The report declares no missing Section-4 lemma.  As a check on its
   exclusions, `grep -rn` over the whole
   `formalization/NSFormalization/Section4` tree found no
   `BoundedDomainNormAPI`, `boundedDomainNormStatement`, `domainSobolevENorm`,
   `restrictDatum`, `restrictField`, `zeroExtension`, or `IsCutoffDatum`; the
   exclusions at `REPORT_423.md:27-28` are therefore not hiding an existing
   tree theorem.

## 4. Commands and results

All Lean commands below used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and
were run from `verification/` (except the root `make`/gate commands).

The requested canonical build exited 0.  Its final, lane-owned output was:

```text
⚠ [9940/9940] Replayed NSFormalization.Section3.T22.Assembly
warning: NSFormalization/Section3/T22/Assembly.lean:24:0: Definition `boundedDomainNorm` is a proposition; use `theorem` instead of `def`
Note: This linter can be disabled with `set_option linter.defProp false`
Build completed successfully (9940 jobs).
```

`lake env lean ../formalization/NSFormalization/Section3/T22/Assembly.lean`
exited 0 with the warning quoted in note 1.  `lake build Tests.BoundedDomainNorm`
also exited 0 and ended with:

```text
⚠ [9945/9947] Replayed NSFormalization.Section3.T22.Assembly
warning: NSFormalization/Section3/T22/Assembly.lean:24:0: Definition `boundedDomainNorm` is a proposition; use `theorem` instead of `def`
⚠ [9946/9947] Replayed Bindings.BoundedDomainNorm
warning: Bindings/BoundedDomainNorm.lean:54:0: Definition `toCanonical` is a proposition; use `theorem` instead of `def`
warning: Bindings/BoundedDomainNorm.lean:59:0: Definition `ofCanonical` is a proposition; use `theorem` instead of `def`
warning: Bindings/BoundedDomainNorm.lean:80:0: Definition `boundedDomainNorm` is a proposition; use `theorem` instead of `def`
ℹ [9947/9947] Replayed Tests.BoundedDomainNorm
info: Tests/BoundedDomainNorm.lean:28:0: Contract BlowupDensity.Tests.checkedBoundedDomainNorm: checked; standard logical axioms only
info: Tests/BoundedDomainNorm.lean:33:0: Contract BlowupDensity.Tests.checkedBoundedDomainNormStatement: checked; standard logical axioms only
Build completed successfully (9947 jobs).
```

`lake env lean ../research/T22/axioms_ureg.lean` exited 0.  Its exact output
was:

```text
'NSFormalization.Section3.T22.boundedDomainNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.boundedDomainNormStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.boundedDomainNormStatement_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T22.nonvacuityΩ' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityK' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityBump' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityField' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityΩ_open' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityK_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityK_subset_Ω' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityField_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityField_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.nonvacuityField_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.boundedDomainNorm_nonvacuity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.BoundedDomainNorm.DomainTest' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.BoundedDomainNorm.DomainFunctional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Contracts.V1.BoundedDomainNorm.restrictDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.BoundedDomainNorm.domainSobolevENorm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Contracts.V1.BoundedDomainNorm.restrictField' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.BoundedDomainNorm.zeroExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.BoundedDomainNorm.IsCutoffDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.BoundedDomainNorm.BoundedDomainNormAPI' does not depend on any axioms
'BlowupDensity.Contracts.V1.BoundedDomainNorm.boundedDomainNormStatement' does not depend on any axioms
'BlowupDensity.Bindings.BoundedDomainNorm.domainTest_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.domainFunctional_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.restrictDatum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.domainSobolevENorm_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.restrictField_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.zeroExtension_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.isCutoffDatum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.toCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.ofCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.ofCanonical_toCanonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.toCanonical_ofCanonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.boundedDomainNormStatement_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.boundedDomainNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.BoundedDomainNorm.boundedDomainNormStatement_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Tests.checkedBoundedDomainNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedBoundedDomainNormStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The root `make check` exited 0; `make check` from `verification/` correctly
returns `make: *** No rule to make target 'check'.  Stop.` because the Makefile
is at the worktree root.  The final root checks were:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The full architecture check also reports the repository's pre-existing copied
source token at `formalization/NSFormalization/Paper1/BoundaryCorollary.lean:90`
and `source_hashes_match: false`; it exits 0 and neither path is in this lane's
implementation diff.

The complete requested gate script was run as
`BASE_REF=origin/erenup/integration-section3 scripts/gates.sh`; it exited 0:

```text
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

The standalone `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
exited 0 and reported `"registered_contracts": 43` and
`"base_compatibility_checked": true`.  The registry diff is 11 added lines:

```text
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

The required hygiene check `git diff --check origin/erenup/integration-section3...HEAD`
exited 0 (Git warns of multiple merge bases and selects `24031a9f...`).  The
triple-dot path list includes unrelated already-integrated T20/T24 files due
that moving-base warning; `git diff --name-only HEAD^ HEAD` shows only this
lane's additions, and no existing contract/test file is modified.

For the substantive negative check, reviewer-only
`research/T22/probes/rev423_negative.lean:15-21` changes the multiplier
conclusion to `ENNReal.ofReal (C / 2)`.  It exits 1 with the expected error:

```text
../research/T22/probes/rev423_negative.lean:21:2: error: Type mismatch: After simplification, term
  boundedDomainNorm.cutoffMultiplier
 has type
  ∀ (s : ℝ) (χ : Space → ℝ),
    ContDiff ℝ ∞ χ →
      HasCompactSupport χ →
        ∃ C, 0 < C ∧ ∀ (A : RealVectorSobolev s), ∃ B, IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ
but is expected to have type
  ∀ (s : ℝ) (χ : Space → ℝ),
    ContDiff ℝ ∞ χ →
      HasCompactSupport χ →
        ∃ C, 0 < C ∧ ∀ (A : RealVectorSobolev s), ∃ B, IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal (C / 2) * ‖A‖ₑ
```

This changes a substantive constant and does not merely drop an argument.  The
positive bump instance is independently typechecked by
`Tests/BoundedDomainNorm.lean:46-74`.

Fixes (one line each):

- Suppress or explicitly record the four local `defProp` diagnostics at `formalization/NSFormalization/Section3/T22/Assembly.lean:24`, `verification/Bindings/BoundedDomainNorm.lean:54`, `verification/Bindings/BoundedDomainNorm.lean:59`, and `verification/Bindings/BoundedDomainNorm.lean:80` so the promised module typecheck is silent.
- Amend `REPORT_423.md:23-27` to state the two structural axiom-free declarations as an intentional exception to the three-axiom audit.
