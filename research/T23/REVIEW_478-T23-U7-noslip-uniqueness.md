ACCEPT-WITH-NOTES

## 1. What the lane claims

The operative deliverable is the continuation report
`research/T23/REPORT_478b.md:1-123`, not the earlier honest partial. It claims:

- box-domain velocity uniqueness with the exact U7 data/force/solution/time/point
  binders, changing only the domain premise to `IsBoxDomain Ω`
  (`REPORT_478b.md:5-9`);
- a genuine scalar boundary integration-by-parts proposition `IBP Ω`, proved for
  boxes by `ibp_box` (`REPORT_478b.md:11-14`);
- the difference-energy identity, convection bound, and Grönwall/continuity
  conclusion (`REPORT_478b.md:16-28`);
- the full U7 conclusion conditional only on `IBP Ω`
  (`REPORT_478b.md:30-34`); and
- one remaining analytic gap for regular-level domains, with no unrestricted
  `noSlip_uniqueness` declaration (`REPORT_478b.md:64-80`).

This is the mathematics requested by the continuation. The manuscript says that
classical no-slip uniqueness is the same difference-energy calculation as the
periodic local result, with boundary terms vanishing
(`paper/sections/03-torus.tex:632-644,653-665`). The reconciled target is
velocity-only on `Ico 0 (min T₁ T₂)`, not pressure equality
(`research/T23/RECONCILIATION.md:51-52`), and the exact Spec field is at
`research/T23/Spec.lean:1008-1020`. The periodic comparison theorem indeed has
the same quantifier order and conclusion but no domain binder
(`formalization/NSFormalization/Section3/T11/Uniqueness.lean:26-35`).

Two non-blocking findings require exact cleanup:

1. **Citation note.** Several copied Spec citations point to nearby but wrong
   manuscript lines. To retain the claimed byte synchronization, make the same
   one-line replacements in `DomainSolution.lean` and the matching Spec lines:
   - `DomainSolution.lean:16` / `Spec.lean:454`: `03-torus.tex:635-639` →
     `03-torus.tex:638-642`;
   - `DomainSolution.lean:120` / `Spec.lean:558`: replace
     `02-preliminaries.tex:28-29` and `03-torus.tex:641` by
     `01-introduction.tex:4-7` and `03-torus.tex:634-646`;
   - `DomainSolution.lean:124` / `Spec.lean:562`: `03-torus.tex:641` →
     `03-torus.tex:643`;
   - `DomainSolution.lean:128` / `Spec.lean:566`: `03-torus.tex:641` →
     `03-torus.tex:643`;
   - `DomainSolution.lean:133` / `Spec.lean:571`: `03-torus.tex:641` →
     `03-torus.tex:644`.
2. **Whitespace note.** Make `git diff --check
   origin/erenup/integration-section3...HEAD` silent: delete the extra EOF blank
   lines reported at `DifferenceEnergy.lean:389`, `DomainSolution.lean:271`,
   `NoSlipEnergy.lean:172`, and
   `research/T23/probes/box_integration_by_parts_closes.lean:17`; remove trailing
   spaces at `research/T23/ATTEMPTS_U7.md:425,433`.

Neither note changes a theorem statement or proof.

## 2. What is in Lean

### Statement fidelity and proof path

- The canonical domain vocabulary and `ClassicalSolutionOmega` occupy
  `formalization/NSFormalization/Section3/T23/DomainSolution.lean:16-140`.
  A literal diff against `research/T23/Spec.lean:454-578` exits 0 with no output.
  The record has genuine smoothness, positive horizon, initial value,
  divergence, momentum, no-slip, and pressure-gauge fields
  (`DomainSolution.lean:104-140`); there is no `⊤.toReal`, empty-interval trick,
  or conclusion-shaped input.
- `IBP` is a `def ... : Prop` whose body is precisely scalar boundary
  integration by parts for two `C¹` fields, with only the first field zero on
  `frontier Ω` (`DomainSolution.lean:211-221`). Its docstring explicitly calls
  it the sole missing domain-specific analytic input
  (`DomainSolution.lean:211-214`). `ibp_box` proves it by transporting the
  coordinate-box theorem (`DomainSolution.lean:223-269`), whose face-flux and
  product-rule proofs are at `BoxIntegration.lean:11-110`.
- The difference equation is derived from the two momentum equations at
  `DifferenceEnergy.lean:108-155`. Divergence and no-slip are separately
  derived at `DifferenceEnergy.lean:157-179`. The energy identity explicitly
  consumes both in the transport and pressure cancellations at
  `DifferenceEnergy.lean:193-269`, especially `:217-224`.
- The convection estimate is the claimed operator-norm bound
  (`DifferenceEnergy.lean:271-297`). `velocity_eq_of_ibp` obtains a derivative
  bound, proves `E' ≤ 2 C E`, invokes the genuine integrating-factor Grönwall
  theorem, and upgrades zero energy to pointwise equality
  (`DifferenceEnergy.lean:298-345`; supplier
  `vendor/NavierStokesAndEuler/NavierStokes/PeriodicUniqueness.lean:154-183`).
- `noSlip_uniqueness_of_ibp` has the exact U7 target plus only `IBP Ω`
  (`DifferenceEnergy.lean:347-358`). `noSlip_uniqueness_box` has the exact U7
  binders with `IsBoxDomain Ω` and no analytic premise
  (`DifferenceEnergy.lean:375-386`). The literal conformance probes restate
  these types at `research/T23/probes/noslip_uniqueness_closes.lean:8-16` and
  `research/T23/probes/noslip_box_closes.lean:8-18`.
- The initial-class and force-class premises are proof-redundant once two records
  with the same parameters are supplied (`DifferenceEnergy.lean:357,385` names
  them `_ha`, `_hf`), but they are the exact Spec binders rather than vacuity.
  The reviewer constructed actual zero initial data, zero force, and two zero
  solution records on the concrete box `(0,1)^3`, then applied the box theorem
  at an interior time and point
  (`research/T23/probes/rev478_nonvacuity.lean:10-65`). This compiled with exit
  0 and zero output.

### Negative check

`research/T23/probes/rev478_drop_no_slip.lean:14-27` defines the canonical
solution record with only the `no_slip` field removed. Lines `31-40` mutate the
main box theorem to use those weaker records. This is a field deletion, not an
argument omission. Reusing the reviewed theorem fails as expected:

```text
../research/T23/probes/rev478_drop_no_slip.lean:40:57: error: Application type mismatch: The argument
  u₁
has type
  SolutionWithoutNoSlip ν Ω a' f T₁
but is expected to have type
  ClassicalSolutionOmega ν Ω a' f T₁
in the application
  noSlip_uniqueness_box ν hν Ω hΩ a' ha f hf T₁ T₂ u₁
```

Command exit: 1. This agrees with the direct proof dependency on
`u.no_slip`/`v.no_slip` at `DifferenceEnergy.lean:217-224`.

### Hygiene

All six Lean modules are additions relative to the base; no pre-existing Lean
module was modified. `SPEC_ISSUES.md` and `T23_SPLIT.md` are the continuation's
requested record updates. No `verification/` path occurs in the base diff.
The only admission-keyword match in delivered Lean source is the explanatory
doc comment at `DomainSolution.lean:103`; there is no proof use of
`sorry`, `admit`, `axiom`, or `native_decide`, no `maxHeartbeats`, and no import
of `BoundaryCorollary`. Direct module typechecking is silent, and the axiom file
audits 40 declarations (`research/T23/axioms_u7.lean:5-44`).

## 3. Gaps

The report's sole gap is exact and honest:

```lean
∀ (Ω : Set Space), IsOpen Ω → Bornology.IsBounded Ω →
  IsRegularLevelDomain Ω → IBP Ω
```

It is recorded as unproved, not declared as an axiom
(`research/T23/SPEC_ISSUES.md:21-27`), and the public entry-point docstring says
that its regular-level-domain instance is the sole analytic residual
(`formalization/NSFormalization/Section3/T23/NoSlipUniqueness.lean:3-8`). A
repository-wide declaration search finds `IBP`, `ibp_box`, the conditional
theorem, and the box theorem, but no unrestricted theorem named
`noSlip_uniqueness` (`DomainSolution.lean:215,224`;
`DifferenceEnergy.lean:349,377`). Per the lead instruction, this absence is not
a rejection reason.

The required whole-tree Section4 searches gave:

```text
$ grep -rnEi 'regular.?level|level.?domain|level.?set.*domain' formalization/NSFormalization/Section4 --include='*.lean'
[no output; exit 1]
$ grep -rnEi 'no.?slip.*uniqu|uniqu.*no.?slip|domain.*velocity.*uniqu|velocity.*uniqu.*domain' formalization/NSFormalization/Section4 --include='*.lean'
[no output; exit 1]
$ grep -rnEi 'integral.*divergence|divergence.*integral|divergence theorem|stokes theorem' formalization/NSFormalization/Section4 --include='*.lean'
formalization/NSFormalization/Section4/A01/ConstructorAssembly.lean:71:weak-to-classical divergence theorem. -/
formalization/NSFormalization/Section4/A01/ConstructorDivergenceSlice.lean:24:test identity is `weak_divergence_test_integral`; the vendor packages the analytic weak-to-classical
[exit 0]
```

Those two Section4 hits are unrelated comments. The pinned Mathlib search returns
only coordinate/order-box suppliers. Inspection confirms that
`integral_divergence_of_hasFDerivAt_off_countable` integrates `Icc a b`
(`verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:266-288`),
its equivalence variant still assumes an order interval and an order-compatible
equivalence (`:313-335`), and the box-integral theorem is on `Box.Icc I`
(`verification/.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean:265-278`).
Thus the stated regular-level-domain IBP theorem is exactly what is still
missing; no declaration claims more.

## 4. Commands and results

All Lake commands below were run from `verification/` after sourcing
`../scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`, one at a time.

### Required build and typechecks

`lake build NSFormalization.Section3.T23.NoSlipUniqueness` exited 0. It emitted
only replayed, pre-existing dependency linter warnings; the T23 module itself was
silent. Exact first/last excerpt:

```text
⚠ [8778/8820] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]
...
⚠ [8814/8820] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (8820 jobs).
```

The following each exited 0 with exactly zero output:

```text
lake env lean ../formalization/NSFormalization/Section3/T23/NoSlipUniqueness.lean
lake env lean ../research/T23/probes/noslip_box_closes.lean
lake env lean ../research/T23/probes/noslip_uniqueness_closes.lean
lake env lean ../research/T23/probes/box_integration_by_parts_closes.lean
lake env lean ../research/T23/probes/rev478_nonvacuity.lean
```

`lake env lean ../research/T23/axioms_u7.lean` exited 0. The raw output has one
block for every `#print`; its first and last entries are:

```text
'NSFormalization.Section3.T23.box_face_mem_frontier' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.box_integral_divergence_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.box_integral_mul_fderiv_eq_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
...
'NSFormalization.Section3.T23.velocity_eq_of_ibp' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.noSlip_uniqueness_of_ibp' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.IsBoxDomain.open_bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.noSlip_uniqueness_box' depends on axioms: [propext, Classical.choice, Quot.sound]
```

An exact audit of the complete raw output returned:

```text
axiom declarations=40
nonstandard axiom lists=0
```

### Repository check

`. scripts/lean-env.sh && LEAN_NUM_THREADS=6 make check` exited 0. Per the raw
output limit, here are exact first/last excerpts (63,360 total lines):

```text
[first 40 lines]
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 712,
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
  "registered_contracts": 52,
...
[last 40 lines; total=63360]
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.MultipleRegions"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.043s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The copied-source admission and hash messages are pre-existing repository-wide
diagnostics; `make check` exits 0 and reports no reachable citation interface.

### Diff, conditional gates, and hygiene output

`git diff --name-status origin/erenup/integration-section3...HEAD` marks every
lane Lean module `A` (added), not `M`. The same base diff has no `verification/`
path (`grep '^verification/'`: no output, exit 1), so the brief's conditional
`scripts/gates.sh` and `check_contracts.py --base-ref
origin/erenup/integration-section3` gates do not apply.

The exact nonzero hygiene output is below, with the two offending terminal
spaces rendered as `[trailing space]`:

```text
$ git diff --check origin/erenup/integration-section3...HEAD
formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:389: new blank line at EOF.
formalization/NSFormalization/Section3/T23/DomainSolution.lean:271: new blank line at EOF.
formalization/NSFormalization/Section3/T23/NoSlipEnergy.lean:172: new blank line at EOF.
research/T23/ATTEMPTS_U7.md:425: trailing whitespace.
+../formalization/NSFormalization/Section3/T23/DomainTimeIntegral.lean:16:2: warning: Try this:[trailing space]
research/T23/ATTEMPTS_U7.md:433: trailing whitespace.
+../formalization/NSFormalization/Section3/T23/DomainTimeIntegral.lean:40:2: warning: Try this:[trailing space]
research/T23/probes/box_integration_by_parts_closes.lean:17: new blank line at EOF.
[exit 2]
```

This output and the citation offsets are the only reasons for
`ACCEPT-WITH-NOTES`; the mathematical statements, proofs, build gates, axiom
audit, substantive mutation, non-vacuity instance, and declared residual all
pass.
