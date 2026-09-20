ACCEPT-WITH-NOTES

## 1. What the lane claims

This review treats the first-stage partial as accepted history and reviews the
continuation against `research/T23/REPORT_487b.md`, as directed by the lead.  The
continuation claims four substantive results:

1. The U2b/U3 seam is closed by replacing U3's global radial-potential premise
   with an operational window core that contains only the facts U3 uses
   (`research/T23/REPORT_487b.md:5-9`).
2. One supplier family is selected and all 48 fields of
   `BoundaryInsertionAPI` are assembled without exposing supplier clauses in the
   registered statement (`research/T23/REPORT_487b.md:11-15,34-38`).
3. `T04.boundary_insertion` registers the G0 existential repair, packet-indexed,
   with boxes unconditional and the smooth-domain case conditional on explicit
   `IBP Ω`; the universal prescribed-cutoff statement is excluded
   (`research/T23/REPORT_487b.md:17-22,56-68`).
4. The full unit-box witness and standard-axiom/build/contract gates pass
   (`research/T23/REPORT_487b.md:43-50,70-98`).

The mathematical target agrees with the manuscript.  The paper assumes a
bounded box or bounded smooth domain and a compatible reference past `T`
(`paper/sections/03-torus.tex:632-646`), places the construction in any
prescribed interior ball (`paper/sections/03-torus.tex:646,653-655`), uses the
domain/zero-extension norms and subcritical range (`paper/sections/03-torus.tex:647-651,657-663`),
and concludes by no-slip uniqueness that the inserted solution is singular
exactly at `T` (`paper/sections/03-torus.tex:664`).  The local potential and
correction really only operate in the controlled ball/window
(`paper/sections/03-torus.tex:176-192,212-215`).

## 2. What is in Lean

### Statement fidelity and the G2 seam

The old `LocalCorrectionCore` still contains the global `potential_formula` and
the potential/correction formulas (`formalization/NSFormalization/Section3/T23/LocalCorrection.lean:253-303`).
The new `WindowedCorrectionCore` has exactly ten operational fields: positive
cutoff radius, time/space scale bounds, correction smoothness/divergence/support,
cancellation, and the two cross transports.  It has no potential identity at
all (`formalization/NSFormalization/Section3/T23/LocalCorrection.lean:548-575`).
Every old core projects to it (`formalization/NSFormalization/Section3/T23/LocalCorrection.lean:578-597`).

This is genuinely weaker, not a renamed global identity.  The review probe
replaces `D.potential` by an arbitrary spacetime field while retaining every
window-core field (`research/T23/probes/rev487_windowed_core_weaker.lean:13-64`),
and Lean accepts it with zero output.  Conversely, the historical diagnostic
shows that the old core forces global potential equality
(`formalization/NSFormalization/Section3/T23/Assembly.lean:50-58`).  The binding
constructs the window core only from equality on
`Ioo 0 (T+δ) × ball x₀ r` (`verification/Bindings/BoundaryInsertion.lean:284-304`),
and the supplier-to-core theorem uses local agreement plus the operational
cancellation/transports (`formalization/NSFormalization/Section3/T23/Assembly.lean:60-102`).

The changed U3 proofs refer only to those operational fields: the occurrences
in `Triple.lean` are correction support/smoothness/divergence and cross
transports, not `potential_formula`, `potential_smooth`, `potential_curl`, or
`correction_formula` (`formalization/NSFormalization/Section3/T23/Triple.lean:160-336`).
`Solution.lean` changes only the core parameter of its two constructors
(`formalization/NSFormalization/Section3/T23/Solution.lean:33-82`).  The original
U3 probe explicitly projects the old core at nine call sites, so the previously
proved interface still elaborates
(`research/T23/probes/T23-U3-triple-solution_closes.lean:1224-1302`).

The continuation authorization was respected.  Against the requested base, the
only pre-existing production modules modified for G2 are the authorized
`LocalCorrection.lean`, `Triple.lean`, and `Solution.lean`; there is no
`PressureNormalization.lean` diff:

```text
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using cbfc6f5e28a9364295e1f0b6dda553fa74952da5
M formalization/NSFormalization/Section3/T23/LocalCorrection.lean
M formalization/NSFormalization/Section3/T23/Solution.lean
M formalization/NSFormalization/Section3/T23/Triple.lean
```

### The 48-field assembly

`boundaryInsertionAPI` exists with the claimed parameters and hypotheses
(`formalization/NSFormalization/Section3/T23/Assembly.lean:308-350`).  Its record
literal contains 48 named assignments, one for every field, with no placeholder
(`formalization/NSFormalization/Section3/T23/Assembly.lean:412-468`).  In
particular the four U9 fields are directly `hΩ`, `hδ`, `hg`, and `ha`
(`formalization/NSFormalization/Section3/T23/Assembly.lean:412-416`), while the
same record threads:

- U1/U2/U3 through the positive common threshold, triple, and solution
  (`formalization/NSFormalization/Section3/T23/Assembly.lean:351-440`);
- U8 lifespan/maximality/blowup through the same velocity and solution family
  (`formalization/NSFormalization/Section3/T23/Assembly.lean:441-447`);
- U4 transports/support, U5 comparison, U6 rates/convergence, and U7 uniqueness
  (`formalization/NSFormalization/Section3/T23/Assembly.lean:448-468`).

The production binding obtains an outer ball, one matching supplier, its
literal supplier cutoff, local agreement, and the window core
(`verification/Bindings/BoundaryInsertion.lean:266-307`).  It then derives the
packet/correction estimates from that same `C`/`A`/`D` family and calls the
48-field assembler (`verification/Bindings/BoundaryInsertion.lean:308-349`).
Thus no named supplier hypothesis survives in the registered theorem.  The
contract/canonical conversions also assign all 48 fields in both directions
(`verification/Bindings/BoundaryInsertion.lean:471-583`) and their round trips
are definitionally `rfl` (`verification/Bindings/BoundaryInsertion.lean:585-586`).

The interval is nonempty: the assembled threshold has a strict positivity proof
(`formalization/NSFormalization/Section3/T23/Assembly.lean:351-364,418-421`).
The box domain is a genuine strict-coordinate box, not `True`
(`verification/Contracts/V1/BoundaryInsertion.lean:243-262`), and the API's
domain/reference hypotheses are concrete, including the prescribed closed ball
(`formalization/NSFormalization/Section3/T23/Boundary.lean:134-166`).  There is
no `⊤.toReal = 0` escape or empty scale interval.  The public `0 < ν` premise is
redundant with the packet's stored viscosity positivity, but it is the paper's
honest positive-viscosity assumption and does not make the statement vacuous.
The exceptional `IBP Ω` hypothesis is isolated to the conditional branch.

### Registered statement

The contract's repaired statement quantifies a registered `PacketImportAPI` and
existentially chooses both `C` and `D`, pins the supplier time/margin/center/radius,
requires local reference agreement, pins all seven cutoff data fields, and
returns a nonempty 48-field API
(`verification/Contracts/V1/BoundaryInsertion.lean:795-812`).  The box theorem
has `IsBoxDomain Ω` and no `IBP Ω` premise
(`verification/Contracts/V1/BoundaryInsertion.lean:814-831`); the general
box-or-smooth theorem has explicit `IBP Ω`
(`verification/Contracts/V1/BoundaryInsertion.lean:833-850`).  V1 is precisely
their conjunction (`verification/Contracts/V1/BoundaryInsertion.lean:852-853`).

The binding proves the conditional theorem without unconsumed supplier inputs,
derives box domain structure and `ibp_box` for the unconditional branch, and
packages the conjunction (`verification/Bindings/BoundaryInsertion.lean:589-613`).
The registry entry is version 1 under parent `T04`; its scope explicitly says
G0 existential, packet/48-field, box-unconditional, smooth-level conditional on
`IBP Ω`, owner-pending G0/G1 wording, and explicitly excludes the universal
cutoff statement (`verification/contracts.json:599-607`).  The test checks the
complete conjunction and both projections
(`verification/Tests/BoundaryInsertion.lean:7-16`).  The base and head counts
were independently read as 54 and 55.

### Negative and non-vacuity checks

The substantive mutation deletes `IsBoxDomain Ω` from the unconditional
theorem's statement while leaving all other quantifiers/conclusions intact
(`research/T23/probes/rev487_drop_box_hypothesis.lean:18-40`).  It fails exactly
at the missing box witness:

```text
../research/T23/probes/rev487_drop_box_hypothesis.lean:40:43: error: Application type mismatch: The argument
  hδ
has type
  0 < δ
but is expected to have type
  IsBoxDomain Ω
in the application
  Bindings.BoundaryInsertion.Contract.boundaryInsertionStatement'_box_holds ν hν P place Ω norms a g r δ reference hδ
```

The positive probe uses the actual open unit box, zero initial datum/force and
zero reference, center `(1/2,1/2,1/2)`, prescribed radius `1/4`, supplier radius
`1/8`, and `ν = T = δ = 1`
(`research/T23/probes/assembly_box_closes.lean:11-85`).  It proves the registered
packet is nonzero from its speed blowup (`research/T23/probes/assembly_box_closes.lean:87-92`)
and guards both declarations to the standard three axioms
(`research/T23/probes/assembly_box_closes.lean:96-101`).

## 3. Gaps and hygiene

No mathematical field or registration obligation remains open.  Per the lead's
instruction, the accepted G0/G1 owner-pending V1 wording and the first-stage
partial are not rejection grounds.  `REPORT_487b.md` correctly excludes an
unconditional regular-level-domain IBP theorem and the universal-cutoff
registration (`research/T23/REPORT_487b.md:56-68`).  The required whole-tree
negative search found no exact T23 boundary API, regular-level domain, no-slip
uniqueness, or general `IBP` declaration in Section4:

```text
$ grep -rnE 'IsRegularLevelDomain|IsBoundedBoxOrSmoothDomain|BoundaryInsertionAPI|boundaryInsertionStatement|noSlip_uniqueness|def IBP|theorem ibp_' formalization/NSFormalization/Section4 --include='*.lean'
grep_exit=1
```

Changed Lean files contain no code declaration using `sorry`, `admit`, `axiom`,
or `native_decide`, no `set_option maxHeartbeats`, and no import of the forbidden
`Paper1.BoundaryCorollary` module.  The only forbidden-token grep hits were prose
comments that explicitly say the sorry-bearing file is cited but not imported.
The 54 guarded U9 declarations are listed in
`research/T23/axioms_u9.lean:3-218`; there are 54 `#print axioms` commands and 54
matching expectations, all exactly `[propext, Classical.choice, Quot.sound]`.

One non-mathematical discrepancy prevents a bare `ACCEPT`: the worker report says
`git diff --check` passed (`research/T23/REPORT_487b.md:91`), but the requested
base diff currently reports trailing whitespace in
`research/T23/ATTEMPTS_T23-U6-rates-convergence.md:118,124,130,136,145` and
`research/T23/probes/T23-U6-rates-convergence_closes.lean:48`, plus a blank line
at EOF in `research/T23/REPORT_483.md:118`.  These are inherited U6/U4 record/probe
hygiene issues, not Lean or statement defects.

```text
exit_code=2
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using cbfc6f5e28a9364295e1f0b6dda553fa74952da5
research/T23/ATTEMPTS_T23-U6-rates-convergence.md:118: trailing whitespace.
+  
research/T23/ATTEMPTS_T23-U6-rates-convergence.md:124: trailing whitespace.
+  
research/T23/ATTEMPTS_T23-U6-rates-convergence.md:130: trailing whitespace.
+  
research/T23/ATTEMPTS_T23-U6-rates-convergence.md:136: trailing whitespace.
+  
research/T23/ATTEMPTS_T23-U6-rates-convergence.md:145: trailing whitespace.
+  
research/T23/REPORT_483.md:118: new blank line at EOF.
research/T23/probes/T23-U6-rates-convergence_closes.lean:48: trailing whitespace.
+example : 
```

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`; every `lake` command was run
from `verification/` with `LEAN_NUM_THREADS=6`.

1. `lake build NSFormalization.Section3.T23.Assembly` — exit 0.  The target module
   emitted no warning of its own; Lake replayed pre-existing upstream linter
   warnings.  Exact first/last output excerpt:

   ```text
   ⚠ [8778/8979] Replayed NSFormalization.Source.FiniteHilbertBochner
   warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
   ```

   [Middle omitted.]

   ```text
   Build completed successfully (10695 jobs).
   ```

2. Direct module and guarded U9 audit:

   ```text
   $ lake env lean ../formalization/NSFormalization/Section3/T23/Assembly.lean
   [exit 0; 0 output bytes]
   $ lake env lean ../research/T23/axioms_u9.lean
   [exit 0; 0 output bytes]
   prints=54
   standard_expectations=54
   nonstandard_expectations=0
   ```

3. U1-U8 compatibility and full assembly probes — every Lean invocation had
   zero output:

   ```text
   PASS placement_closes.lean (0 Lean output)
   PASS local_correction_closes.lean (0 Lean output)
   PASS T23-U2b-matching-supplier_closes.lean (0 Lean output)
   PASS T23-U3-triple-solution_closes.lean (0 Lean output)
   PASS T23-U4-differences-boundary_closes.lean (0 Lean output)
   PASS T23-U5-domain-comparison_closes.lean (0 Lean output)
   PASS T23-U6-rates-convergence_closes.lean (0 Lean output)
   PASS box_integration_by_parts_closes.lean (0 Lean output)
   PASS noslip_box_closes.lean (0 Lean output)
   PASS noslip_uniqueness_closes.lean (0 Lean output)
   PASS T23-U8-interior-blowup_closes.lean (0 Lean output)
   PASS assembly_supplier_closes.lean (0 Lean output)
   PASS assembly_box_closes.lean (0 Lean output)
   ```

   The separate review strict-weakness probe also exited 0 with zero output.

4. `make check` — exit 0, 69,290 output lines.  Per the raw-output limit, exact
   first/last excerpts only:

   ```text
   python3 experiments/check_formalization_plan.py --check
   {
     "task_count": 45,
     "source_counts": {
       "formalization": 744,
       "vendor/NavierStokesAndEuler": 2486,
       "vendor/HeliCorgi": 129
     },
     "source_manifest_entries": 2975,
     "missing_copied_imports": [],
     "citation_interfaces_reachable": [],
   ```

   [Middle omitted.]

   ```text
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

   The displayed historical `BoundaryCorollary.lean` admission and
   `source_hashes_match: false` are repository-wide inventory diagnostics; the
   command exits 0 and the lane does not import that module.

5. `make test` — exit 0.  Exact new contract line:

   ```text
   info: Tests/BoundaryInsertion.lean:10:0: Contract BlowupDensity.Tests.checkedBoundaryInsertion: checked; standard logical axioms only
   ```

6. `make test-mutations` — exit 0.  Exact tail:

   ```text
   implementation_refactor: accepted
   admitted_proof: rejected as required
   extra_axiom: rejected as required
   weakened_hypothesis: rejected as required
   Mutation suite passed. This is an infrastructure check, not a PDE proof.
   ```

7. `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
   — exit 0.  Exact filtered result, after the full JSON succeeded:

   ```text
   {
     "registered_contracts": 55,
     "base_compatibility_checked": true
   }
   ```

   Independent registry counts:

   ```text
   base_registered_contracts=54
   head_registered_contracts=55
   ```

8. `BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T23.Assembly`
   — exit 0, 69,808 output lines.  Exact first/last excerpts only:

   ```text
   == make check
   python3 experiments/check_formalization_plan.py --check
   {
     "task_count": 45,
   ```

   [Middle omitted.]

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

9. Hygiene counters:

   ```text
   assembly_field_assignments=48
   contract_conversion_field_assignments=48
   u9_axiom_prints=54
   u9_axiom_standard_guards=54
   changed_forbidden_code_tokens=0
   changed_heartbeat_overrides=0
   changed_forbidden_imports=0
   ```

Fixes required for a clean bare accept:

1. Remove trailing spaces at `research/T23/ATTEMPTS_T23-U6-rates-convergence.md:118,124,130,136,145` and `research/T23/probes/T23-U6-rates-convergence_closes.lean:48`.
2. Remove the extra blank line at EOF at `research/T23/REPORT_483.md:118`.
3. Rerun `git diff --check`; once it is clean, `research/T23/REPORT_487b.md:91` becomes accurate without any Lean or mathematical change.
