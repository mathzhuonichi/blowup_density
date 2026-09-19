ACCEPT-WITH-NOTES

## 1. What the lane claims

The lane claims a canonical, contract-free T23 vocabulary rather than a proof of
the boundary corollary: a 48-field raw `BoundaryInsertionAPI`, the literal false
statement, the owner-pending repaired statement, a 73-field raw adapter for the
registered whole-space correction record, and three auxiliary geometry lemmas
(`research/T23/REPORT_480.md:5-16`, `research/T23/REPORT_480.md:20-33`). That is
the correct scope. In particular, the report explicitly does **not** claim an
inhabitant of either statement (`research/T23/REPORT_480.md:12-13,45-50`).

Statement fidelity passes:

- The paper says bounded box or smooth domain, compatible smooth no-slip
  reference, prescribed interior ball, `L²(Ω)` energy, `L¹Hˢ(Ω)` force control,
  a fixed compact interior support, boundary agreement, no-slip uniqueness, and
  singularity exactly at `T` (`paper/sections/03-torus.tex:632-651,654-664`).
  The canonical record contains precisely these obligations: domain/reference
  fields at `formalization/NSFormalization/Section3/T23/Boundary.lean:134-166`,
  the inserted solution and boundary fields at `:181-336`, localization and
  rates at `:338-450`, and uniqueness at `:452-465`.
- The 48 field names and order match the Spec record
  (`research/T23/Spec.lean:690-1021`) exactly. A mechanical field-name/order
  diff returned `FIELD_NAME_ORDER_DIFF_EXIT=0`; the compiled forward and reverse
  record maps cover every field (`research/T23/probes/boundary_api_on_canonical.lean:1369-1484`).
  The entire original Spec is embedded byte-for-byte: comparing
  `research/T23/Spec.lean` with probe lines 2-1084 produced exactly
  `SPEC_EMBED_DIFF_EXIT=0`.
- The literal statement is the Spec statement after the required raw packet
  substitution (`formalization/NSFormalization/Section3/T23/Boundary.lean:482-494`;
  exact `rfl` check at `research/T23/probes/boundary_api_on_canonical.lean:1529-1540`).
  Its arbitrary `D` defect is exposed, not hidden: `eps_pos` and
  `eps_le_cutoff` are incompatible when `D.ε₀ = 0`
  (`formalization/NSFormalization/Section3/T23/Boundary.lean:171-179,517-529`).
- The repair is exactly the lead-approved G0 addendum
  (`research/T23/SPEC_ISSUES.md:124-144`): `0 < r`, both ball inclusions, a jointly
  selected full correction supplier and cutoff, time/margin/center/radius
  identities, reference agreement, and all seven cutoff identities appear at
  `formalization/NSFormalization/Section3/T23/Boundary.lean:497-515`. The raw
  binder equality is checked at
  `research/T23/probes/boundary_api_on_canonical.lean:1542-1559`, and equivalence
  with the contract-side existential is proved at `:1568-1593`.
- The predecessor records are canonical and have the claimed sizes: 16 placement
  fields (`formalization/NSFormalization/Section3/T23/Placement.lean:35-112`),
  seven cutoff fields (`formalization/NSFormalization/Section3/T23/LocalCorrection.lean:16-56`),
  and ten solution fields (`formalization/NSFormalization/Section3/T23/DomainSolution.lean:104-140`).
  The raw packet convention agrees with T18's `InsertionData`
  (`formalization/NSFormalization/Section3/T18/Insertion.lean:30-57`). Exact count
  output was:

  ```text
  48
  73
  16
  7
  10
  ```

- `WholeSpaceCorrectionAPI` begins at
  `formalization/NSFormalization/Section3/T23/WholeSpaceCorrection.lean:16` and
  ends with its 73rd field at `:349-352`. Its registered source is
  `verification/Contracts/V1/Correction.lean:197-533`; both 73-field conversions
  and both arbitrary-record round trips compile
  (`research/T23/probes/boundary_api_on_canonical.lean:1176-1339`). The only
  implementation-side `structure CorrectionAPI` found elsewhere is the distinct
  torus interface at
  `formalization/NSFormalization/Section3/T17/Correction.lean:71-100`.
- All four theorem claims in the report have the stated types: compactness,
  positive inner closed ball, and open-domain frontier separation are at
  `formalization/NSFormalization/Section3/T23/Geometry.lean:8-29`; the exact G0
  obstruction is at
  `formalization/NSFormalization/Section3/T23/Boundary.lean:517-529`. The three
  one-line consumers are at
  `research/T23/probes/boundary_api_on_canonical.lean:1486-1489`.

No hidden vacuity was found. `IsBoundedBoxOrSmoothDomain` includes openness,
boundedness, nonemptiness, and the genuine box/smooth disjunction
(`formalization/NSFormalization/Section3/T23/DomainSolution.lean:46-61`). Thus
the use of `(volume Ω).toReal` in the pressure mean
(`formalization/NSFormalization/Section3/T23/Boundary.lean:93-102`) is guarded in
the API by a finite, positive-volume domain, rather than by `⊤.toReal = 0`.
Admissible scale intervals are nonempty because `eps_pos` is a field before every
`Ioc 0 ε₀` conclusion (`formalization/NSFormalization/Section3/T23/Boundary.lean:171-179`).
The legacy `r` and `norms` parameters in the literal record are redundant exactly
as in the frozen Spec; they do not make it vacuous. The repaired statement makes
`r` positive and load-bearing (`formalization/NSFormalization/Section3/T23/Boundary.lean:504-511`).

The reviewer non-vacuity probe constructs an actual bounded box/domain-class
witness (`research/T23/probes/rev480_nonvacuity.lean:11-28`), an inhabited
16-field placement (`:30-39`), a positive inner radius and both ball inclusions
(`:41-61`). It typechecks with zero output.

## 2. What is in Lean

The public module imports the existing placement, local correction, domain
solution/uniqueness, and T22 norm vocabularies rather than restating them
(`formalization/NSFormalization/Section3/T23/Boundary.lean:1-7`). It defines the
domain lifespan/maximal predicate and concrete norms/gauge at `:24-102`, the
48-field interface at `:109-465`, both statement definitions at `:467-515`, and
only the negative G0 theorem at `:517-529`. There is no existence theorem.

The canonical probe checks more than field names: placement/cutoff/solution/full
correction round trips are at
`research/T23/probes/boundary_api_on_canonical.lean:1093-1339`, the lifespan and
maximal predicates are transported at `:1341-1364`, and all 48 boundary fields
are transported in both directions at `:1369-1484`. This is adequate evidence
that the raw substitutions did not change the mathematics.

The three requested geometry lemmas are faithful to the paper's “smaller closed
ball strictly inside Ω” step (`paper/sections/03-torus.tex:654`): compactness is
unconditional, the smaller radius is strictly positive, and frontier separation
has the explicit `IsOpen Ω` premise
(`formalization/NSFormalization/Section3/T23/Geometry.lean:8-29`).

Hygiene is otherwise clean. Searches of the three new production modules found
no proof occurrence of `sorry`, `admit`, `axiom`, or `native_decide`, no `True`
field, and no `maxHeartbeats`/`set_option`. The only `sorry` strings in the wider
T23 sources are provenance comments, e.g.
`formalization/NSFormalization/Section3/T23/DomainSolution.lean:101-103`.
There is no direct forbidden import in the reviewed modules
(`formalization/NSFormalization/Section3/T23/Boundary.lean:1-7`).

The exact requested branch comparison warns about multiple merge bases and lists
all T23 Lean files as additions, not modifications. The stronger command
`git diff --diff-filter=M --name-only origin/erenup/integration-section3...HEAD -- '*.lean'`
produced no output, so the lane's “no existing Lean module edited” claim is
correct. No file under `verification/` is in the diff.

One minor hygiene/reporting defect remains: `research/T23/REPORT_480.md:74-75`
says `git diff --check` passed, but the specified base-range check exits 2 on
inherited lane-478 whitespace. This does not affect Lean or statement fidelity,
but it requires the exact cleanup listed below.

## 3. Gaps

The report's open gaps are honest and remain outside U-CAN: no theorem proves
`boundaryInsertionStatement'`, no matching I02/I03 inhabitant is constructed,
U3-U6/U8 and registration remain future work, and unrestricted smooth-domain
IBP remains open (`research/T23/REPORT_480.md:43-50`). A search for an inhabitant
or `_holds` theorem found only the existential binder itself at
`formalization/NSFormalization/Section3/T23/Boundary.lean:508`.

The required full-tree Section4 gap searches were run before accepting these
claims:

```text
$ grep -rnE 'structure[[:space:]]+CorrectionAPI|def[[:space:]]+CorrectionAPI|abbrev[[:space:]]+CorrectionAPI' formalization/NSFormalization/Section4 --include='*.lean'
[no output]

$ grep -rnE 'BoundaryInsertionAPI|boundaryInsertionStatement|ClassicalSolutionOmega|WholeSpaceCorrectionAPI|noSlip_uniqueness|IsRegularLevelDomain|regular.?level|RegularLevel|bounded.*domain.*uniqu|domain.*lifespan|DomainSolution' formalization/NSFormalization/Section4 --include='*.lean'
[no output]
```

The broader implementation-tree correction-record search returned only
`formalization/NSFormalization/Section3/T17/Correction.lean:71`, whose signature
is the torus placement/reference/cutoff interface, not registered I02's
whole-space record (`formalization/NSFormalization/Section3/T17/Correction.lean:71-100`).
The Section4 IBP search returned only unrelated Fourier/compact-support
integration-by-parts material, for example
`formalization/NSFormalization/Section4/A04/NonlinearBound.lean:76-162` and
`formalization/NSFormalization/Section4/D01/OrderZeroCurl.lean:67-89`, not a
regular-level-domain divergence theorem. This supports, without overstating,
the G1 residual recorded at `research/T23/SPEC_ISSUES.md:21-39,76-80`.

The substantive negative mutation changes the G0 threshold constant from `0`
to `1`, never drops an argument
(`research/T23/probes/rev480_zero_cutoff_one_mutation.lean:10-34`). Running the
unguarded proof failed as expected:

```text
../research/T23/probes/rev480_zero_cutoff_one_mutation.lean:23:26: error: Application type mismatch: The argument
  A.eps_pos
has type
  0 < A.ε₀
but is expected to have type
  1 < A.ε₀
in the application
  not_lt_of_ge hl A.eps_pos
```

The final `#guard_msgs` probe records that exact diagnostic at
`research/T23/probes/rev480_zero_cutoff_one_mutation.lean:12-34` and itself exits
0 with zero output.

## 4. Commands and results

Every Lean command sourced `. scripts/lean-env.sh`; Lake ran only from
`verification/` with `LEAN_NUM_THREADS=6`.

1. Seven predecessor modules:

   ```text
   $ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T23.Placement NSFormalization.Section3.T23.LocalCorrection NSFormalization.Section3.T23.SpatialExtension NSFormalization.Section3.T23.LocalCorrectionBridge NSFormalization.Section3.T23.StatementRepair NSFormalization.Section3.T23.NoSlipUniqueness NSFormalization.Section3.T23.BoxIntegration
   [upstream replayed linter warnings only]
   Build completed successfully (9915 jobs).
   ```

2. Canonical module:

   ```text
   $ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T23.Boundary
   [upstream replayed linter warnings only; no diagnostic from a T23 module]
   Build completed successfully (10087 jobs).

   $ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T23/Boundary.lean
   [no output]
   ```

   Exit 0 in both cases. Direct checks of `Geometry.lean`,
   `WholeSpaceCorrection.lean`, and
   `research/T23/probes/boundary_api_on_canonical.lean` also exit 0 with exactly
   zero output.

3. Axiom audit, exit 0; exact output:

   ```text
   'NSFormalization.Section3.T23.domainMaximalLifespan' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.IsMaximalDomainSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.domainEnergyEssSup' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.domainEnergyGradient' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.domainEnergyENorm' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.domainForceSobolevENorm' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.zeroExtForceSobolevENorm' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.domainPressureMean' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.domainNormalizePressure' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.BoundaryInsertionAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.boundaryInsertionStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.boundaryInsertionStatement'' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.prescribed_closedBall_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.exists_inner_closedBall' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.prescribed_closedBall_disjoint_frontier' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T23.WholeSpaceCorrectionAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.boundaryInsertionAPI_zero_cutoff' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   ```

4. `make check`, exit 0. Its decisive exact output was:

   ```text
   python3 experiments/check_formalization_plan.py --check
     "task_count": 45,
     "missing_copied_imports": [],
     "citation_interfaces_reachable": [],
     "tokens_in_copied_umbrella_closure": [
         "module": "NSFormalization.Paper1.BoundaryCorollary",
         "line": 90,
         "token": "sorry"
     "tracked_cache_free": true,
     "source_hashes_match": false
   Explicit axiom/admission tokens, all copied sources: 11
   python3 experiments/check_contracts.py
     "registered_contracts": 54,
     "base_compatibility_checked": false,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.043s

   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

   The omitted middle of `check_contracts.py` is only its very large closure
   lists; there was no error. The umbrella admission and hash mismatch are the
   disclosed repository-wide diagnostics, not part of Boundary's import closure
   (`research/T23/REPORT_480.md:52-55`).

5. Reviewer probes:

   ```text
   $ LEAN_NUM_THREADS=6 lake env lean ../research/T23/probes/rev480_zero_cutoff_one_mutation.lean
   [no output]
   $ LEAN_NUM_THREADS=6 lake env lean ../research/T23/probes/rev480_nonvacuity.lean
   [no output]
   ```

   Both exit 0; the first succeeds because `#guard_msgs` requires the mutation's
   exact failure.

6. Git/conditional gates:

   ```text
   $ git diff --diff-filter=M --name-only origin/erenup/integration-section3...HEAD -- '*.lean'
   [no output]
   $ git diff --name-only origin/erenup/integration-section3...HEAD -- verification
   [no output]
   ```

   Therefore `scripts/gates.sh` and
   `check_contracts.py --base-ref origin/erenup/integration-section3` are not
   applicable under the brief's “if `verification/` was touched” condition.

   The hygiene check is the sole note:

   ```text
   $ git diff --check origin/erenup/integration-section3...HEAD
   warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 6bb89798de160005a84876bd0e2df201ff879bde
   formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:389: new blank line at EOF.
   formalization/NSFormalization/Section3/T23/DomainSolution.lean:271: new blank line at EOF.
   formalization/NSFormalization/Section3/T23/NoSlipEnergy.lean:172: new blank line at EOF.
   research/T23/ATTEMPTS_U7.md:425: trailing whitespace.
   +../formalization/NSFormalization/Section3/T23/DomainTimeIntegral.lean:16:2: warning: Try this: [trailing space shown by the check]
   research/T23/ATTEMPTS_U7.md:433: trailing whitespace.
   +../formalization/NSFormalization/Section3/T23/DomainTimeIntegral.lean:40:2: warning: Try this: [trailing space shown by the check]
   research/T23/probes/box_integration_by_parts_closes.lean:17: new blank line at EOF.
   ```

   Exit 2. The pre-existing modified lane brief remains untouched, as required.

Exact fixes before merge:

- Delete the extra final blank line at `formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:389`.
- Delete the extra final blank line at `formalization/NSFormalization/Section3/T23/DomainSolution.lean:271`.
- Delete the extra final blank line at `formalization/NSFormalization/Section3/T23/NoSlipEnergy.lean:172`.
- Strip the trailing spaces at `research/T23/ATTEMPTS_U7.md:425` and `research/T23/ATTEMPTS_U7.md:433`.
- Delete the extra final blank line at `research/T23/probes/box_integration_by_parts_closes.lean:17`.
- Rerun the base-range `git diff --check`; once clean, `research/T23/REPORT_480.md:74-75` is accurate.
