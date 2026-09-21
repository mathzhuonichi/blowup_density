ACCEPT

## 1. What the lane claims

The worker claims two declarations: `regularReference_compact`, the
`Y = forceClassCompact` specialization of the reconciled R45
`regularReference` field, and the optional companion
`regularReference_of_memForceR` with the same epsilon-form conclusion in
`forceClassR` (`research/R45/REPORT_254.md:5-15`).  It also claims that the
compact proof uses one insertion record, shrinks its scale to cover an arbitrary
`τ < T`, preserves compact force membership, and introduces no supplier
hypothesis (`research/R45/REPORT_254.md:19-36` and
`research/R45/ATTEMPTS_COMPACT_RIDER.md:5-24,43-45`).

The mathematical source supports that target.  Theorem 4.1 promises the same
earlier history, exact singular time, and convergence in `E_T`
(`paper/sections/04-whole-space.tex:8-13`); Theorem 4.2 makes the history window
`0 ≤ t ≤ T - 2ε²`, makes the force correction spacetime compact, and gives the
two convergence statements (`paper/sections/04-whole-space.tex:31-42`).
Corollary 4.5 says that all of Theorem 4.1 remains valid after replacing
`F_R` by `F_c` or `F_rd`, specifically because the correction is compact and
addition preserves those classes (`paper/sections/04-whole-space.tex:194-198`).

## 2. What is in Lean

1. **PASS — exact main statement.**  The Spec field quantifies, in order,
   `ν,T,q,s,a,g,δ,v,τ,r,η` and concludes compact-class membership, a full
   `ClassicalSolutionR`, exact lifespan, the two strict bounds, and pointwise
   history on the closed interval `[0,τ]`
   (`research/R45/Spec.lean:130-147`).  After the advertised specialization
   `Y = forceClassCompact`, the theorem has exactly those binders and conjuncts
   (`verification/Bindings/CompactClassRider.lean:29-46`).  The independent
   `#check` probe prints that exact type
   (`research/R45/probes/rev254_statements.lean:5`).

2. **PASS — exact companion statement.**  `regularReference_of_memForceR`
   differs from the main statement only by replacing both occurrences of
   `forceClassCompact` with `forceClassR`; it retains every guard and conjunct
   (`verification/Bindings/CompactClassRider.lean:118-135`).  This is precisely
   the epsilon form obtained from the registered Tendsto-shaped family rider,
   whose one family jointly carries force membership, exact lifespan, a full
   solution, `[0,T-2ε²]` history, and both limits
   (`verification/Contracts/V1/MainThresholds.lean:79-98`).  The second
   independent `#check` prints the claimed type
   (`research/R45/probes/rev254_statements.lean:6`).

3. **PASS — honest proof dependencies.**  The compact proof calls
   `insertionLifespanV2_of_data` once
   (`verification/Bindings/CompactClassRider.lean:48-52`).  That supplier asks
   for the original datum, `MemForceR g`, and a strict lifespan lower bound and
   returns a record definitionally tied to `a,g,T`
   (`verification/Bindings/InsertionFromData.lean:87-110`).  Registered
   uniqueness identifies the record reference with the named solution on the
   common interval (`verification/Contracts/V1/Uniqueness.lean:89-94` and
   `verification/Bindings/CompactClassRider.lean:56-67`).  The V2 record gives
   the full-horizon classical solution
   (`verification/Contracts/V2/InsertionLifespan.lean:117-131`), while its
   inherited lifespan field gives exact equality, not merely `≤`
   (`verification/Contracts/V1/InsertionFamily.lean:421-434`).

4. **PASS — cutoff arithmetic and compact membership.**  Positivity of
   `T-τ` makes `min 1 ((T-τ)/4)` positive; the chosen scale belongs both to the
   genuine record interval and to this smaller nonempty interval
   (`verification/Bindings/CompactClassRider.lean:87-97`).  The proof derives
   `ε² ≤ ε` from `0 < ε ≤ 1`, then `τ ≤ T-2ε²`, and feeds exactly that inequality
   to the registered history field
   (`verification/Bindings/CompactClassRider.lean:98-114`), whose source
   statement is exactly the paper's endpoint
   (`verification/Contracts/V1/InsertionFamily.lean:222-226`).  Compactness is
   obtained from the registered compact difference
   (`verification/Contracts/V1/InsertionFamily.lean:259-266`) and the honest
   addition lemma (`verification/Bindings/CompactClassDensity.lean:29-46`), not
   from a stronger named premise.

5. **PASS — non-vacuity and hypotheses.**  There is no norm `.toReal` premise,
   no `⊤.toReal = 0` route, and no empty scale interval.  The only `toReal` is
   the required exponent conversion in `criticalOrder q.toReal`.  Although the
   proof does not need to invoke the named hypothesis `0 ≤ τ`, the statement
   retains it, so the requested history interval cannot be empty.  The audit
   instantiates `ν=T=1`, `a=g=0`, `δ=1`, and `τ=0` with the genuine zero
   solution on `[0,2)`; it proves zero-force compact membership and applies the
   theorem at positive finite radii (`research/R45/axioms_compact_rider.lean:19-45`).
   Thus even the endpoint history interval contains `t=0`.

6. **PASS — hygiene and citations.**  The changed Lean files contain no
   `sorry`, `admit`, `axiom`, or `native_decide`, and contain no
   `set_option maxHeartbeats`.  `git diff --diff-filter=M --name-only
   origin/erenup/integration...HEAD -- '*.lean'` is empty: the branch adds Lean
   modules but modifies none.  Commit `96b2862` adds the rider module and audit
   and modifies only the requested research comparison note; the extra compact
   density additions visible in the branch diff are the stacked lane-252 base.
   The module's citations to the Spec and Corollary 4.5 are consistent with
   `research/R45/Spec.lean:112-147` and
   `paper/sections/04-whole-space.tex:194-198`.

7. **PASS — substantive negative check.**  The scratch probe preserves the
   complete main theorem but flips the force error from `f - g` to `f + g`
   (`research/R45/probes/rev254_mutated_sign.lean:18-38`).  Lean rejects the
   unchanged proof with the expected mismatch at line 38:

   ```text
   ../research/R45/probes/rev254_mutated_sign.lean:38:2: error: Type mismatch
     regularReference_compact
   has type
     ... forceSobolevENorm q s (f - g) < r ...
   but is expected to have type
     ... forceSobolevENorm q s (f + g) < r ...
   ```

   Exit status was `1`.  No argument was dropped.

## 3. Gaps

No compact-rider proof or hypothesis gap remains.  The report correctly leaves
the rapid-class `density`, `zeroIff`, and `regularReference` instances and
`schwartzDensity` outside this lane (`research/R45/REPORT_254.md:38-44`).  The
required whole-tree search was:

```text
$ grep -rnE 'schwartzDensity|density_rapid|zeroIff_rapid|regularReference_rapid|forceClassRapid|MemForceRapid' formalization/NSFormalization/Section4
[no output]
grep_exit=1
```

The same check run as literal `grep -rn` once per declared gap returned:

```text
density_rapid exit=1 matches=0
zeroIff_rapid exit=1 matches=0
regularReference_rapid exit=1 matches=0
schwartzDensity exit=1 matches=0
forceClassRapid exit=1 matches=0
MemForceRapid exit=1 matches=0
```

A broader case-insensitive search for rapid-decay, Schwartz-density, and
regular-reference wording found only unrelated reference/local-theory comments,
not any missing rapid R45 result.  A repository-wide Lean search found the
rapid statements only in the R45 drafts/Spec and the class definition in
`verification/Contracts/V1/Data.lean:565-578`; it found no proof declaration.

## 4. Commands and results

Every Lean/Lake command sourced `scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, and ran Lake from `verification/`.

- `lake build Bindings.CompactClassRider` — exit `0`.  The 298-line output
  consists of replayed upstream/vendor diagnostics and ends exactly:

  ```text
  Note: This linter can be disabled with `set_option linter.style.haveILetI false`
  Build completed successfully (10609 jobs).
  ```

  It contains no diagnostic from `Bindings/CompactClassRider.lean`.  Exact log:
  17,132 bytes, SHA-256
  `fbe20ca18e911f98b3acc2f76030a04f807ccef7f710972faf25869e1d14ae1e`.

- `lake env lean Bindings/CompactClassRider.lean` — exit `0`, exact output:

  ```text
  [no output]
  ```

- `lake env lean ../research/R45/axioms_compact_rider.lean` — exit `0`, exact
  output:

  ```text
  'BlowupDensity.Bindings.regularReference_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
  'BlowupDensity.Bindings.regularReference_of_memForceR' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

  The following non-vacuity example elaborated silently.

- `make check` — exit `0`.  Because the generated closure JSON is 33,680 lines,
  its exact head/tail rather than all 1,385,378 bytes is pasted:

  ```text
  python3 experiments/check_formalization_plan.py --check
  {
    "task_count": 30,
    "source_counts": {
      "formalization": 547,
      "vendor/NavierStokesAndEuler": 2486,
      "vendor/HeliCorgi": 129
    },
  ...
  python3 experiments/test_contract_policy.py
  .............
  ----------------------------------------------------------------------
  Ran 13 tests in 0.044s

  OK
  python3 experiments/check_work_queue.py
  30 work items: ownership, contract registration and task cards consistent.
  ```

  Exact full-log SHA-256:
  `550e067ed34f095384350da816f0d42521297c1d25d1087d27f51325958b8611`.

- `make test` — exit `0`.  The 364-line output contains replayed diagnostics and
  the registered contract checks; its exact tail is:

  ```text
  ℹ [10695/10698] Replayed Tests.MaximalPartialV2
  info: Tests/MaximalPartialV2.lean:24:0: Contract BlowupDensity.Tests.checkedMaximalPartialV2: checked; standard logical axioms only
  ℹ [10696/10698] Replayed Tests.InsertionLifespanV2
  info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
  ℹ [10697/10698] Replayed Tests.TameProduct
  info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
  ℹ [10698/10698] Replayed Tests.MainThresholds
  info: Tests/MainThresholds.lean:15:0: Contract BlowupDensity.Tests.checkedMainThresholds: checked; standard logical axioms only
  ```

  Exact full-log SHA-256:
  `39db64c4a2c627c1b5191913a95ae1a215287c49b7e3e83cc1027f7836e7ad76`.

- `scripts/gates.sh Bindings.CompactClassRider` — exit `0`.  Gate markers were
  exactly:

  ```text
  == make check
  == lake build Bindings.CompactClassRider
  == make test
  == make test-mutations
  == check_contracts
  == gates OK
  ```

  Exact tail:

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

  Exact full aggregate log: 34,024 lines, 1,407,378 bytes, SHA-256
  `84bc9996fbe1f20c4741997f8554b6e972bf6354744f1fc501dfae7f4cb6e3dc`.

- `python3 experiments/check_contracts.py --base-ref
  origin/erenup/integration` — exit `0`.  Exact head/tail:

  ```text
  {
    "registered_contracts": 32,
    "closures": {
  ...
    },
    "base_compatibility_checked": true,
    "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
  }
  ```

  Exact full-log size: 33,648 lines, 1,384,407 bytes; SHA-256
  `095b765d49b28810ce39572d6847c973c3f065d042193a1dde38c1f580bab4b6`.

- `git diff --name-status origin/erenup/integration...HEAD` produced exactly:

  ```text
  A research/R45/ATTEMPTS_COMPACT.md
  A research/R45/ATTEMPTS_COMPACT_RIDER.md
  M research/R45/COMPARISON.md
  A research/R45/REPORT_252.md
  A research/R45/REPORT_254.md
  A research/R45/axioms_compact_class.lean
  A research/R45/axioms_compact_rider.lean
  A verification/Bindings/CompactClassDensity.lean
  A verification/Bindings/CompactClassRider.lean
  ```

  `git diff --check origin/erenup/integration...HEAD` and the modified-Lean-file
  query both exited `0` with no output.  No git mutation was performed.

No fixes are required.
