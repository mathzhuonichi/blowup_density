ACCEPT

## 1. What the lane claims

The worker claims one theorem, `BlowupDensity.Bindings.completedSobolevDensity`,
with the first field of `REnergyAPI` verbatim: compact smooth forces satisfying
the prescribed lifespan bound are dense in the full completed
`L^q(0,∞;H^s)` space for `q ∈ {1,2}` and `s < criticalOrder q.toReal`
(`research/R46/REPORT_256.md:5`).  It also claims a zero-target non-vacuity
specialization (`research/R46/REPORT_256.md:13`) and no extra satisfiability
hypothesis or remaining gap for this field (`research/R46/REPORT_256.md:21`).

Those claims are accurate.  The other two R46 fields are explicitly described
only as out of scope for lane 256 (`research/R46/REPORT_256.md:22`), not as
results proved by this lane.

## 2. What is in Lean

### Statement fidelity

- The theorem exists at
  `verification/Bindings/CompletedSobolevDensity.lean:27`.  Its type through
  line 34 has the same binders, order, strict threshold, and target as the spec
  field at `research/R46/Spec.lean:81`: `a ∈ initialClassR`, positive `ν` and
  `T`, `q = 1 ∨ q = 2`, `s < criticalOrder q.toReal`, and
  `CompletedDense q s (breakdownSetIn forceClassCompact ν a T)`.
- This is the requested mathematics.  The paper says smooth compact forces with
  `T_max^ν(a,f) ≤ T` are dense in every full `L^q(0,∞;H^s)` for
  `q ∈ {1,2}` and `s < s_q` at
  `paper/sections/04-whole-space.tex:218-219`.  The registered vocabulary has
  `criticalOrder q = 2/q - 3/2` at
  `verification/Contracts/V1/Data.lean:259`, compact smooth forces at
  `verification/Contracts/V1/Data.lean:559-563`, and exactly the lifespan
  sublevel set at `verification/Contracts/V1/Data.lean:672-674`.
  `CompletedDense` expands to arbitrary completed data and arbitrary positive
  `ℝ≥0∞` radii at `verification/Contracts/V1/Data.lean:732-744`; there is no
  `.toReal` distance or restricted target hidden in the statement.
- The proof follows the claimed composition.  B01's implementation really
  proves `CompletedDense q s forceClassCompact`
  (`formalization/NSFormalization/Section4/B01/Compact.lean:155-180`) and its
  registered binding points to that theorem
  (`verification/Bindings/BochnerPartial.lean:65-82`).  Compact relative
  density has the required strict threshold and lifespan target at
  `verification/Bindings/CompactClassDensity.lean:50-77`.  Path addition and
  its honest integrability premises are exactly the contract fields at
  `verification/Contracts/V1/DatumLemmas.lean:309-325`.
- In the lane proof, the compact approximation is obtained at lines 41-42, the
  compact relative-density step at lines 43-44, the infimum witness at lines
  45-46, and the two integrability premises at lines 47-66 of
  `verification/Bindings/CompletedSobolevDensity.lean`.  The final measurable
  path and Bochner triangle bound are lines 67-76.  Every main hypothesis is
  used: `a,ν,T,q,s` feed `density_compact`; `q` also yields `1 ≤ q` and
  `q ≠ ⊤`; the completed datum and radius feed `approxCompact` and the final
  triangle estimate.  No hypothesis was added, no interval was emptied, and
  no `⊤.toReal = 0` route occurs.

### Non-vacuity and negative test

The lane's own non-vacuity example is at
`verification/Bindings/CompletedSobolevDensity.lean:80-94`.  I additionally
fixed the radius to `1`, so the probe asserts an actual member of the breakdown
set rather than merely restating a universally quantified implication
(`research/R46/probes/rev256_nonvacuity.lean:13-28`).  It typechecks silently.

The substantive mutation in
`research/R46/probes/rev256_mutation.lean:14-31` widens the main statement from
`s < criticalOrder q.toReal` to the closed endpoint
`s ≤ criticalOrder q.toReal`, while keeping the proof's arguments.  Lean rejects
the density step for the intended reason:

```text
../research/R46/probes/rev256_mutation.lean:31:51: error: Application type mismatch: The argument
  hs
has type
  s ≤ criticalOrder q.toReal
but is expected to have type
  s < criticalOrder q.toReal
in the application
  Bindings.density_compact ν hν T hT q hq s a ha hs
```

### Axioms and hygiene

`research/R46/axioms_sobolev_density.lean:3` audits the only named theorem and
prints exactly `[propext, Classical.choice, Quot.sound]`.  The lane's Lean files
contain no `sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats` option.
`git diff --diff-filter=M ... -- '*.lean'` is empty: the only lane Lean module
is new, and no existing module, binding, contract, or test was modified.  The
full lane diff contains only the new binding, its audit and records, plus the
required update to `research/R46/COMPARISON.md`.

## 3. Gaps

There is no gap in the reviewed first field and no named assumption to isolate.
The proof handles `r = ⊤` honestly: each half-radius inequality supplies a
finite summand, and `ENNReal.add_lt_add` is used before
`ENNReal.add_halves` (`verification/Bindings/CompletedSobolevDensity.lean:75-76`).

The report's two remaining R46 fields are scope notes, not "not in the tree"
claims.  I nevertheless ran the required whole-tree searches.  There is no
`completedHomogeneousDensity` or `strongTrajectoryClosure` declaration in
`formalization/NSFormalization/Section4`; there is, correctly, a lower-level
homogeneous approximation theorem at
`formalization/NSFormalization/Section4/B02/ApproxCompact.lean:229`, matching
the report's statement that only its R46 composition remains.  The search for
a `Tendsto` theorem involving `forceHomogeneousENorm`, or a named homogeneous
convergence theorem, returned no match.  Thus the worker did not overlook an
already assembled theorem while describing the other clauses as separate work.

Exact search output:

```text
$ grep -rn "completedHomogeneousDensity\|strongTrajectoryClosure" formalization/NSFormalization/Section4
[no output; exit 0 because the review command used `|| true`]

$ grep -rn "approxCompactHomogeneous" formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/B02/ApproxCompact.lean:6:# B02 final field (lane 110): `approxCompactHomogeneous` and its export
formalization/NSFormalization/Section4/B02/ApproxCompact.lean:9:`HomogeneousApproxAPI`, `approxCompactHomogeneous` (`Spec.lean:607`), together
formalization/NSFormalization/Section4/B02/ApproxCompact.lean:208:/-! ## 3. The spec field `approxCompactHomogeneous` (`research/B02/Spec.lean:607`) -/
formalization/NSFormalization/Section4/B02/ApproxCompact.lean:210:/-- **`approxCompactHomogeneous`** (`research/B02/Spec.lean:607`).  For every
formalization/NSFormalization/Section4/B02/ApproxCompact.lean:229:theorem approxCompactHomogeneous : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ s : ℝ, SplitRange s →

$ grep -rnE "Tendsto.*forceHomogeneousENorm|forceHomogeneousENorm.*Tendsto|homogeneous.*[Cc]onvergence" formalization/NSFormalization/Section4
[no output; exit 0 because the review command used `|| true`]
```

## 4. Commands and results

All Lake commands were run from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

1. `lake build Bindings.CompletedSobolevDensity`: exit 0.  The command replayed
   pre-existing dependency lints but emitted no diagnostic from
   `CompletedSobolevDensity.lean`.  Exact terminal line:

   ```text
   Build completed successfully (10616 jobs).
   ```

   The quiet/error-level confirmation
   `lake -q --log-level=error build Bindings.CompletedSobolevDensity` exited 0
   with exactly zero output.

2. `lake env lean Bindings/CompletedSobolevDensity.lean`: exit 0, exactly zero
   output.

3. `lake env lean ../research/R46/axioms_sobolev_density.lean`: exit 0, exact
   output:

   ```text
   'BlowupDensity.Bindings.completedSobolevDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. `make check`: exit 0.  Its raw JSON/closure output was very large; per the
   review-output size rule, the exact terminal check is reproduced here:

   ```text
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.046s

   OK
   python3 experiments/check_work_queue.py
   30 work items: ownership, contract registration and task cards consistent.
   ```

5. `make test`: exit 0.  It began with `lake -d verification test`, replayed the
   registered contract checks, and ended exactly with:

   ```text
   info: Tests.TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
   info: Tests.MainThresholds.lean:15:0: Contract BlowupDensity.Tests.checkedMainThresholds: checked; standard logical axioms only
   ```

6. `scripts/gates.sh Bindings.CompletedSobolevDensity`: exit 0.  Exact tail:

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

7. `python3 experiments/check_contracts.py --base-ref origin/erenup/integration
   | tail -3`: exit 0, exact output:

   ```text
     "base_compatibility_checked": true,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   ```

8. `lake env lean ../research/R46/probes/rev256_nonvacuity.lean`: exit 0,
   exactly zero output.  The mutated endpoint probe exited 1 with the expected
   type mismatch quoted in part 2.

9. Hygiene commands and exact outputs:

   ```text
   $ git diff --name-only origin/erenup/integration...HEAD
   research/R46/ATTEMPTS_SOBOLEV_DENSITY.md
   research/R46/COMPARISON.md
   research/R46/REPORT_256.md
   research/R46/axioms_sobolev_density.lean
   verification/Bindings/CompletedSobolevDensity.lean

   $ git diff --diff-filter=M --name-only origin/erenup/integration...HEAD -- '*.lean'
   [no output]

   $ rg -n "set_option maxHeartbeats|\b(sorry|admit|axiom|native_decide)\b" verification/Bindings/CompletedSobolevDensity.lean research/R46/axioms_sobolev_density.lean
   [no output]

   $ git diff --check origin/erenup/integration...HEAD
   [no output]
   ```

No fixes required.
