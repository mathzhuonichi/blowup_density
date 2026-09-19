ACCEPT

## 1. What the lane claims

The worker claims one public result:

```lean
theorem constantTransportCommutesLambda :
    ∀ (m : Space) (v Lv : SpatialField), SmoothPeriodicT v →
      IsPeriodicLambda v Lv →
        IsPeriodicLambda (constantTransportSpatialT m v)
          (constantTransportSpatialT m Lv)
```

That claim is accurate.  The delivered declaration is at
`formalization/NSFormalization/Section3/T20/TransportLambda.lean:52`, with its
full type at lines 52--56.  It is token-for-token the canonical
`CriticalRegularityTAPI.constantTransportCommutesLambda` field at
`formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:274`--`278`.
The two conformance examples at
`research/T20/probes/transport_lambda_closes.lean:34`--`37` independently
elaborate both the API projection and the theorem at the same named field type.

The mathematics matches the brief and paper.  The paper says that spatially
constant transport commutes with the corresponding Fourier multiplier at
`paper/sections/03-torus.tex:411`.  The fixed-time operator used by the field is
literally the spatial derivative in direction `m` at
`formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:52`--`56`.
`IsPeriodicLambda` is a smooth-periodic output plus the concrete multiplier
identity `sqrt(periodicAngularFrequencySq k)` at
`formalization/NSFormalization/Section3/T12/MeanZeroCalculus.lean:92`--`101`.
Thus the result asserts commutation of the two actual coefficient multipliers;
it is not an equality hidden behind an unconstrained predicate.

No hypothesis is vacuous or dishonest.  `hLv` supplies both smooth periodicity
of `Lv` and its Lambda coefficient graph, used at
`TransportLambda.lean:58,65`--`66`.  The separate `SmoothPeriodicT v`
hypothesis is used at line 66 to invoke the directional-derivative Fourier
formula on `v`; that formula genuinely requires smoothness and periodicity at
`formalization/NSFormalization/Section3/T20/CriticalEnergy.lean:191`--`198`.
There is no `toReal`, time interval, positivity side condition, unused binder,
or named input in this statement.

The reported non-vacuity witness is real.  The probe defines the cosine field
at `research/T20/probes/transport_lambda_closes.lean:41`--`42`, proves its
mean-zero part nonzero at lines 85--117, obtains an actual `Lv` from
`lambda_exists`, and applies U5 with the nonzero direction `e₀` at lines
121--129.  The supplying existence theorem constructs the physical Lambda
field and its coefficient graph at
`formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean:293`--`318`.

## 2. What is in Lean

The new module proves smooth periodicity of fixed constant transport at
`formalization/NSFormalization/Section3/T20/TransportLambda.lean:29`--`48`.
The main proof then unfolds the target coefficient identity, applies
`periodicFourierCoeff_fderiv_dir` to `Lv` and `v`, rewrites by the supplied
Lambda graph, and closes commutativity of the scalar symbols by `ring` at lines
57--67.  This is exactly the Fourier-side route requested by U5.  Fourier
injectivity is correctly unnecessary because the target itself is the
coefficientwise `IsPeriodicLambda` graph.

The positive closure probe compiles with zero output, including the exact field
match and nonzero witness (`transport_lambda_closes.lean:27`--`37,121`--`129`).
The axiom audit names precisely the public theorem at
`research/T20/axioms_u5.lean:6` and prints exactly
`[propext, Classical.choice, Quot.sound]`.

The substantive reviewer mutation is
`research/T20/probes/rev452_negative_sign.lean:21`--`42`.  It retains every
binder and hypothesis but flips the Lambda multiplier sign.  Replaying the
same coefficient rewrites leaves `A = -A`, and Lean rejects the proof at the
final `ring`; this confirms the sign is load-bearing rather than testing mere
argument arity.

Hygiene is clean.  A declaration/admission scan found no `sorry`, `admit`,
`axiom`, or `native_decide`, and no `maxHeartbeats` occurs in the module,
positive probe, axiom audit, or reviewer probe.  The worker commit `d1e9fc06`
adds one new formalization module and five research/record files; it modifies
no existing Lean file.  The full branch comparison also has no path under
`--diff-filter=M -- '*.lean'`.  The branch is intentionally stacked on lane
441, so the unfiltered comparison to the integration base also lists lane
441's new `GlobalRegularity.lean`; neither it nor any other existing Lean
module was edited by this lane.

## 3. Gaps

No mathematical, statement, build, axiom, citation, or hygiene gap was found.
The worker report declares no missing tree lemma, so the requested whole-tree
grep audit for a reported "not in the tree" gap is not applicable.  Its remark
that Fourier injectivity is unnecessary is not a missing-lemma claim; it
follows directly from the definition of `IsPeriodicLambda` at
`MeanZeroCalculus.lean:96`--`101`.

`verification/` was not touched by either `d1e9fc06` or the full branch diff.
Therefore the conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates do not
apply.  No fixes are required.

## 4. Commands and results

All Lean commands used `. scripts/lean-env.sh`; every `lake` command ran from
`verification/`, and builds used `LEAN_NUM_THREADS=6`.

1. Module build:

   ```text
   $ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.TransportLambda
   [exit 0]
   ```

   The raw run replayed pre-existing warnings from imported modules, emitted no
   warning from `TransportLambda.lean`, and ended exactly with:

   ```text
   Build completed successfully (10650 jobs).
   ```

   A filtered rerun (`... 2>&1 | rg 'TransportLambda|Build completed
   successfully'`, with `pipefail`) produced exactly:

   ```text
   Build completed successfully (10650 jobs).
   ```

2. Direct module check:

   ```text
   $ lake env lean ../formalization/NSFormalization/Section3/T20/TransportLambda.lean
   [exit 0; no output]
   ```

3. Positive closure/non-vacuity probe:

   ```text
   $ lake env lean ../research/T20/probes/transport_lambda_closes.lean
   [exit 0; no output]
   ```

4. Axiom audit:

   ```text
   $ lake env lean ../research/T20/axioms_u5.lean
   'NSFormalization.Section3.T20.constantTransportCommutesLambda' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   [exit 0]
   ```

5. Repository check:

   ```text
   $ make check
   [exit 0]
   ```

   The full command succeeded.  An exact status-filtered rerun printed:

   ```text
   python3 experiments/check_formalization_plan.py --check
   Explicit axiom/admission tokens, all copied sources: 11
   python3 experiments/check_contracts.py
   python3 experiments/test_contract_policy.py
   Ran 13 tests in 0.046s
   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

   The 11 copied-source tokens and the plan JSON's
   `"source_hashes_match": false` are pre-existing repository-wide diagnostics;
   the checker returns success, and none occurs in this lane's files.

6. Negative sign mutation:

   ```text
   $ lake env lean ../research/T20/probes/rev452_negative_sign.lean
   Try this:
     [apply] ring_nf

     The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

     Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
   ../research/T20/probes/rev452_negative_sign.lean:30:81: error: unsolved goals
   m : Space
   v Lv : SpatialField
   hv : SmoothPeriodicT v
   hLv : IsPeriodicLambda v Lv
   hOriginal : IsPeriodicLambda (constantTransportSpatialT m v) (constantTransportSpatialT m Lv)
   i : Fin 3
   k : PeriodicFrequency
   ⊢ (∑ x, ↑(m.ofLp x) * periodicDerivativeSymbol x k) * ↑√(periodicAngularFrequencySq k) *
         periodicFourierCoeff (fun x => ↑((v x).ofLp i)) k =
       -((∑ x, ↑(m.ofLp x) * periodicDerivativeSymbol x k) * ↑√(periodicAngularFrequencySq k) *
           periodicFourierCoeff (fun x => ↑((v x).ofLp i)) k)
   [exit 1, expected]
   ```

7. Hygiene scans:

   ```text
   $ rg -n '^[[:space:]]*(sorry|admit|axiom|native_decide)\b|:=[[:space:]]*(sorry|admit|native_decide)\b' <lane Lean files>
   [no output]
   $ rg -n 'maxHeartbeats' <lane Lean files>
   [no output]
   $ git diff --name-only --diff-filter=M d1e9fc06^ d1e9fc06 -- '*.lean'
   [no output]
   $ git diff --name-only --diff-filter=M origin/erenup/integration-section3...HEAD -- '*.lean'
   warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 34e9559010cf5d92ed57a36d5b5363eeacc313a8
   [no paths]
   $ git diff --name-only d1e9fc06^ d1e9fc06 -- verification 'verification/**'
   [no output]
   ```

8. Required unfiltered base comparison:

   ```text
   $ git diff --name-only origin/erenup/integration-section3...HEAD
   warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 34e9559010cf5d92ed57a36d5b5363eeacc313a8
   formalization/NSFormalization/Section3/T20/GlobalRegularity.lean
   formalization/NSFormalization/Section3/T20/TransportLambda.lean
   logs/LESSONS.md
   research/T20/ATTEMPTS_U12.md
   research/T20/ATTEMPTS_U5.md
   research/T20/REPORT_441.md
   research/T20/REPORT_452.md
   research/T20/T20_SPLIT.md
   research/T20/axioms_u12.lean
   research/T20/axioms_u5.lean
   research/T20/probes/global_regularity_closes.lean
   research/T20/probes/transport_lambda_closes.lean
   [exit 0]
   ```

   The reviewer files are untracked and therefore correctly absent from this
   committed-range output.
