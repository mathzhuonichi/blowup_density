ACCEPT

## 1. What the lane claims

The worker claims a complete implementation of all five requested parts: a
zero-extended reference, construction of `InsertionData`, discharge of
`RawPremises`, assembly of `PeriodicInsertionAPI`, all requested export lemmas,
the combined subcritical Sobolev limit, and `exists_force_close`
(`research/T19/REPORT_461.md:5-121`). It also claims 25 declarations with only
the three standard axioms, no gap, and no edit to an existing Lean module
(`research/T19/REPORT_461.md:123-143`).

Those claims are faithful to the brief and to the paper:

- The paper assumes a periodic reference smooth through `T + δ` and concludes
  exact lifespan `T`, blowup, the energy rate, the mixed rate, and the Sobolev
  rate (`paper/sections/03-torus.tex:287-310`). The exported Lean fields retain
  those constants and exponents exactly
  (`formalization/NSFormalization/Section3/T19/Threading.lean:141-199`), matching
  the source T18 fields
  (`formalization/NSFormalization/Section3/T18/Assembly.lean:81-96` and
  `formalization/NSFormalization/Section3/T18/Assembly.lean:127-169`).
- The paper's density proof uses the exact-lifespan inserted force in the
  regular branch and covers every `s < 1/2`
  (`paper/sections/03-torus.tex:349-365`). `exists_force_close` has precisely
  that content, with strict positive real radius and exact lifespan, at
  `formalization/NSFormalization/Section3/T19/Threading.lean:224-237`. It is the
  requested real-radius packaging of the canonical sharp reference clause at
  `formalization/NSFormalization/Section3/T19/Density.lean:84-93`.
- `RegularThroughT` really supplies `∃ δ > 0` and a nonempty classical
  solution on `T + δ`
  (`verification/Contracts/V1/TorusLocalTheory.lean:203-207`), exactly as unpacked
  by `exists_force_close` at
  `formalization/NSFormalization/Section3/T19/Threading.lean:230-237`.
- T15 fixes `place.T := T`, `chartRadius := 3/8`, and `x₀ := chartCenter`
  (`formalization/NSFormalization/Section3/T15/Assembly.lean:53-67`), so the lane's
  radius `1/4` and horizon reduction are honest
  (`formalization/NSFormalization/Section3/T19/Threading.lean:81-96`).
- The T17 bridge really asks for global spatial periodicity, open-slab
  smoothness, divergence, packet support, and ball inclusion
  (`formalization/NSFormalization/Section3/T17/SlabBridge2.lean:20-31`), and its
  proved constructor is `correctionStatementSlab'_holds`
  (`formalization/NSFormalization/Section3/T17/SlabBridge2.lean:192-220`). The
  lane supplies each of those hypotheses directly at
  `formalization/NSFormalization/Section3/T19/Threading.lean:91-96`.

No hypothesis makes the result vacuous. In particular, `eps_pos` makes every
small-scale filter/interval argument substantive
(`formalization/NSFormalization/Section3/T19/Threading.lean:131-135` and
`formalization/NSFormalization/Section3/T19/Threading.lean:221-222`), and
`hr' : 0 < r'` is converted to the genuinely positive ENNReal target at
`formalization/NSFormalization/Section3/T19/Threading.lean:227-233`. There is no
`toReal ⊤` escape or empty-interval proof.

## 2. What is in Lean

All statements printed in the worker report exist with the stated types:

- `extendByZero` transports every `ClassicalSolutionT` field, including local
  momentum and pressure gauge, at
  `formalization/NSFormalization/Section3/T19/Threading.lean:18-55`. Its equality
  on the original `Ico` slab, global spatial periodicity, and open-slab
  smoothness are at
  `formalization/NSFormalization/Section3/T19/Threading.lean:57-73`.
- `insertionData` selects the registered packet, builds the T15 placement and
  scaling objects, chooses the T17 correction, and stores the zero extension at
  `formalization/NSFormalization/Section3/T19/Threading.lean:79-116`. The raw
  support and nonnegative energy/dissipation premises are proved at
  `formalization/NSFormalization/Section3/T19/Threading.lean:118-124`; the source
  record requires exactly those three clauses at
  `formalization/NSFormalization/Section3/T18/Assembly.lean:171-176`.
- `insertion` is the actual T18 assembly at
  `formalization/NSFormalization/Section3/T19/Threading.lean:126-127`. The direct
  exports, including both honesty guards, occupy
  `formalization/NSFormalization/Section3/T19/Threading.lean:131-204` and agree
  field-for-field with T18.
- The nonnegative- and negative-order cases are combined without an analytic
  premise at `formalization/NSFormalization/Section3/T19/Threading.lean:206-222`.
  The reused power-limit lemma has exactly the required exponents
  (`formalization/NSFormalization/Paper1/ScalingLimits.lean:10-16`).

The worker conformance file restates every requested export and closes it by
`exact` (`research/T19/probes/threading_closes.lean:18-123`). The axiom file
lists all 25 declarations (`research/T19/axioms_u0.lean:3-27`).

The report did not contain a closed non-vacuity instance, so I added one. It
uses viscosity `1`, zero initial datum, zero force, horizon `1`, margin `1`, and
the repository's genuine rest solution to construct a sigma witness containing
both `InsertionData` and its `PeriodicInsertionAPI`
(`research/T19/probes/rev461_nonvacuity.lean:13-41`). It typechecks with zero
output.

The substantive negative mutation changes the exact lifespan from `T` to
`T + 1` (`research/T19/probes/rev461_negative_lifespan.lean:19-22`). Lean rejects
the unchanged proof with the expected error:

```text
../research/T19/probes/rev461_negative_lifespan.lean:22:2: error: Type mismatch
  NSFormalization.Section3.T19.lifespan hν ha hg hT hδ reference
has type
  ∀ ε ∈ Ioc 0 ins.ε₀, maximalLifespanT ν a (ins.force ε) = ENNReal.ofReal T
but is expected to have type
  ∀ ε ∈ Ioc 0 ins.ε₀, maximalLifespanT ν a (ins.force ε) = ENNReal.ofReal (T + 1)
```

## 3. Gaps

No mathematical or implementation gap remains. The worker report makes no
"not in the tree" gap claim, so the requested whole-Section4 missing-lemma
search is not applicable. Its only upstream negative claim is correct: the old
slab statement is explicitly refuted by `not_correctionStatementSlab` at
`formalization/NSFormalization/Section3/T17/SlabBridge.lean:53-61`, while this
lane imports and uses the amended proved statement.

Hygiene is clean:

- The forbidden-token/heartbeat scan of `Threading.lean` and the worker probe
  produced no output. The `sorry` text in `ATTEMPTS_U0.md` is a quoted historical
  cascading diagnostic, not source code
  (`research/T19/ATTEMPTS_U0.md:3-14`).
- No `set_option maxHeartbeats` occurs in the implementation.
- `git diff --name-status origin/erenup/integration-section3...HEAD -- '*.lean'`
  reports only `A` entries. It warns that the branch has multiple merge bases,
  which is why the already-merged T15/Scaling3 additions also appear; no
  existing Lean file is marked `M`. Lane commit `e5b9e31a` itself contains only
  the new T19 module/research files and the intended `T19_SPLIT.md` update.
- `git diff --check` exits 0.

The worker report's citations and route note are consistent with the actual
tree. In particular, the U0 completion and the U7/U8/U9/U13 route are recorded
at `research/T19/T19_SPLIT.md:22-35`.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`; all `lake` commands ran from
`verification/` with `LEAN_NUM_THREADS=6`.

1. `lake build NSFormalization.Section3.T19.Threading`

   Exit 0. Lake replayed warnings from pre-existing dependency modules only;
   there was no line from `Threading.lean`. The exact terminal line was:

   ```text
   Build completed successfully (10655 jobs).
   ```

2. `lake env lean ../formalization/NSFormalization/Section3/T19/Threading.lean`

   Exit 0, exact output: `(no output)`.

3. `lake env lean ../research/T19/probes/threading_closes.lean`

   Exit 0, exact output: `(no output)`.

4. `lake env lean ../research/T19/probes/rev461_nonvacuity.lean`

   Exit 0, exact output: `(no output)`.

5. `lake env lean ../research/T19/probes/rev461_negative_lifespan.lean`

   Exit 1 with the exact expected diagnostic pasted in Part 2.

6. `lake env lean ../research/T19/axioms_u0.lean`

   Exit 0. Exact output:

   ```text
   'NSFormalization.Section3.T19.zeroExtension_eventuallyEq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.extendByZero' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.extendByZero_velocity_eqOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.extendByZero_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.extendByZero_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.insertionData' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.insertionData_rawPremises' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.insertion' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.insertion_eps_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.force_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.forceDifference_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.lifespan' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.blowup_limsup' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.energyRate' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.forceDiffMixedConst_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.forceDifference_mixed_memLp' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.forceDifference_mixed_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.forceDiffSobolevConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.forceDifference_sobolev_memLp' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.forceDifference_sobolev_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.forceDifference_negativeSobolev_tendsto' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T19.negative_s_memLp' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.forceDifference_sobolev_tendsto' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T19.exists_force_close' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

7. `make check`

   Exit 0. The command emits the full generated closure arrays; the exact
   invariant-bearing terminal output was:

   ```text
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.046s

   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

   The preceding `check_contracts.py` JSON reported exactly
   `"registered_contracts": 50`; `check_formalization_plan.py` reported
   `"task_count": 45`, no missing copied imports, and the known informational
   copied-source token in `Paper1/BoundaryCorollary.lean` outside this closure.

8. `scripts/gates.sh NSFormalization.Section3.T19.Threading`

   Exit 0. It reran `make check`, the module build, all registered tests, and the
   mutation suite. Exact terminal output:

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

9. `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`

   Exit 0. Exact terminal fields:

   ```text
     "base_compatibility_checked": true,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   ```

10. Hygiene commands

    The forbidden-token scan, both `git diff --check` invocations, and the
    lane-local source scan produced no findings. The exact Lean status list was:

    ```text
    warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 76630e3e363ab6f22e52992d6f8e2f05cbf18236
    A formalization/NSFormalization/Section3/T15/Assembly.lean
    A formalization/NSFormalization/Section3/T19/Threading.lean
    A research/T15/axioms_u15.lean
    A research/T15/probes/assembly_closes.lean
    A research/T19/axioms_u0.lean
    A research/T19/probes/threading_closes.lean
    A verification/Bindings/Scaling3.lean
    A verification/Contracts/V1/Scaling3.lean
    A verification/Tests/Scaling3.lean
    ```

Verdict: ACCEPT. Fixes: none.
