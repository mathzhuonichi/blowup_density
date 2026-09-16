ACCEPT

## 1. What the lane claims

The worker claims three unconditional results for an arbitrary positive-viscosity
classical solution with admissible force:

1. `criticalDatumInputs_of_classical` fills exactly the two fields of
   `CriticalDatumInputs` (`velocityHalf_smooth` on `Ico 0 T` and the interior
   momentum identity); the source record really has only those two fields at
   `formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean:701-710`,
   and the delivered theorem has the claimed binders and conclusion at
   `formalization/NSFormalization/Section4/R43/CriticalMomentum.lean:319-324`.
2. `exists_criticalDatumPath'` removes the `CriticalDatumInputs` binder and
   returns `Nonempty (CriticalDatumPath w hf)` exactly as claimed at
   `formalization/NSFormalization/Section4/R43/CriticalMomentum.lean:326-331`.
3. `rcritical1_of_classical'` removes the carrier/momentum input and returns both
   the genuine `HasDerivAt` assertion and
   `E'/2 + (nu - trilinearConst*y)*z^2 <= b*y` on `Ioo 0 T`, exactly at
   `formalization/NSFormalization/Section4/R43/CriticalMomentum.lean:333-347`.

This is faithful to the lane brief and to the manuscript's
`1/2 (y^2)' + (nu-C_0 y)z^2 <= by` at
`paper/sections/04-whole-space.tex:91-99`.  The Lean quantities really are the
half-order velocity norm, three-halves dissipation norm, and half-order force
norm (`formalization/NSFormalization/Section4/R43/CriticalPairing.lean:50-60`),
and `criticalEnergyDerivative` is certified as the derivative of the squared
critical norm (`formalization/NSFormalization/Section4/R43/CriticalPairing.lean:239-269`).
The lane correctly claims only eq:Rcritical1, not the full global-regularity
conclusion of Proposition 4.3 (`paper/sections/04-whole-space.tex:82-88`).

The report's citation to lane 215 is honest.  Commit
`1768cd0871fc50566514c82b439eed7baf9bca18` contains the seven declarations at
`Section4/A04/RestartFixedForce.lean:14-183`; the copies at
`CriticalMomentum.lean:23-192` have the same statements/proofs modulo the new
namespace and explicit `A02.MemForceR` qualification.  The cited module and
report are absent from this lane's checked-out HEAD, as the worker states.

## 2. What is in Lean

The implementation matches the claimed route.

- The scalar and vector Bessel-to-homogeneous continuous linear maps are defined
  at `CriticalMomentum.lean:206-237`.  Their bound is the actual multiplier
  contraction, not an ENNReal `.toReal` shortcut: the symbol bound is proved at
  `formalization/NSFormalization/Source/BesselFractionalData.lean:15-32` and the
  datum norm contraction at `:55-70`.
- `chosenHomogeneousDatum_eq` uses genuine homogeneous-datum uniqueness
  (`CriticalMomentum.lean:239-249`); that uniqueness theorem identifies the
  underlying Fourier data at
  `formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:441-450`.
  The order-lowering map is the existing continuous linear map at
  `formalization/NSFormalization/Section4/D01/HalfOrder.lean:91-113`.
- The local-carrier window proof transfers the carrier's smooth datum path to
  the arbitrary solution on a relative neighborhood of each point, including
  the one-sided endpoint at zero (`CriticalMomentum.lean:153-192`).  Thus
  `criticalVelocityHalf_smooth` really has domain `Ico 0 T`, as required
  (`CriticalMomentum.lean:266-275`).
- The momentum proof uses the existing order-two datum identity, whose exact
  statement is
  `deriv G t = nu • L - N - P + F` at
  `formalization/NSFormalization/Section4/A04/MomentumDatum.lean:138-151`.
  It obtains honest order-two data for all four physical slices and transports
  the identity through the continuous linear map at
  `CriticalMomentum.lean:282-317`.  No sign or coefficient is hidden by a
  simplification.
- Assembly is direct: the two preceding theorems are exactly the two record
  fields at `CriticalMomentum.lean:319-324`, and the final theorem invokes the
  pre-existing exact scalar consequence at
  `formalization/NSFormalization/Section4/R43/Parseval.lean:138-151`.

There is no vacuity issue.  `ClassicalSolutionR` includes `0 < T`
(`formalization/NSFormalization/Section4/A02/SolutionClass.lean:112-138`), so
neither the half-open smoothness interval nor the interior momentum interval is
forced empty.  The homogeneous norms are attained whenever used
(`CriticalPairing.lean:62-91`), so this is not a `top.toReal = 0` proof.  The
named inputs are used in the local-carrier and momentum constructions at
`CriticalMomentum.lean:271` and `:289-299`; there is no fallback hypothesis.

The supplied non-vacuity check is genuine: `zeroCriticalMomentum` and a
`Nonempty (CriticalDatumPath ...)` example use `A04.zeroSol 1 2` at
`research/R43/axioms_critical_momentum.lean:28-39`.  The zero solution has the
actual positive horizon passed to it and satisfies the full classical-solution
record (`formalization/NSFormalization/Section4/A04/ZeroSolution.lean:87-105`).

The negative probe
`research/R43/probes/rev219_sign_mutation.lean:7-15` changes the main momentum
law's pressure term from `- criticalPressureHalf` to
`+ criticalPressureHalf`.  Lean rejects the theorem application with the
expected sign mismatch:

```text
../research/R43/probes/rev219_sign_mutation.lean:15:2: error: Type mismatch
  criticalVelocityHalf_momentum hν hf w
has type
  ∀ t ∈ Ioo 0 T,
    deriv (criticalVelocityHalf w) t =
      ν • criticalLaplacianHalf w t - criticalAdvectionHalf w t - criticalPressureHalf w t + criticalForceHalf t
but is expected to have type
  ∀ t ∈ Ioo 0 T,
    deriv (criticalVelocityHalf w) t =
      ν • criticalLaplacianHalf w t - criticalAdvectionHalf w t + criticalPressureHalf w t + criticalForceHalf t
```

Exit code was 1.

Hygiene is clean.  The worker commit adds the only production Lean module and
does not modify an existing one (`git show --name-status HEAD` marks
`CriticalMomentum.lean` `A`).  The required triple-dot comparison lists the
stacked lane-216 file as an addition as well; it is byte-identical to the copy
now at `origin/erenup/integration` (`git diff origin/erenup/integration HEAD --
.../CriticalDatumPath.lean` has zero output).  The forbidden-token scan is empty
after excluding the literal `#print axioms` directives.  The sole heartbeat
override is declaration-local, exactly `400000`, with its explanation
immediately above it at `CriticalMomentum.lean:277-282`.

## 3. Gaps

There is no remaining gap in the requested half-order velocity smoothness,
datum-level momentum identity, carrier construction, or eq:Rcritical1.

The worker separately records that G2/G3/G4 still lack a time-integrated
homogeneous force path / primitive.  A whole-tree declaration search under
`formalization/NSFormalization/Section4` supports that claim.  The only
`forceHomogeneousENorm` declarations are the definition, a lower bound, and a
conditional equality at
`formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:627-697`;
the file itself explicitly identifies strong measurability as missing at
`:21-29`.  There is no declaration combining `criticalForceHalf` or
`chosenHomogeneousDatum` with `AEStronglyMeasurable`/`MemLp`.  The only
`forcePrimitive` in the tree is the L2 slice primitive at
`formalization/NSFormalization/Section4/C01/EnergyBounds.lean:68-74`, not the
homogeneous half-order primitive.  The delivered force result remains correctly
slicewise at `CriticalDatumPath.lean:285-293`.  Thus those later gaps are real
and outside this lane, not concealed assumptions in the delivered theorem.

Exact concise search output:

```text
formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:627:def forceHomogeneousENorm (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : ℝ≥0∞ :=
formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:681:theorem eLpNorm_slice_le_forceHomogeneousENorm {q : ℝ≥0∞} {s : ℝ} (hs : -3 / 2 < s)
formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:690:theorem forceHomogeneousENorm_eq_of_aestronglyMeasurable {q : ℝ≥0∞} {s : ℝ} (hs : -3 / 2 < s)
formalization/NSFormalization/Section4/C01/EnergyBounds.lean:69:def forcePrimitive (f : A02.SpaceTimeField) (t : ℝ) : ℝ :=
```

The second search, for a declaration mentioning both
`criticalForceHalf|chosenHomogeneousDatum` and `AEStronglyMeasurable|MemLp`,
returned exactly zero output.

## 4. Commands and results

All Lean commands used `. scripts/lean-env.sh`; all `lake` invocations were from
`verification/` with `LEAN_NUM_THREADS=6`, one at a time.

1. `lake build NSFormalization.Section4.R43.CriticalMomentum` — exit 0.  The raw
   output has 298 lines / 17132 bytes and SHA-256
   `30b3214c84af2333dc664bf598d4efd55cfd237e6fc6153b7e1f1c7da2bf4d13` at
   `/tmp/rev219_build.log`.  Exact head/tail (the omitted middle consists only of
   replayed pre-existing dependency diagnostics; a search found no target-file
   warning/error):

   ```text
   ⚠ [8777/8830] Replayed NSFormalization.Source.FiniteHilbertBochner
   warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

   Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
   warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
     PiLp.single_apply

   Hint: Omit it from the simp argument list.
     [apply] simp [h]
   ...
   Note: This linter can be disabled with `set_option linter.style.haveILetI false`
   warning: NSFormalization/Source/FractionalRealization.lean:104:2: Try this:
     letI

   The goal is a proposition, so `let` is preferred over `letI`.
   The difference between `let` and `letI` is that `letI` inlines the value.
   But this is not relevant for proofs because of proof irrelevance.

   Note: This linter can be disabled with `set_option linter.style.haveILetI false`
   Build completed successfully (10534 jobs).
   ```

2. `lake env lean ../formalization/NSFormalization/Section4/R43/CriticalMomentum.lean`
   — exit 0, exact output: empty.

3. `lake env lean ../research/R43/axioms_critical_momentum.lean` — exit 0.
   Exact output:

   ```text
   'NSFormalization.Section4.R43.CarrierWindow.RestartFixedForce' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section4.R43.CarrierWindow.referenceForce_timeShift_norm_le' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section4.R43.CarrierWindow.restartFixedForce_of_memForceR' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section4.R43.CarrierWindow.shiftedSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.CarrierWindow.compact_hSeven_bound' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section4.R43.CarrierWindow.exists_carrier_window' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section4.R43.CarrierWindow.classical_hasSmoothSobolevPath' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section4.R43.CriticalHomogeneous.ofSobolevScalarLM' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section4.R43.CriticalHomogeneous.ofSobolevScalarL' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section4.R43.CriticalHomogeneous.ofSobolevVectorL' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section4.R43.CriticalHomogeneous.ofSobolevVectorL_apply' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section4.R43.CriticalHomogeneous.chosenHomogeneousDatum_eq' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section4.R43.CriticalHomogeneous.orderTwoToHalf' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section4.R43.CriticalHomogeneous.chosenHomogeneousDatum_eq_orderTwoToHalf' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section4.R43.criticalVelocityHalf_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.criticalVelocityHalf_momentum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.criticalDatumInputs_of_classical' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section4.R43.exists_criticalDatumPath'' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.rcritical1_of_classical'' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.zeroCriticalMomentum' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. Root `make check` — exit 0.  The raw JSON-heavy output has 28234 lines /
   1159606 bytes and SHA-256
   `53e5735ae5b3d64361191724499905c048222319647eebe528479aa66c435b1c` at
   `/tmp/rev219_make_check.log`.  Exact bounded output:

   ```text
   python3 experiments/check_formalization_plan.py --check
   {
     "task_count": 30,
     "source_counts": {
       "formalization": 533,
       "vendor/NavierStokesAndEuler": 2486,
       "vendor/HeliCorgi": 129
     },
     "source_manifest_entries": 2975,
     "missing_copied_imports": [],
     "citation_interfaces_reachable": [],
     "tokens_in_copied_umbrella_closure": [
   ...
     "base_compatibility_checked": false,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.045s

   OK
   python3 experiments/check_work_queue.py
   30 work items: ownership, contract registration and task cards consistent.
   ```

5. Extra honesty replay: `lake test` — exit 0; all registered tests report
   `checked; standard logical axioms only`, with only replayed dependency
   warnings.  `make test-mutations` — exit 0, exact final output:

   ```text
   implementation_refactor: accepted
   admitted_proof: rejected as required
   extra_axiom: rejected as required
   weakened_hypothesis: rejected as required
   Mutation suite passed. This is an infrastructure check, not a PDE proof.
   ```

6. Hygiene commands:

   - forbidden-token scan of the two worker-added Lean files, excluding literal
     `#print axioms` commands — exact output: empty;
   - `git diff --check origin/erenup/integration...HEAD` — exact output: empty;
   - heartbeat scan — exact output:

     ```text
     formalization/NSFormalization/Section4/R43/CriticalMomentum.lean:279:set_option maxHeartbeats 400000 in
     ```

7. `git diff --name-only origin/erenup/integration...HEAD` — exact output:

   ```text
   formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean
   formalization/NSFormalization/Section4/R43/CriticalMomentum.lean
   research/R43/ATTEMPTS_CRITICAL_DATUM.md
   research/R43/ATTEMPTS_CRITICAL_MOMENTUM.md
   research/R43/R43_SPLIT.md
   research/R43/REPORT_216.md
   research/R43/REPORT_219.md
   research/R43/axioms_critical_datum.lean
   research/R43/axioms_critical_momentum.lean
   ```

8. `git diff --name-only origin/erenup/integration...HEAD -- verification`
   — exact output: empty.  Therefore the brief's conditional
   `scripts/gates.sh` and `check_contracts.py --base-ref
   origin/erenup/integration` gates are not applicable.  The unconditional
   `make check` did run `check_contracts.py` successfully.

9. Negative probe command
   `lake env lean ../research/R43/probes/rev219_sign_mutation.lean` — exit 1
   with the expected error reproduced in Part 2.

No fixes requested.
