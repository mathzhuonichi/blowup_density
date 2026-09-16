ACCEPT

# Review 215-A04-restart-fixed-force

## 1. What the lane claims

The report makes three material claims, and the checked Lean declarations match them.

1. `RestartFixedForce` fixes `ν`, `f`, and `S`, then chooses `δ` after a finite
   `K` but before both `t₀ ∈ Icc 0 S` and the datum `a'`; the datum bound is H⁷
   and the conclusion is a lower bound on the selected `localHorizon'`
   (`formalization/NSFormalization/Section4/A04/RestartFixedForce.lean:14-18`).
   `restartFixedForce_of_memForceR` has exactly the requested hypotheses
   `0 < ν`, `MemForceR f`, and `0 ≤ S` and proves that proposition
   (`RestartFixedForce.lean:41-43`). Appendix A says that one common positive
   duration is needed while `t₀ ↑ S`, with the force bounded on `[0,S+1]`
   (`paper/sections/appendix-a-local-theory.tex:146-153`). The lane's H⁷
   fixed-force recut is the one explicitly requested by this lane brief; it
   does not pretend to prove the paper's stronger H¹/all-force interface.

2. `higherOrderBound_of_gronwall` inhabits the pre-existing, unchanged
   `HigherOrderBound` (`RestartFixedForce.lean:233-263`). The latter still
   quantifies over every natural order and every `t ∈ Ico 0 S`
   (`formalization/NSFormalization/Section4/A04/Continuation.lean:184-193`),
   and the conformance file checks this spelling by definitional equality
   (`research/A04/axioms_restart_fixed_force.lean:26-33`). This is precisely
   Appendix A's conclusion that finite eq:criterion control uniformly bounds
   every H^m norm up to `S` (`appendix-a-local-theory.tex:127-147`).

3. The three fixed-force consumers exist at
   `RestartFixedForce.lean:274-312`, `:298-323`, and `:325-354`. They use the
   same fixed force and restart times `t ∈ Ico 0 S`, passed into the closed
   restart interval using `ht.2.le` (`:287-296`). The report correctly states
   that the two final `..._of_memForceR` theorems are not unconditional: both
   retain the single named `ShiftedLocalExtension` input (`:265-272`,
   `:315-323`, `:343-354`).

No claimed unconditional shifted-gluing theorem is present in the report.

## 2. What is in Lean

### Statement and proof fidelity

- The force-window proof uses the antitone selected horizon, not the vendor's
  unrelated existential duration. `referenceForce_timeShift_norm_le` maps
  `r ∈ [0,1]` and `t₀ ∈ [0,S]` to `r+t₀ ∈ [0,S+1]`
  (`RestartFixedForce.lean:20-37`), and
  `restartFixedForce_of_memForceR` feeds that comparison to
  `uniformHorizon_antitone` (`:45-62`). The antitone theorem is the genuine
  lane-211 selection (`formalization/NSFormalization/Section4/A01/LocalTheoryBundle.lean:180-200`).
  The alternative vendor declaration is
  `EulerUniformHeatLocal.exists_uniform_restart_time`
  (`vendor/NavierStokesAndEuler/Euler/UniformHeatLocal.lean:27-40`); the
  physical specialization `forced_uniform_restart_time` only constructs a
  cylinder mild path (`formalization/NSFormalization/Section4/A01/Continuation.lean:242-263`)
  and does not compare its duration to `localHorizon'`. The report's route
  description is therefore correct.

- The H⁷-to-cylinder estimate is not a `.toReal`-at-top loophole. The proof
  uses `hK : K ≠ ⊤` in `ENNReal.toReal_mono` before obtaining the real norm
  bound (`RestartFixedForce.lean:52-62`). Although the exported `0 ≤ S`
  binder is syntactically unused (`_hS` at `:42`), it is not a hidden
  vacuity device: the intended interval is nonempty, and the checked
  zero-solution example uses the full interval `Icc 0 1`
  (`axioms_restart_fixed_force.lean:35-49`). The proof is simply stronger for
  negative `S`, where the quantified interval is empty.

- The lane supplies the missing smooth-path input for arbitrary classical
  solutions by translating the solution (`RestartFixedForce.lean:67-103`),
  bounding H⁷ on a compact interior interval (`:105-118`), choosing a carrier
  window (`:120-140`), and transferring the carrier path by velocity and datum
  uniqueness (`:142-183`). This uses only a solution strictly inside its
  existing horizon, so it does not assume an endpoint carrier or the desired
  continuation conclusion.

- The explicit lane-179 carrier bridge is honest: `localCarrier_gronwall_bound`
  consumes the same `LocalCarrier.w`, `U`, cylinder path, invariance and slice
  equality (`RestartFixedForce.lean:185-198`) and calls
  `highOrder_bddAbove_of_kbnd_Ico_full`
  (`formalization/NSFormalization/Section4/A01/GronwallEndpoint.lean:30-41`).
  The general `HigherOrderBound` proof instead uses lane 179's underlying
  `highOrder_bddAbove_of_kbnd` (`GronwallInstance.lean:60-107`) on the shorter
  solution supplied by `SolvesBelow` (`RestartFixedForce.lean:245-251`).
  `running_hTwo_integral_le` bounds every real running H² integral by the
  finite ENNReal criterion before taking `.toReal` (`:200-231`); hence no
  `⊤.toReal = 0` escape is present. Lowering from `max m 3` supplies the low
  orders (`:238-263`).

- The consumers use `RestartFixedForce` only at the same `f`, at times in
  `[0,S]`, with the H⁷ bound furnished by `HigherOrderBound` at order 7
  (`RestartFixedForce.lean:276-312`). No cross-force uniformity is used.
  The final lifespan contradiction is delegated unchanged to
  `lifespanInfiniteOfLocallyFinite_of_extendsBeyond`
  (`Continuation.lean:67-96`, `RestartFixedForce.lean:326-341`).

### Non-vacuity and negative mutation

The checked conformance file supplies actual `zeroSol` instances for both the
uniform restart window and the all-order bound
(`axioms_restart_fixed_force.lean:35-60`); `zeroSol` is a genuine
`ClassicalSolutionR` (`formalization/NSFormalization/Section4/A04/ZeroSolution.lean:87-105`).
It also exhibits a finite shifted-extension conclusion (`axioms_restart_fixed_force.lean:62-65`).

The reviewer probe
`research/A04/probes/rev215_widen_restart_interval.lean:11-39` substantively
widens the main restart-time interval from `[0,S]` to `[0,S+1]` while retaining
the original `[0,S+1]` force-control window and proof. It fails at the expected
force-window boundary:

```text
../research/A04/probes/rev215_widen_restart_interval.lean:29:48: error: Application type mismatch: The argument
  ht₀
has type
  t₀ ∈ Icc 0 (S + 1)
but is expected to have type
  t₀ ∈ Icc 0 S
in the application
  referenceForce_timeShift_norm_le f hf S t₀ ht₀
```

This is an interval mutation, not a failure produced by dropping an argument.

### Axioms and hygiene

All 16 audited declarations print exactly
`[propext, Classical.choice, Quot.sound]`; the exact output is recorded below.
The production module has no `sorry`, `admit`, `axiom`, `native_decide`, or
`maxHeartbeats`. `git diff --check` passes. Relative to integration, the only
Lean module changed by the worker is the new module itself; no existing Lean
module or contract is modified.

## 3. Gaps

There is exactly one retained input:

```lean
def ShiftedLocalExtension : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (w : ClassicalSolutionR ν a f T) (b : ℝ), b ∈ Ico (0 : ℝ) T →
    ∀ L : ℝ, ClassicalSolutionR ν (fun x => w.velocity (b, x)) (timeShift b f) L →
      ENNReal.ofReal (b + L) ≤ maximalLifespanR ν a f
```

This is exactly `RestartFixedForce.lean:268-272`. It is used once, after all
restart qualifications and horizon bounds have been discharged
(`RestartFixedForce.lean:287-296`). A whole-`formalization/NSFormalization/Section4`
search for shifted/concatenated classical solutions found no theorem with this
conclusion. The closest A02 theorem is `patch`, whose two inputs share the same
initial datum and force and whose result merely chooses the longer horizon
(`formalization/NSFormalization/Section4/A02/Patch.lean:83-114`). The A01
`gluePath` hits are cylinder mild-path gluing, not `ClassicalSolutionR` gluing.
Thus the report's “not in the tree” claim survives the required whole-tree
search.

Consequently the brief's aspirational unconditional continuation theorem is
not delivered, but the lane follows the brief's explicit satisfiability rule:
one genuinely missing fact is isolated as one named hypothesis, with no
conjunction hiding further analytic obligations. The worker report says this
clearly (`research/A04/REPORT_215.md:34-54`), so this is a recorded residual gap,
not a statement-fidelity defect.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`; Lake was run only
from `verification/` with `LEAN_NUM_THREADS=6`.

### Build and direct checks

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A04.RestartFixedForce
[exit 0]
⚠ [8777/9013] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
...
⚠ [10419/10478] Replayed NSFormalization.Section4.A01.MildGronwall
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.
...
Build completed successfully (10478 jobs).
```

The plain build replayed 241 lines of pre-existing dependency warnings; none
points to `RestartFixedForce.lean`. Exact full output is in
`tmp/rev215_build.log`. The worker's suppressed form was also reproduced:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake -q --log-level=error build NSFormalization.Section4.A04.RestartFixedForce
[exit 0; zero output]

$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A04/RestartFixedForce.lean
[exit 0; zero output]
```

The axioms/non-vacuity file produced exactly:

```text
'NSFormalization.Section4.A04.RestartFixedForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.referenceForce_timeShift_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A04.restartFixedForce_of_memForceR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.shiftedSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.compact_hSeven_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.exists_carrier_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.classical_hasSmoothSobolevPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.localCarrier_gronwall_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.running_hTwo_integral_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.higherOrderBound_of_gronwall' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.ShiftedLocalExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.restartBeyond_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.extendsBeyond_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.extendsBeyond_of_memForceR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.lifespanInfiniteOfLocallyFinite_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A04.lifespanInfiniteOfLocallyFinite_of_memForceR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Command: `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A04/axioms_restart_fixed_force.lean`; exit 0.

### Repository gates

`LEAN_NUM_THREADS=6 make check` exited 0. Its exact output is very large JSON;
the exact head and tail were:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 532,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
...
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.042s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

The complete standard gate was run as
`LEAN_NUM_THREADS=6 BASE_REF=origin/erenup/integration scripts/gates.sh NSFormalization.Section4.A04.RestartFixedForce`.
It exited 0; full exact output is `tmp/rev215_gates.log` (28,518 lines). Its exact
terminal section was:

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

Thus `scripts/gates.sh`, `make test`, mutation tests, and
`check_contracts.py --base-ref origin/erenup/integration` all pass. No file
under `verification/` was touched by this lane, but the base-ref contract check
was run anyway.

### Hygiene and tree-gap searches

```text
$ git diff --name-status origin/erenup/integration...HEAD
A formalization/NSFormalization/Section4/A04/RestartFixedForce.lean
A research/A04/ATTEMPTS_RESTART_FIXED_FORCE.md
M research/A04/COMPARISON.md
A research/A04/REPORT_215.md
A research/A04/axioms_restart_fixed_force.lean

$ grep -nE '\b(sorry|admit|axiom|native_decide|maxHeartbeats)\b' formalization/NSFormalization/Section4/A04/RestartFixedForce.lean
[exit 1; zero output]

$ git diff --check origin/erenup/integration...HEAD
[exit 0; zero output]
```

The required whole-tree gap grep returned only the new declaration and comments
about the same missing classical gluing, A02's same-origin `patch`, A01 cylinder
`gluePath` results, and unrelated uses of “glue”; it returned no producer of
`ShiftedLocalExtension`. The relevant exact hits are listed in Part 3 with
their source lines.

No fixes required.
