REJECT

## 1. What the lane claims

The worker is candid that this is a partial delivery.  The report claims an
unconditional H³ Fourier inverse, exact recovery of its datum, initial-value and
continuity results for the recovered velocity, reweight transport, a nonzero
coefficient-solver instance, and a full affine-constant classical solution
(`REPORT_318.md:3-57`).  It explicitly says that neither the general U9d target
nor the requested complete `(ii)+(iii)` fallback was proved
(`REPORT_318.md:77-98`).

The latter admission is blocking, not merely a note.  The binding target is the
quantified theorem at `EXISTENCE_ROUTE.md:253-266`; it requires recovery for
every positive viscosity, contract, smooth periodic datum/force, Leray-projected
force path, and forced mild path, on the same positive horizon.  The brief
allowed exactly one satisfiable named analytic input if necessary and, at a
minimum, required full physical velocity and pressure/PDE recovery from an
all-order input.  The peeling rule requires such an input to be isolated and
the remaining target proved (`T11_SPLIT.md:14-23`).  The lane instead introduces
no named input and leaves bootstrap, divergence, pressure, and the PDE all open
(`EXISTENCE_ROUTE.md:277-301`).

This matters mathematically.  The paper requires one common interval for all
Sobolev orders (`paper/sections/02-preliminaries.tex:105-120`) and explains that
the projected equation first supplies all spatial/time regularity before the
pressure formulas restore the gradient force (`paper/sections/appendix-a-local-theory.tex:62-77`).
The pressure and projected equations themselves are
`paper/sections/02-preliminaries.tex:80-88`.  An isolated spatially homogeneous
solution cannot establish those assertions for a general mild coefficient
path.

## 2. What is actually in Lean

The report's displayed theorem signatures do exist exactly as stated:

- `torusPhysicalField_eq` is at `PhysicalRecovery.lean:133-149`.
- `torusPhysicalVelocity_initial` is at `PhysicalRecovery.lean:151-158`.
- `torusPhysicalField_datum` is at `PhysicalRecovery.lean:234-257`.
- `torusPhysicalVelocity_datum` is at `PhysicalRecovery.lean:259-262`.
- `torusForcedMildOn_physical_continuous` is at
  `PhysicalRecovery.lean:382-387`.
- `torusPhysicalField_datum_reweight` is at
  `PhysicalRecovery.lean:399-403`.
- `torusForcedMildOn_affine_constant` is at
  `PhysicalRecovery.lean:489-528`.
- `torusPhysicalRecovery_affine_constant` is at
  `PhysicalRecovery.lean:530-549`.

The supporting claims are also real: absolute summability and continuity are
proved at `PhysicalRecovery.lean:44-109`, periodicity at `:114-131`, reality and
coefficient inversion at `:165-257`, the continuous inverse map and joint
continuity at `:264-387`, and conditional time smoothness at `:412-424`.
The use of `periodic_component_eq_tsum` is faithful to its actual continuous,
summable inversion statement (`Section3/T10/FourierCalculus.lean:164-172`).
The pressure citations are also honest: the coefficient Poisson inverse only
solves zero-mode-compatible coefficient data
(`Paper1/PeriodicPressureSymbolOperator.lean:35-41`), while the recovery bridge
explicitly assumes an already supplied smooth flow/pressure
(`Paper1/PeriodicPressureRecoveryBridge.lean:4-10,27-49`).

The delivered lemmas do not silently exploit `⊤.toReal = 0`, an empty interval,
or an impossible named hypothesis.  The only `.toReal` uses are the finite
exponent `2` and `ENNReal.one` (`PhysicalRecovery.lean:65,218,287-291`).  The
general mild continuity statement inherits `0 ≤ T` from
`TorusForcedMildOn.time_nonneg` (`LocalExistenceProbe.lean:246-258`), while the
full affine classical recovery assumes `0 < T` (`PhysicalRecovery.lean:531`).
Its three regularity fields are genuinely filled using the homogeneous
solution theorem (`PhysicalRecovery.lean:536-549` and
`LocalExistenceProbe.lean:313-371`).

Non-vacuity was independently checked in
`probes/rev318_nonvacuity.lean:10-24`: the contract exists, `T > 0`, the force
datum `torusConstantDatum 3 (coordinateVector 0)` is nonzero, and both recovered
velocity expressions are nonzero.  The probe compiles with no output.

Nevertheless, the only full `ClassicalSolutionT + PeriodicLocalRegularity`
result in the module is the affine-constant special case at
`PhysicalRecovery.lean:530-549`.  The module itself says no general recovery is
asserted (`PhysicalRecovery.lean:10-13`), and the supplied conformance probe says
the exact target remains open (`probes/physical_recovery_closes.lean:3-20`).
There is no theorem in this module with the target at
`EXISTENCE_ROUTE.md:253-266`.

Hygiene is otherwise good.  Against
`origin/erenup/integration-section3...HEAD`, the only formalization change is
the new `PhysicalRecovery.lean`; no existing Lean module or `verification/`
file was modified.  The two local instances are explicitly named
(`PhysicalRecovery.lean:23-26`).  The new lane Lean files contain no code use of
`sorry`, `admit`, `axiom`, or `native_decide`, and no `maxHeartbeats` override.
There are 40 `def`/`theorem` declarations plus the two named instances, and the
axiom audit contains 42 guarded `#print axioms` commands
(`axioms_physical_recovery.lean:5-171`).  Its zero-output successful run proves
that every guard matched exactly
`[propext, Classical.choice, Quot.sound]`.

## 3. Gaps and rejection reason

The blocking finding is statement fidelity:

1. The exact general U9d theorem is absent.  This omits the requested all-order
   common-horizon bootstrap, general smooth and divergence-free physical
   velocity, normalized pressure and Poisson equation, Duhamel time
   differentiation, momentum/projected equations, and assembly into
   `ClassicalSolutionT` with `PeriodicLocalRegularity`.
2. The brief's fallback is also absent.  No single all-order named input is
   defined and no theorem recovers general physical velocity and pressure/PDE
   fields from such an input.  This violates the peeling rule rather than
   satisfying it conditionally.
3. The affine constant family is a useful satisfiability test but cannot replace
   a theorem universally quantified over `a`, `g`, `A`, `F`, `P`, and `u`.

The worker's "not yet in the tree" assessment was checked with a whole-tree
search:

```text
grep -rnE 'TorusForcedMildOn|torusPhysicalVelocity|physical.*recover|recover.*physical|all.order|allOrder|Duhamel.*(deriv|differ)|deriv.*Duhamel|pressure.*recover|recover.*pressure|IsPeriodicLerayDatum|PeriodicLocalRegularity' formalization/NSFormalization/Section4
```

The closest Section 4 results do not close the torus target.  In particular,
`A01/JointRepresentative.lean:552-590` requires supplied all-order paths or an
all-order cylinder family; `A01/ManuscriptRegularity.lean:176-181` obtains
pressure recovery from an already existing `ClassicalSolutionR`;
`A01/DatumPathDeriv.lean:344-360` differentiates a different cylinder Duhamel
path under finite-order cylinder hypotheses; and
`A01/ConstructorDivergenceSlice.lean:49-71` proves an a.e. divergence statement
from supplied cylinder/representative data.  None is a theorem over
`TorusForcedMildOn`, `PeriodicSobolev`, or the U9d binders.  Thus the stated gaps
are real, although Section 4 contains analogous machinery that may be adapted.

The required substantive negative test is
`probes/rev318_negative_sign.lean:9-16`.  It flips the main affine trajectory
from `(1+t)c` to `(1-t)c` without dropping an argument.  Lean rejects it for the
expected sign mismatch:

```text
../research/T11/probes/rev318_negative_sign.lean:16:2: error: Type mismatch
  torusForcedMildOn_affine_constant C c hT
has type
  TorusForcedMildOn C (torusConstantDatum 3 c) (fun x => torusConstantDatum 3 c) T fun t =>
    (1 + t) • torusConstantDatum 3 c
but is expected to have type
  TorusForcedMildOn C (torusConstantDatum 3 c) (fun x => torusConstantDatum 3 c) T fun t =>
    (1 - t) • torusConstantDatum 3 c
```

Exit status was 1, as required.  This validates the special affine theorem's
sign; it does not repair the missing general target.

Required fix: either prove the exact target at `EXISTENCE_ROUTE.md:253-266`, or
follow the authorized fallback by defining exactly one satisfiable, non-tautological
all-order input and proving all of physical velocity recovery, divergence,
pressure/gauge/Poisson recovery, Duhamel differentiation, the classical
momentum/projected equations, and the final same-horizon conclusion from it.
The conformance probe must then close that general theorem, not merely state in
a comment that it is open.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, with
`LEAN_NUM_THREADS=6`; all `lake` commands were run from `verification/` and one
at a time.

1. Module build:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.PhysicalRecovery
⚠ [8778/9353] Replayed NSFormalization.Source.FiniteHilbertBochner
...
⚠ [9970/9977] Replayed NSFormalization.Paper1.PeriodicLocalLifespan
Build completed successfully (9977 jobs).
```

Exit 0.  The omitted middle consists only of replayed dependency warnings; no
warning names `PhysicalRecovery.lean`.  This is the exact beginning/end form
used because the repository review instructions cap pasted raw gate output.

2. Direct module, worker probe, and exact axiom audit:

```text
$ lake env lean ../formalization/NSFormalization/Section3/T11/PhysicalRecovery.lean
<no output>
$ lake env lean ../research/T11/probes/physical_recovery_closes.lean
<no output>
$ lake env lean ../research/T11/axioms_physical_recovery.lean
<no output>
```

Each exited 0.  In particular the module satisfies the requested zero-output
direct check, and all 42 exact axiom guards passed.

3. Reviewer non-vacuity probe:

```text
$ lake env lean ../research/T11/probes/rev318_nonvacuity.lean
<no output>
```

Exit 0.

4. Reviewer negative mutation:

```text
$ lake env lean ../research/T11/probes/rev318_negative_sign.lean
../research/T11/probes/rev318_negative_sign.lean:16:2: error: Type mismatch
  torusForcedMildOn_affine_constant C c hT
has type
  TorusForcedMildOn C (torusConstantDatum 3 c) (fun x => torusConstantDatum 3 c) T fun t =>
    (1 + t) • torusConstantDatum 3 c
but is expected to have type
  TorusForcedMildOn C (torusConstantDatum 3 c) (fun x => torusConstantDatum 3 c) T fun t =>
    (1 - t) • torusConstantDatum 3 c
```

Exit 1, expected.

5. Root gate:

```text
$ LEAN_NUM_THREADS=6 make check
python3 experiments/check_formalization_plan.py --check
...
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

Exit 0.  `check_formalization_plan.py` reported 45 tasks, no missing copied
imports, and a clean tracked cache; `check_contracts.py` reported 38 registered
contracts.  The very large generated closure lists are omitted.

6. Full wrapper, run even though `verification/` was not touched:

```text
$ BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 \
    scripts/gates.sh NSFormalization.Section3.T11.PhysicalRecovery
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

Exit 0.  The wrapper also reran `make check`, the module build, and `make test`;
all 38 displayed contract checks said "standard logical axioms only".

7. Explicit requested base-ref contract check:

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3 | tail -n 4
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

Exit 0.  It was conditional on touching `verification/`; the lane did not touch
that directory, but the check was run anyway.

8. Diff and hygiene:

```text
$ git diff --name-status origin/erenup/integration-section3...HEAD
A formalization/NSFormalization/Section3/T11/PhysicalRecovery.lean
A research/T11/ATTEMPTS_PHYSICAL_RECOVERY.md
M research/T11/EXISTENCE_ROUTE.md
A research/T11/REPORT_318.md
M research/T11/T11_SPLIT.md
A research/T11/axioms_physical_recovery.lean
A research/T11/probes/physical_recovery_closes.lean
$ git diff --check origin/erenup/integration-section3...HEAD
<no output; exit 0>
```

The only additional working-tree files are the two permitted reviewer probes
and this required review report.  No git state-changing command was run.
