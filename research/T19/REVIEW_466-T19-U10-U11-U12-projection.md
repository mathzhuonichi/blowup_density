ACCEPT

## 1. What the lane claims

The worker reports three closed theorems: fixed-fibre density in the extended
breakdown set, projection of that set onto all admissible initial data, and
projection of its zero-initial-data subfamily onto the singleton zero
(`research/T19/REPORT_466.md:5`, `research/T19/REPORT_466.md:18`,
`research/T19/REPORT_466.md:25`). It also claims exact conformance probes,
standard logical axioms only, no residual gaps or named inputs, and all listed
gates passing (`research/T19/REPORT_466.md:35`,
`research/T19/REPORT_466.md:44`, `research/T19/REPORT_466.md:51`,
`research/T19/REPORT_466.md:64`).

These claims are accurate.

## 2. What is in Lean

### Statement fidelity

The implementation signatures at
`formalization/NSFormalization/Section3/T19/Projection.lean:22`,
`formalization/NSFormalization/Section3/T19/Projection.lean:37`, and
`formalization/NSFormalization/Section3/T19/Projection.lean:57` are exactly the
three canonical `ProjectionAPI` field types at
`formalization/NSFormalization/Section3/T19/Density.lean:222`,
`formalization/NSFormalization/Section3/T19/Density.lean:234`, and
`formalization/NSFormalization/Section3/T19/Density.lean:240`. The worker's
three `exact` checks independently elaborate those same types at
`research/T19/probes/projection_closes.lean:10`,
`research/T19/probes/projection_closes.lean:21`, and
`research/T19/probes/projection_closes.lean:26`.

The mathematics matches the source. The paper defines
`B_{nu,T} = {(a,f) in X x F : T_max^nu(a,f) <= T}` at
`paper/sections/03-torus.tex:564`-`paper/sections/03-torus.tex:569`, asserts
product density and full projection at `paper/sections/03-torus.tex:570`, and
the zero-initial singleton projection at `paper/sections/03-torus.tex:571`.
Its proof explicitly keeps `a` fixed and changes only the force
(`paper/sections/03-torus.tex:573`-`paper/sections/03-torus.tex:576`), with the
important `forall a, exists f` order stated at
`paper/sections/03-torus.tex:579`-`paper/sections/03-torus.tex:580`. Lean's
`extendedBreakdownSetT` contains exactly initial-class membership, force-class
membership, and the `<= ENNReal.ofReal T` lifespan bound
(`formalization/NSFormalization/Section3/T19/Density.lean:49`-
`formalization/NSFormalization/Section3/T19/Density.lean:53`).

U10 is the requested definitional repackaging: it applies
`fixedInitialDensity` and puts its force membership and lifespan bound together
with `a in initialClassT`
(`formalization/NSFormalization/Section3/T19/Projection.lean:31`-
`formalization/NSFormalization/Section3/T19/Projection.lean:34`). The source
theorem has the correct strict radius guard and subcritical range
(`formalization/NSFormalization/Section3/T19/DensityEngine.lean:24`-
`formalization/NSFormalization/Section3/T19/DensityEngine.lean:46`), while
`RelativelyDenseT` itself quantifies over a genuine positive radius and returns
a member of the target set
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:322`-
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:325`). There is no
`top.toReal = 0`, empty interval, or unused statement binder.

U11 proves both inclusions. The forward inclusion extracts the initial-class
component (`formalization/NSFormalization/Section3/T19/Projection.lean:41`-
`formalization/NSFormalization/Section3/T19/Projection.lean:44`); the reverse
inclusion constructs the zero force and invokes U10 with the honest choices
`s = 0`, `r = 1`
(`formalization/NSFormalization/Section3/T19/Projection.lean:45`-
`formalization/NSFormalization/Section3/T19/Projection.lean:54`). The empty set
there is only the compact support witness for the identically zero force, not
an empty quantified interval: the canonical force class permits compact time
support contained in positive time
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:237`-
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:245`).

U12's forward inclusion uses the imposed first-coordinate equality, and its
reverse inclusion directly proves that zero is smooth, periodic, and
solenoidal before again applying U10
(`formalization/NSFormalization/Section3/T19/Projection.lean:63`-
`formalization/NSFormalization/Section3/T19/Projection.lean:85`). This agrees
with the canonical initial-class definition
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:232`-
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:235`). A concrete
reviewer instance at `nu = T = r = 1`, `s = 0`, and zero input data proves that
the produced fibre is nonempty
(`research/T19/probes/rev466_nonvacuity.lean:11`-
`research/T19/probes/rev466_nonvacuity.lean:31`); it typechecks with no output.

The cited proof templates are also honest: the periodic insertion fibre
returns force membership, strict force distance, and exact lifespan
(`formalization/NSFormalization/Paper1/PeriodicDensityFiber.lean:116`-
`formalization/NSFormalization/Paper1/PeriodicDensityFiber.lean:127`), while
the zero and arbitrary fixed slices retain the lifespan upper bound and strict
distance (`formalization/NSFormalization/Paper1/PeriodicDense.lean:60`-
`formalization/NSFormalization/Paper1/PeriodicDense.lean:81`). The cited R3
zero-initial analogue really is at
`formalization/NSFormalization/Section4/A04/ZeroSolution.lean:80`-
`formalization/NSFormalization/Section4/A04/ZeroSolution.lean:83` and is used by
`verification/Bindings/DensityFromInsertion.lean:53`-
`verification/Bindings/DensityFromInsertion.lean:58`.

### Axioms, hygiene, and diff scope

The axiom audit file names exactly the three delivered declarations
(`research/T19/axioms_u10_u12.lean:3`-
`research/T19/axioms_u10_u12.lean:5`), and every declaration prints exactly
`[propext, Classical.choice, Quot.sound]`.

There is no `sorry`, `admit`, `axiom`, or `native_decide` token and no
`set_option maxHeartbeats` in the implementation, conformance probe, or axiom
audit. `git diff --check origin/erenup/integration-section3...HEAD` exits 0.
The base comparison warns that the branch has multiple merge bases (expected
because lane 466 was based on lane 464), then lists:

```text
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 072ed4dd2bd3918832cbd51cb7ab080ad0e4781c
formalization/NSFormalization/Section3/T19/DensityEngine.lean
formalization/NSFormalization/Section3/T19/Projection.lean
research/T19/ATTEMPTS_U10_U12.md
research/T19/ATTEMPTS_U7_U9.md
research/T19/REPORT_464.md
research/T19/REPORT_466.md
research/T19/T19_SPLIT.md
research/T19/axioms_u10_u12.lean
research/T19/axioms_u7_u9.lean
research/T19/probes/density_engine_closes.lean
research/T19/probes/projection_closes.lean
```

Both Lean modules in that branch-level list are newly added; lane 466's own
commit adds only `Projection.lean` as Lean implementation code. The sole
modified pre-existing tracked file in lane 466 is the explicitly requested
research status ledger `T19_SPLIT.md`; no existing Lean module or verification
file was modified. The uncommitted modification to
`collaboration/briefs/466-T19-U10-U11-U12-projection.md` predates this review
and was left untouched.

## 3. Gaps and negative check

There is no theorem gap. The worker report expressly declares none
(`research/T19/REPORT_466.md:51`-`research/T19/REPORT_466.md:62`), and neither
the report nor the attempt log claims that a required lemma is absent from the
tree. Therefore the requested Section4 whole-tree grep for each declared
"not in the tree" gap has an empty set of claims to check.

The substantive negative mutation widens the main density range from
`s < 1/2` to `s < 3/4`
(`research/T19/probes/rev466_negative.lean:10`-
`research/T19/probes/rev466_negative.lean:22`). It fails at the density-engine
call, rather than from a dropped argument, with the expected exact diagnostic:

```text
../research/T19/probes/rev466_negative.lean:22:41: error: Application type mismatch: The argument
  hs
has type
  s < 3 / 4
but is expected to have type
  s < 1 / 2
in the application
  fixedInitialDensity a ha ν hν T hT s hs
```

This confirms that the critical constant in the delivered proof is
load-bearing. The positive reviewer probe described in Part 2 separately
confirms non-vacuity.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, only from
`verification/`, with `LEAN_NUM_THREADS=6`.

1. `lake build NSFormalization.Section3.T19.DensityEngine` — exit 0. Lake
   replayed pre-existing imported-module warnings; no warning names the target.
   Exact terminating output:

   ```text
   Build completed successfully (10658 jobs).
   ```

2. `lake build NSFormalization.Section3.T19.Projection` — exit 0. Lake replayed
   the same pre-existing imported-module warnings; no warning names
   `Projection.lean`. Exact terminating output:

   ```text
   Build completed successfully (10659 jobs).
   ```

3. `lake env lean ../formalization/NSFormalization/Section3/T19/Projection.lean`
   — exit 0, exact output: empty.

4. `lake env lean ../research/T19/probes/projection_closes.lean` — exit 0,
   exact output: empty.

5. `lake env lean ../research/T19/probes/rev466_nonvacuity.lean` — exit 0,
   exact output: empty.

6. `lake env lean ../research/T19/probes/rev466_negative.lean` — exit 1 with
   exactly the expected diagnostic pasted in Part 3.

7. `lake env lean ../research/T19/axioms_u10_u12.lean` — exit 0, exact output:

   ```text
   'NSFormalization.Section3.T19.extendedProductDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.projectionOntoInitialData' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T19.zeroInitialProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

8. `make check` — exit 0. It ran the four Makefile checks at `Makefile:3`-
   `Makefile:7`. Exact final output:

   ```text
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.044s

   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

   The preceding architecture JSON also reported
   `"missing_copied_imports": []` and contract-policy checking completed before
   the 13 tests. The known copied-source scan reports the repository's isolated
   `Paper1/BoundaryCorollary.lean:90` token; it is not imported by this lane and
   does not make the check fail.

9. Hygiene commands:

   ```text
   rg -n --glob '*.lean' '\b(sorry|admit|axiom|native_decide)\b' formalization/NSFormalization/Section3/T19/Projection.lean research/T19/probes/projection_closes.lean research/T19/axioms_u10_u12.lean
   # no output
   rg -n 'set_option[[:space:]]+maxHeartbeats' formalization/NSFormalization/Section3/T19/Projection.lean research/T19/probes/projection_closes.lean research/T19/axioms_u10_u12.lean
   # no output
   git diff --name-only origin/erenup/integration-section3...HEAD -- verification
   # no output
   ```

   Since the last command is empty, the brief's conditional
   `scripts/gates.sh` and `check_contracts.py --base-ref
   origin/erenup/integration-section3` gates do not apply.

No fixes required.
