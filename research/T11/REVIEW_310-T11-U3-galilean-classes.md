ACCEPT

## 1. What the lane claims

The worker report claims three public theorems, with displayed signatures:
`translation_preserves_sobolev` (`research/T11/REPORT_310.md:5`),
`transformed_classes` (`research/T11/REPORT_310.md:12`), and
`transformed_mean_zero` (`research/T11/REPORT_310.md:21`).  It also claims one
explicitly named measure-invariance instance and supporting results
(`research/T11/REPORT_310.md:33`), exact target-shape checks plus a nonzero
stationary solution (`research/T11/REPORT_310.md:40`), exact standard axioms
(`research/T11/REPORT_310.md:45`), and no residual proof gap or named input
(`research/T11/REPORT_310.md:51`).

These are exactly the three U3 obligations in the binding split
(`research/T11/T11_SPLIT.md:55`) and the three corresponding fields of the
canonical API (`research/T11/probes/api_on_canonical.lean:174`, `:180`, and
`:189`).  The intended mathematics is the manuscript's data-defined
Galilean reduction: `m`, `X`, transformed velocity and force are defined at
`paper/sections/appendix-a-local-theory.tex:89-100`; the cancellation is
explained at `:101-102`; and translation invariance of every Sobolev norm is
stated at `:103`.  The independent Section 3 argument likewise says that
integrating the equation kills convection, Laplacian, and pressure and yields
`m' = g-bar` (`paper/sections/03-torus.tex:395-410`).

## 2. What is in Lean

All claimed declarations exist and have the claimed statements.

- `translation_preserves_sobolev` is at
  `formalization/NSFormalization/Section3/T11/GalileanClasses.lean:210-213`,
  textually matching the API at
  `research/T11/probes/api_on_canonical.lean:189-192`.  The proof obtains the
  translated Fourier datum with the unimodular phase at `:94-194`, preserves
  its norm at `:142-173`, and applies the one-sided inequality again at `-y`
  at `:196-221`.  Thus the empty-datum case is genuinely handled: there is no
  `.toReal` use and no reliance on `top.toReal = 0`.  This matches the datum
  definition and empty-infimum convention at
  `formalization/NSFormalization/Section3/T10/PeriodicData.lean:104-120` and
  uses the quotient evaluation bridge at
  `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:38-44`.
- `transformed_classes` is at
  `formalization/NSFormalization/Section3/T11/GalileanClasses.lean:323-328`,
  exactly matching `research/T11/probes/api_on_canonical.lean:174-179`.
  Global, rather than slab-only, smoothness of the force mean and both
  primitives is proved at `GalileanClasses.lean:225-307`; the cited scalar
  result really is the all-order half-open cube-integral theorem at
  `formalization/NSFormalization/Paper1/PeriodicPressureNormalization.lean:90-128`.
  Initial smoothness/periodicity/solenoidality and force smoothness/periodicity
  are assembled at `GalileanClasses.lean:329-349`; the original compact set
  and its positive-time inclusion are reused, and time support is proved at
  `:350-361`.  These are precisely the fields of `initialClassT` and
  `forceClassT` at `PeriodicData.lean:232-245`.
- `transformed_mean_zero` is at
  `formalization/NSFormalization/Section3/T11/GalileanClasses.lean:575-583`,
  exactly matching `research/T11/probes/api_on_canonical.lean:180-188`.
  The Lean proof integrates the PDE componentwise: the Laplacian, pressure,
  and advection means vanish at `GalileanClasses.lean:371-437`; differentiation
  of the velocity mean and use of the momentum equation occur at `:439-514`;
  the initial value and FTC identify it with the prescribed mean at `:516-546`;
  and translation/subtraction then proves all three zero means at `:548-622`.
  This is the mathematics of the cited manuscript lines, not merely a
  definitional zero.

The closure probe reuses each theorem at the full target type, without extra
hypotheses (`research/T11/probes/galilean_classes_closes.lean:18-41`).  Its
non-vacuity example constructs a `ClassicalSolutionT 1 a f 1` with nonzero
constant velocity and an admissible compactly supported zero force
(`:43-98`).  In particular the time intervals are not empty.  Although
`nu`, its positivity proof, `T`, and the solution are not needed by the proof
of `transformed_classes` (`GalileanClasses.lean:329`), they were not silently
added: they occur verbatim in the canonical API, and the proof establishes the
class conclusion without using them.  `ClassicalSolutionT` itself enforces
`0 < T` (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:265-274`).
There is no named input hypothesis.

Hygiene is clean.  The sole instance is explicitly named
`galileanPeriodicTorusMeasure_isAddRightInvariant`
(`GalileanClasses.lean:28-32`).  There is no heartbeat override and no
executable `sorry`, `admit`, `axiom`, or `native_decide`.  Against
`origin/erenup/integration-section3`, all three changed Lean files are new;
the only pre-existing changed file is the brief-required one-line status
addition to `research/T11/T11_SPLIT.md`.  `verification/` is untouched.
The guarded audit covers the instance and all three theorems
(`research/T11/axioms_galilean_classes.lean:7-23`), and the unguarded reviewer
audit at `research/T11/probes/rev310_axioms.lean:5-8` confirms each exact axiom
set.

## 3. Gaps

No proof, fidelity, satisfiability, citation, or hygiene gap was found, and no
fix is required.

The report makes no "not in the tree" or missing-lemma claim, so there is no
declared gap to validate.  As an additional check, the required whole-tree
command

```text
grep -rn -E 'Galilean|galilean|translation_preserves_sobolev|transformed_classes|transformed_mean_zero' formalization/NSFormalization/Section4
```

had exactly no output.  This is consistent with, but not needed to justify,
the worker's no-gap claim.

The substantive negative probe changes the first conclusion of
`transformed_mean_zero` from zero to the nonzero `coordinateVector 0`
(`research/T11/probes/rev310_mutation.lean:13-24`).  This changes a mathematical
constant rather than dropping an argument.  Direct proof reuse fails with the
expected type mismatch:

```text
../research/T11/probes/rev310_mutation.lean:24:2: error: Type mismatch
  transformed_mean_zero
has type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ a ∈ initialClassT,
        ∀ f ∈ forceClassT,
          ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
            meanT (meanZeroPartT a) = 0 ∧
              (∀ t ∈ Ico 0 T, (meanT fun x => galileanVelocityT a f w.velocity (t, x)) = 0) ∧
                ∀ t ∈ Ico 0 T, (meanT fun x => galileanForceT a f (t, x)) = 0
but is expected to have type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ a ∈ initialClassT,
        ∀ f ∈ forceClassT,
          ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
            meanT (meanZeroPartT a) = coordinateVector 0 ∧
              (∀ t ∈ Ico 0 T, (meanT fun x => galileanVelocityT a f w.velocity (t, x)) = 0) ∧
                ∀ t ∈ Ico 0 T, (meanT fun x => galileanForceT a f (t, x)) = 0
```

## 4. Commands and results

Environment for every Lean command: `. scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`; all direct `lake` commands ran from `verification/`.

1. `lake build NSFormalization.Section3.T11.GalileanClasses` — exit 0.  The
   exact final output was:

   ```text
   Build completed successfully (9929 jobs).
   ```

   Lake also replayed pre-existing warnings from
   `Source/FiniteHilbertBochner.lean`, `Source/RealSobolev.lean`,
   `Paper3/SpatiallyCompactTime.lean`, `Paper3/RealPositiveDensity.lean`,
   `Paper3/RealVectorPositiveDensity.lean`, `Source/PacketForceExtension.lean`,
   `Source/ViscosityPacket.lean`, `Source/PhysicalBesselSobolev.lean`, and
   `Paper3/SobolevDirectionalDerivative.lean`.  There was no diagnostic from
   `GalileanClasses.lean`; the direct module check below was silent.

2. These commands all exited 0 with exactly no output:

   ```text
   lake env lean ../formalization/NSFormalization/Section3/T11/GalileanClasses.lean
   lake env lean ../research/T11/probes/galilean_classes_closes.lean
   lake env lean ../research/T11/axioms_galilean_classes.lean
   lake env lean ../research/T11/probes/api_on_canonical.lean
   ```

3. `lake env lean ../research/T11/probes/rev310_axioms.lean` — exit 0, exact
   output:

   ```text
   'NSFormalization.Section3.T11.galileanPeriodicTorusMeasure_isAddRightInvariant' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T11.translation_preserves_sobolev' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.transformed_classes' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.transformed_mean_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. `make check` — exit 0.  The full JSON closure listing is intentionally not
   duplicated; its exact terminal output was:

   ```text
     },
     "base_compatibility_checked": false,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.046s

   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

5. `BASE_REF=origin/erenup/integration-section3 scripts/gates.sh
   NSFormalization.Section3.T11.GalileanClasses` — exit 0.  It reran
   `make check`, the module build, all registered contract tests, and the
   mutation suite.  Exact decisive tail:

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

6. Although no `verification/` file changed, the conditional contract command
   was also run directly:

   ```text
   python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
   ```

   It exited 0; exact tail:

   ```text
       ]
     },
     "base_compatibility_checked": true,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   ```

7. The forbidden-token scan, heartbeat scan, and `git diff --check
   origin/erenup/integration-section3...HEAD` all exited 0 with exactly no
   output.  The exact changed-path audit was:

   ```text
   A formalization/NSFormalization/Section3/T11/GalileanClasses.lean
   A research/T11/ATTEMPTS_GALILEAN_CLASSES.md
   A research/T11/REPORT_310.md
   M research/T11/T11_SPLIT.md
   A research/T11/axioms_galilean_classes.lean
   A research/T11/probes/galilean_classes_closes.lean
   ```

8. `lake env lean ../research/T11/probes/rev310_mutation.lean` exited 1 with
   the expected error reproduced in part 3.  This expected failure is the
   negative gate, not a deliverable build failure.
