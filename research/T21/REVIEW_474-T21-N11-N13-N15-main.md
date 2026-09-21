ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker reports canonical proofs of N11, the N12 transport consumed by N14,
N13, N14, and N15, together with a conditional five-field package.  Those
claims occur at `research/T21/REPORT_474.md:7-45`; the report explicitly leaves
the record-level `NonDensityAPI` adapter to the assembly lane at
`research/T21/REPORT_474.md:65-80`.

The mathematical target is correct.  The paper states fixed-initial-data
density for `s < 1/2` and the zero-datum biconditional at
`paper/sections/03-torus.tex:6-16`; its proof combines fixed-data density with
zero-data non-density at and above `1/2` at
`paper/sections/03-torus.tex:506-523`.  The reconciled Lean fields are exactly
`research/T21/Spec.lean:467-559`, and the lane split gives the same verbatim
targets at `research/T21/T21_SPLIT.md:159-229`.

Two documentation-only precision notes require one-line fixes:

1. At `research/T21/REPORT_474.md:30`, replace `le_of_not_lt` with
   `le_of_not_gt`, which is the lemma actually used at
   `formalization/NSFormalization/Section3/T21/Main.lean:76`.
2. At `research/T21/REPORT_474.md:47`, replace “lane 472 now owns” with “lane
   472 is designated to own”.  The canonical `breakdownSetTZero` declaration
   is not present in this checkout; the current module deliberately uses the
   exact local expansion at
   `formalization/NSFormalization/Section3/T21/Main.lean:23-27`.

Neither note changes a theorem statement or proof.

## 2. What is in Lean

Statement fidelity passes field by field:

- `MainTheoremAPI` has exactly the five reconciled fields and binder orders at
  `formalization/NSFormalization/Section3/T21/Main.lean:29-42`, matching
  `research/T21/Spec.lean:467-559`.
- N11 is
  `thresholdValue : T19.criticalOrder 1 = (1 : ℝ) / 2` at
  `formalization/NSFormalization/Section3/T21/Main.lean:44-46`.  It reuses the
  arithmetic theorem whose definition and proof are at
  `formalization/NSFormalization/Section3/T19/Bookkeeping.lean:29-30` and
  `formalization/NSFormalization/Section3/T19/Bookkeeping.lean:55-56`.
- The zero datum belongs to the genuine initial class at
  `formalization/NSFormalization/Section3/T21/Main.lean:48-50`, using the proved
  smooth/periodic/solenoidal instance at
  `formalization/NSFormalization/Section3/T20/CriticalEnergy.lean:402-407`.
- N13 has the required `a`-first order and no extra hypothesis at
  `formalization/NSFormalization/Section3/T21/Main.lean:52-59`.  Its source
  field is verbatim at
  `formalization/NSFormalization/Section3/T19/Density.lean:71-78`, and the
  closed canonical supplier is assembled at
  `formalization/NSFormalization/Section3/T19/Assembly.lean:17-21`.
- N14 is the exact zero-datum biconditional at
  `formalization/NSFormalization/Section3/T21/Main.lean:65-78`.  The forward
  implication converts `¬ s < 1/2` to `1/2 ≤ s` and uses the threaded
  non-density field; the reverse specializes N13 at the proved zero datum.
  This matches `research/T21/Spec.lean:523-537` and the cited order argument at
  `formalization/NSFormalization/Paper1/PeriodicMain.lean:44-53`.
- N15 is exactly the `ν,s,T` to `ν,T,s` reordering of the threaded field at
  `formalization/NSFormalization/Section3/T21/Main.lean:81-89`.  The source
  field and target are `research/T21/Spec.lean:430-431` and
  `research/T21/Spec.lean:557-559`.
- The conditional package and theorem use both hypotheses and fill all five
  fields at `formalization/NSFormalization/Section3/T21/Main.lean:91-117`.
  The worker's exact-field probe checks every field and both constructors at
  `research/T21/probes/main_closes.lean:22-48`.

There is no silent vacuity.  `initialClassT` is the smooth, periodic,
solenoidal class at
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:232-235`;
`breakdownSetT` and `RelativelyDenseT` are the genuine lifespan set and
positive-radius density predicate at
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:312-325`.
Every `ν` and `T` premise is used.  There is no `.toReal`, empty interval,
placeholder proposition, or unused named mathematical input in the delivered
declarations.

The reviewer non-vacuity probe gives the closed concrete instance
`ν = T = 1`, zero initial datum, and `s = 0` at
`research/T21/probes/rev474_nonvacuity.lean:12-19`; it typechecks with empty
output.  This is stronger evidence than merely constructing the abstract API.

Hygiene passes.  The base diff contains one new Lean module and no modified
existing Lean module:

```text
A	formalization/NSFormalization/Section3/T21/Main.lean
A	research/T21/ATTEMPTS_N11_N15.md
A	research/T21/REPORT_474.md
M	research/T21/T21_SPLIT.md
A	research/T21/axioms_n11_n15.lean
A	research/T21/probes/main_closes.lean
```

The `T21_SPLIT.md` modification is the requested status record, not a Lean
module.  `rg -n "sorry|admit|axiom|native_decide|maxHeartbeats"` over the lane
module and worker probes returned only the `#print axioms` commands in the
audit file; there is no forbidden proof token or heartbeat override.  `git
diff --check origin/erenup/integration-section3...HEAD` returned no output.
No `verification/` file was touched.

## 3. Gaps and negative checks

There is no mathematical gap in N11 or N13--N15.  The declaration named
`mainOfDensityAndNonDensity_holds` is the allowed explicit-field conditional
form, not literally a theorem of the research-only definition at
`research/T21/Spec.lean:602-604`; the final record adapter remains the assembly
unit assigned at `research/T21/T21_SPLIT.md:231-259`.  Once the parallel record
is available, the adapter is definitionally the one line already shown in the
worker report.  This is an honest and isolated integration seam, not a named
placeholder.

The report makes no claim that a missing Section 4 analytic lemma is needed.
For completeness, the required whole-tree gap search was run:

```text
$ rg -n "mainOfDensityAndNonDensity(_holds)?|breakdownSetTZero|NonDensityAPI" formalization/NSFormalization/Section4
<no output; exit 1>
```

The substantive mutation widens the main fixed-data range from `s < 1/2` to
`s < 3/4` at `research/T21/probes/rev474_mutation.lean:13-20`.  Reusing the
delivered proof fails for exactly the expected threshold mismatch:

```text
../research/T21/probes/rev474_mutation.lean:20:2: error: Type mismatch
  fixedInitialDensity periodicDensityAPI
has type
  ∀ a ∈ initialClassT,
    ∀ (nu : ℝ), 0 < nu → ∀ (T : ℝ), 0 < T → ∀ s < 1 / 2, RelativelyDenseT 1 s forceClassT (breakdownSetT nu a T)
but is expected to have type
  ∀ a ∈ initialClassT,
    ∀ (nu : ℝ), 0 < nu → ∀ (T : ℝ), 0 < T → ∀ s < 3 / 4, RelativelyDenseT 1 s forceClassT (breakdownSetT nu a T)
```

This changes the mathematical interval and does not obtain failure by dropping
an argument.

## 4. Commands and results

All Lean/Lake commands were run after sourcing `scripts/lean-env.sh`, with
`LEAN_NUM_THREADS=6`, and Lake was invoked only from `verification/`.

1. Closure build:

   ```text
   $ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.Assembly
   [existing upstream replay warnings; no T19.Assembly error]
   Build completed successfully (10661 jobs).
   ```

   Exit 0.  The replay stream contains only pre-existing upstream linter
   warnings, beginning with
   `⚠ [8778/9123] Replayed NSFormalization.Source.FiniteHilbertBochner`.

2. Required module build:

   ```text
   $ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T21.Main
   [existing upstream replay warnings; no T21/Main.lean output]
   Build completed successfully (10724 jobs).
   ```

   Exit 0.  The replay stream begins with
   `⚠ [8778/9077] Replayed NSFormalization.Source.FiniteHilbertBochner`; the
   delivered module itself is silent.

3. Direct module typecheck:

   ```text
   $ cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T21/Main.lean
   <no output>
   ```

   Exit 0.

4. Worker exact-field probe:

   ```text
   $ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T21/probes/main_closes.lean
   <no output>
   ```

   Exit 0.

5. Axiom audit:

   ```text
   'NSFormalization.Section3.T21.MainTheoremAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T21.thresholdValue' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T21.zeroInitialClass' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T21.fixedInitialDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T21.zeroInitialDensityIff' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T21.zeroInitialNonDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T21.mainTheoremAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T21.mainOfDensityAndNonDensity_holds' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   ```

   Exit 0; every declaration has exactly the required three axioms.

6. Reviewer non-vacuity probe:

   ```text
   $ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T21/probes/rev474_nonvacuity.lean
   <no output>
   ```

   Exit 0.

7. Reviewer mutation probe: exit 1 with the exact expected error pasted in
   Part 3.

8. `make check`: exit 0.  Its exact final captured output was:

   ```text
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.043s

   OK
         "NavierStokes.WeightedRadialPrimitive",
         "NavierStokes.ZerothStressIdentity",
         "TestSupport.Axioms",
         "Tests.MultipleRegions"
       ]
     },
     "base_compatibility_checked": false,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   python3 experiments/test_contract_policy.py
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

9. Full gate script:

   ```text
   $ BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T21.Main
   == make check
   [make-check JSON and the same pre-existing upstream replay warnings]
   == lake build NSFormalization.Section3.T21.Main
   Build completed successfully (10724 jobs).
   == make test
   [all listed Contracts: checked; standard logical axioms only]
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

   Exit 0.

10. The explicit requested base check was also observed with this exact tail:

    ```text
      "base_compatibility_checked": true,
      "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
    }
    ```

    Exit 0.  It was not conditionally necessary because the base diff contains
    no `verification/` path, but the full gate script ran it with the requested
    `origin/erenup/integration-section3` base anyway.

Fixes: change the two report-only phrases identified in Part 1; no Lean change
is required.
