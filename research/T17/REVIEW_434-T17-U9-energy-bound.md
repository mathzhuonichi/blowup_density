ACCEPT-WITH-NOTES

## what the lane claims

`research/T17/REPORT_434.md:9-54` claims all five U9 outputs at the concrete
`correctionData`: the two torus `MemLp` fields, an explicit nonnegative energy
constant, and the `energyENormT` bound with exponent `3/2`.  The target record
fields are `formalization/NSFormalization/Section3/T17/Correction.lean:220-241`
and the reconciled Spec is `research/T17/Spec.lean:899-920`.  The paper's
corresponding estimate is exactly `paper/sections/03-torus.tex:232-242`, while
the definition of `E_T` is `paper/sections/01-introduction.tex:141-150`.

Statement fidelity passes for the Lean declarations.  The slice and gradient
theorems are at `formalization/NSFormalization/Section3/T17/Energy.lean:224-252`
and have the canonical conclusions verbatim.  The reviewer-visible exact
restatements are closed by `exact` in
`research/T17/probes/energy_closes.lean:42-74`; the record projections at
`:78-116` typecheck against the actual `CorrectionAPI` fields.  The energy
bound has the expected `Ioc (0) ε₀` quantifier, torus energy norm, and
`ENNReal.ofReal (energyConst * ε ^ ((3 : ℝ) / 2))` conclusion at
`Energy.lean:285-294`, matching `Correction.lean:239-241`.

The constant is explicit at `Energy.lean:261-269`, namely the sum of square
roots of the two chosen `ε³` constants.  The source existentials have exactly
those hypotheses and rates at `Paper1/CorrectionEnergy.lean:54-71` and
`Paper1/InsertionEnergy.lean:175-181`; the registered binding chooses the same
two constants and assigns `Real.sqrt Ae + Real.sqrt De` at
`verification/Bindings/Correction.lean:300-303,349`.  Nonnegativity is the
direct square-root proof at `Energy.lean:273-277`.  The energy proof actually
uses the single-copy Haar bridges at `Energy.lean:158-205`, then
`I02.energyEssSup_le`, `I02.energyGradient_le`, and `sqrt_mul_cube` at
`:316-352`; their exact assumptions and conclusions are
`Section4/I02/Energy.lean:103-114`, `:140-158`, and `:160-167`.

The extra `hv : ContDiff ℝ ∞ v` is the documented G1 issue
(`research/T17/SPEC_ISSUES.md:3`), and the support placement premise is honest:
`hcube_of_placement` composes `CorrectionAPI.ball_in_chart` with
`PlacementData.chartBall_in_cube` at
`research/T17/probes/energy_closes.lean:123-129` (the source fields are
`Section3/T17/Correction.lean:87-100` and `Section3/T15/Scaling.lean:128-134`).
The non-vacuity witness has positive threshold and a cube-interior centre at
`energy_closes.lean:164-230`, with the geometric proof at `:171-182`.

## what is in Lean

The new production module is
`formalization/NSFormalization/Section3/T17/Energy.lean` (354 lines).  Its
supporting declarations are `measurable_torusChart`,
`memLp_torusLift_of_continuous`, `correction_slice_eq`, the two slice-support
lemmas, the two eLpNorm bridges, and `correction_contDiff` at
`Energy.lean:98-219`; none is a placeholder.  The worker probe, axioms file,
attempt log, split status, and lesson are present at the paths named in
`research/T17/REPORT_434.md:58-66`.

`git diff --name-status origin/erenup/integration-section3...HEAD` lists only
the new `Energy.lean`, lane records/probe, and report files; under
`formalization/NSFormalization/Section3/T17` the only entry is the added
`Energy.lean`.  No existing Lean module is modified.  A reviewer-only probe
was added at `research/T17/probes/rev434_energy_mutation.lean`, as permitted by
the review instructions.

The axiom audit covers all 13 module declarations in
`research/T17/axioms_u9.lean:6-18`; every line reports exactly
`[propext, Classical.choice, Quot.sound]`.  Hygiene scans over the production
module, worker probe, axioms file, and reviewer probe found no `sorry`,
`admit`, `axiom`, `native_decide`, or `maxHeartbeats`.  `git diff --check`
also exits 0.

The report's “not in the tree” observation was checked rather than accepted
blindly: `rg -n "memLp_torusLift" formalization/NSFormalization/Section4`
has no matches, and `rg -n "memLp"
formalization/NSFormalization/Section3/T15/HaarBridge.lean` is empty.  The
nearby existing helpers are the explicitly ℂ-valued `Paper1.memLp_torusLift`
at `formalization/NSFormalization/Paper1/TorusCube.lean:54-69` and the
SpatialField-only T10 helper at `Section3/T10/ForcePaths.lean:18-22`; neither is
the generic gradient-tensor helper needed here.  The canonical U9 fields occur
only in `Section3/T17/Correction.lean:223-241` and this new module.

## gaps

There is no mathematical or Lean proof gap.  Three exact reporting/process
fixes remain:

1. `research/T17/REPORT_434.md:11-23` says the displayed “common premise
   block” is identical for the three field theorems, but the actual slice and
   gradient declarations at `Energy.lean:224-248` do **not** bind `r`, `hcube`,
   `hε₀`, or `hεspace`; those premises occur only in the energy-bound theorem
   at `:285-294`.  One-line fix: change “identical on the three field
   theorems” to “the energy-bound theorem (the two MemLp theorems omit the
   placement/rate premises)”.
2. `research/T17/REPORT_434.md:66` says no `REPORT_434.md` was written, while
   that report file is present and is the lead-transcribed report.  One-line
   fix: remove that sentence or say that the file was subsequently
   lead-transcribed.
3. The required moving-base compatibility gate is currently blocked by branch
   drift, not by this lane: `origin/erenup/integration-section3` contains the
   later stable `verification/Contracts/V1/ConservativeForcing.lean`, whereas
   this lane branches at `5baaf09b` and does not.  One-line merge fix: rebase
   or merge the current Section 3 integration base, then rerun the literal
   `scripts/gates.sh` and `check_contracts.py --base-ref
   origin/erenup/integration-section3` commands.

The G1 premise remains an assembly-level issue exactly as documented at
`SPEC_ISSUES.md:3`; it is not a residual in U9, whose theorem explicitly takes
`hv`.

The substantive negative check is independent and passes the required failure
criterion.  In `research/T17/probes/rev434_energy_mutation.lean:27-29`, only
the main rate is changed from `ε^(3/2)` to `ε^(5/2)` while all hypotheses and
the theorem application are retained.  Lean exits 1 with:

```text
error: Type mismatch
  correction_energy_bound hv x₀ T O hθ hη hθc hηc hθsupp hηsupp hcube hε₀ hεspace ε hε
has type
  energyENormT T ((correctionData v x₀ T θ η O θR ε₀).correction ε) ≤
    ENNReal.ofReal (energyConst hv x₀ T hθ hη hθc hηc * ε ^ (3 / 2))
but is expected to have type
  energyENormT T ((correctionData v x₀ T θ η O θR ε₀).correction ε) ≤
    ENNReal.ofReal (energyConst hv x₀ T hθ hη hθc hηc * ε ^ (5 / 2))
```

## commands and results

All Lean commands below were run after `. ../scripts/lean-env.sh`, with
`LEAN_NUM_THREADS=6`, and `lake` from `verification/`.

* `lake build NSFormalization.Section3.T17.Energy` exited 0.  The cold replay
  emitted unrelated dependency linter warnings (for example
  `NSFormalization/Source/FiniteHilbertBochner.lean:24:19`), then the exact
  final line was `Build completed successfully (9924 jobs).`
* `lake env lean ../formalization/NSFormalization/Section3/T17/Energy.lean`
  exited 0 with no output.
* `lake env lean ../research/T17/probes/energy_closes.lean` exited 0; its
  seven outputs all report standard axioms only.  The exact first output is
  `'NSFormalization.Section3.T17.Probe.field_correction_slice_memLp' depends on axioms: [propext, Classical.choice, Quot.sound]`;
  the remaining six have the same three-axiom list.
* `lake env lean ../research/T17/axioms_u9.lean` exited 0.  The exact output
  for every declaration is `[propext, Classical.choice, Quot.sound]` (13
  declarations; the long lines wrap after `propext,` for three declarations).
* Root `make check` exited 0.  Its exact final lines were:

  ```text
  Ran 13 tests in 0.053s

  OK
  45 work items: ownership, contract registration and task cards consistent.
  ```

* With the repository's default base (`origin/erenup/integration`),
  `LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T17.Energy`
  completed with the exact tail:

  ```text
  Mutation suite passed. This is an infrastructure check, not a PDE proof.
  == check_contracts
    "base_compatibility_checked": true,
    "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
  }
  == gates OK
  ```

* The required Section 3-base invocation was also run literally:
  `BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6
  scripts/gates.sh NSFormalization.Section3.T17.Energy`.  The build and
  mutation suite passed, but the final compatibility command exited 1 with
  this exact reproducing error:

  ```text
  == check_contracts
  Traceback (most recent call last):
    File "/data_8T/ping/blowup_density/.claude/worktrees/434-T17-U9-energy-bound/experiments/check_contracts.py", line 153, in <module>
      print(json.dumps(check(base=args.base_ref), indent=2))
    File "/data_8T/ping/blowup_density/.claude/worktrees/434-T17-U9-energy-bound/experiments/check_contracts.py", line 143, in check
      check_compatibility(root, base, contracts)
    File "/data_8T/ping/blowup_density/.claude/worktrees/434-T17-U9-energy-bound/experiments/check_contracts.py", line 62, in check_compatibility
      assert (root / path).is_file(), f'Removed stable specification: {path}'
  AssertionError: Removed stable specification: verification/Contracts/V1/ConservativeForcing.lean
  ```

  The direct required command
  `python3 experiments/check_contracts.py --base-ref
  origin/erenup/integration-section3` gives the same assertion.  The same
  check against the lane merge-base `5baaf09bede59020da78ed2622c71ab30eb1c30e`
  exits 0 (`"base_compatibility_checked": true`).
* The reviewer mutation command
  `lake env lean ../research/T17/probes/rev434_energy_mutation.lean` exits 1
  with the exponent mismatch reproduced above; this is intentional.
