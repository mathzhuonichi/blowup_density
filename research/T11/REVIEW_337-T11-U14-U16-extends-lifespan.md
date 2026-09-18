ACCEPT-WITH-NOTES

## What the lane claims

The worker claims that lane 337 closes the final two fields of
`PeriodicContinuationAPI`, under exactly the single named input
`PeriodicQuantitativeLocalInput'` and an explicit `hHigh` binder carrying the
`higherOrderBound` field (`research/T11/REPORT_337.md:8-34`).  It also claims a
pointwise lifespan export, maximal-existence bridge, non-vacuity witnesses,
standard transitive axioms, and successful gates (`research/T11/REPORT_337.md:36-62,80-90`).

Those are the right obligations.  The manuscript's finite-lifespan argument
really obtains finite terminal (H^2) integral and extends beyond the terminal
time (`paper/sections/03-torus.tex:490-503`).  The canonical probe fixes the
two requested fields, including the endpoint `≤` in U16, at
`research/T11/probes/api_on_canonical.lean:135-150`; the field's higher-order
input is at `:112-120`.

## What is in Lean

Statement fidelity is exact.  The target theorem
`extendsBeyond_of_input` has the same binders, `SolvesBelowT`, endpoint
criterion, and `ExtendsBeyondT` conclusion as the canonical U14 field
(`formalization/NSFormalization/Section3/T11/ExtendsBeyond.lean:101-117` versus
`research/T11/probes/api_on_canonical.lean:135-141`).  Its `hHigh` binder is the
same proposition, with `∃ M` outside the trajectory quantifier
(`ExtendsBeyond.lean:102-110`; canonical `api_on_canonical.lean:112-120`), and
the proof uses it only at `m = 1` (`ExtendsBeyond.lean:118-124`).  The
continuation conclusion is the concrete definition of `ExtendsBeyondT`, not a
lifespan-only surrogate (`formalization/NSFormalization/Section3/T11/LocalTheory.lean:68-74`),
and `restartBeyond` supplies exactly that concrete solution and both agreement
clauses (`formalization/NSFormalization/Section3/T11/RestartBeyond.lean:408-422`).

The target theorem `lifespanInfiniteOfLocallyFinite_of_input` is likewise
token-for-token the canonical U16 field, including `IsMaximalPeriodicSolution`
and `ENNReal.ofReal S ≤ maximalLifespanT` (`ExtendsBeyond.lean:158-176`;
canonical `api_on_canonical.lean:142-150`).  Its contraposition takes
`S = (maximalLifespanT ...).toReal`, applies the criterion at equality, obtains
`SolvesBelowT` from maximality, and invokes U14 (`ExtendsBeyond.lean:177-194`).
The maximality predicate and the supremum definition used here are the cited
tree declarations (`formalization/NSFormalization/Section3/T11/LocalTheory.lean:52-56`;
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:301-304`).

The helper `lifespan_ge_of_horizon` is a valid direct supremum argument
(`ExtendsBeyond.lean:67-75`), and `lifespan_ge_of_extends` correctly extracts
the attained extension (`ExtendsBeyond.lean:77-86`).  The bridge from the one
named local input to lane 323's residual maximal-existence input is explicit
and uses no third named assumption (`ExtendsBeyond.lean:126-145`; the input is
defined at `formalization/NSFormalization/Section3/T11/LocalExistence.lean:24-29`).

The non-vacuity construction is substantive: a nonzero coordinate-constant,
divergence-free velocity, zero force, and zero pressure are packaged on every
positive horizon (`ExtendsBeyond.lean:233-245`), and the probe simultaneously
checks the seven U14/U16 hypotheses at a nonzero velocity
(`research/T11/probes/extends_beyond_closes.lean:154-180`).  The conditional
conclusion-side witness checks both target conclusions
(`research/T11/probes/extends_beyond_closes.lean:185-225`).

All nine exported declarations have only the standard axioms.  The unsuppressed
review audit printed, exactly:

```text
'NSFormalization.Section3.T11.lifespan_ge_of_horizon' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.lifespan_ge_of_extends' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.extendsBeyond_of_input' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.periodicMaximalExistenceInput_of_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T11.exists_maximal_of_input' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.lifespanInfiniteOfLocallyFinite_of_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T11.squaredHTwoIntegralT_ne_top_of_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T11.constantVelocitySolutionT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.squaredHTwoIntegralT_constant_ne_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The target module contains no forbidden proof tokens, heartbeat override, or
anonymous instance (the hygiene scan was empty).  Relative to
`origin/erenup/integration-section3`, the Lean files are additions, not edits
to an existing module (`git diff --name-status ... -- formalization` reports
`A` for `ExtendsBeyond.lean`, `HighOrder.lean`, and `RestartBeyond.lean`; no
`M`), and there is no verification-tree diff.

## Gaps

The two residual assumptions are honestly exposed.  `PeriodicQuantitativeLocalInput'`
is still a definition-level input rather than a theorem
(`formalization/NSFormalization/Section3/T11/LocalExistence.lean:24-29`), and
`hHigh` remains the U12 residual energy-inequality result
(`formalization/NSFormalization/Section3/T11/HighOrder.lean:58-69,481-500`;
`research/T11/REPORT_337.md:64-71`).  The lane correctly records these as
upstream gaps, rather than weakening either target.

I searched the whole Section4 tree before accepting those gap claims:

```text
$ grep -rn 'PeriodicQuantitativeLocalInput' formalization/NSFormalization/Section4
(no output)
$ grep -rn 'higherOrderBound_of_energyInequality' formalization/NSFormalization/Section4
(no output)
```

Section4 does contain an analogous, differently typed `HigherOrderBound` and
its whole-space proofs (`formalization/NSFormalization/Section4/A04/Continuation.lean:184-234`),
but not the missing torus declarations.  Likewise, the report's explanation
that `horizon_le_lifespan` is not pointwise-applicable is correct: that lemma
requires a global horizon/solution family
(`formalization/NSFormalization/Section3/T11/Uniqueness.lean:58-72`), whereas
the lane has a single attained horizon and uses its direct supremum lemma.

Two documentation-only one-line fixes are requested:

1. `research/T11/REPORT_337.md:60` says the probe has “7 个 example”, but
   `research/T11/probes/extends_beyond_closes.lean` has eight examples (starts
   at lines 29, 51, 76, 108, 117, 132, 154, and 185); change `7` to `8`.
2. For precision, change the hHigh citation in
   `research/T11/REPORT_337.md:26` (and the matching module comment at
   `ExtendsBeyond.lean:95`) from `api_on_canonical.lean:112-121` to
   `:112-120`; line 121 begins the next field.

The lane's force-witness note is also mathematically sound: `forceClassT`
requires compact time support inside `Ioi 0`
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:237-245`), so
the smooth/all-order witness `nonzero_forced_witness'` is not silently usable
as a force-class witness (`formalization/NSFormalization/Section3/T11/LocalExistence.lean:653-663`).

## Commands and results

All successful Lean commands used `. scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`, and ran from `verification/`; lake commands were
sequential.

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.ExtendsBeyond
Build completed successfully (10566 jobs).
[exit 0; only replayed dependency linter diagnostics]

$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/ExtendsBeyond.lean
[exit 0; exactly 0 output]

$ LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/extends_beyond_closes.lean
[exit 0; exactly 0 output]

$ LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_extends_beyond.lean
[exit 0; exactly 0 output; all 9 #guard_msgs passed]
```

The required substantive negative mutation was run in the new reviewer probe
`research/T11/probes/rev337_negative.lean`: it changes the U14 extension
horizon from `S + δ` to `S - δ`.  The command intentionally exits 1 with the
expected type mismatch at line 42:

```text
../research/T11/probes/rev337_negative.lean:42:2: error: Type mismatch
  extendsBeyond_of_input H hHigh
has type ... → ExtendsBeyondT ν a f S u p
but is expected to have type ... → BadExtendsBeyondT ν a f S u p
```

This is a real statement mutation, not a dropped argument.  The unsuppressed
axiom output above came from `research/T11/probes/rev337_axioms.lean` and
matches the checked-in conformance file.

`make check` was rerun from the worktree root and exited 0.  Its exact decisive
tail was:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The full `make check` output also reports the repository's pre-existing
architecture inventory (`source_hashes_match: false`, 11 copied-source
admission tokens) and still exits 0; no lane-owned file is implicated.  The
conditional `scripts/gates.sh`/`check_contracts.py --base-ref
origin/erenup/integration-section3` run was not required because the lane has
no `verification/` changes (`git diff ... -- verification` is empty).

ACCEPT-WITH-NOTES — fixes: change the report's example count 7→8; tighten the hHigh citation range 112–121→112–120.
