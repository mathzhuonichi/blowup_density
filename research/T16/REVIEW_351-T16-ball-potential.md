ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker reports that Gap 1 is closed for a reference field smooth and
divergence-free only on `I ×ˢ Metric.ball x₀ r` (`research/T16/REPORT_351.md:5-17`).
It also claims a packaged witness for the three potential fields and explicitly
leaves the periodic correction block to Gap 2 (`research/T16/REPORT_351.md:19-36`).
The route claim is that the global I02 curl theorem is not applicable and that
the curl identity is re-derived using a segment-localized divergence hypothesis
(`research/T16/REPORT_351.md:28-30`; `research/T16/ATTEMPTS_BALL_POTENTIAL.md:45-55`).

## 2. What is in Lean

The two residual statements are present exactly as requested:

- `timePotential_contDiffOn_ball` has the open-time hypothesis and the exact
  `ContDiffOn` conclusion at `formalization/NSFormalization/Section3/T16/BallPotential.lean:181-183`.
- `spatialCurl_timePotential_on_ball` has no silently added `IsOpen I`; its
  hypotheses and pointwise curl conclusion are exactly at
  `formalization/NSFormalization/Section3/T16/BallPotential.lean:237-241`.
- `exists_potential_on_ball` has the required `A : SpaceTimeField`, smoothness,
  globally quantified radial formula, and local curl clauses at
  `formalization/NSFormalization/Section3/T16/BallPotential.lean:324-339`.

The named assumptions are load-bearing and isolated: `hI` is used to make the
spatial bump extension smooth in the first theorem, while `hv` and `hdiv` are
used in the slice construction and segment curl calculation in the second
(`formalization/NSFormalization/Section3/T16/BallPotential.lean:181-228`,
`formalization/NSFormalization/Section3/T16/BallPotential.lean:237-316`).  No
target-equal hypothesis or empty-interval shortcut is added.

These match the canonical API fields at
`formalization/NSFormalization/Section3/T16/LocalPotential.lean:133-139` and
the reconciled spec at `research/T16/Spec.lean:243-259`.  The formula is
definitionally the centered radial integral (`formalization/NSFormalization/Paper1/RadialPotential.lean:173-179`),
and the underlying time slice is exactly `timePotential`
(`formalization/NSFormalization/Paper1/RadialPotential.lean:201-214`).  The
paper states the same local ball formula and curl identity at
`paper/sections/03-torus.tex:176-212`.

The supporting declarations are genuine proofs, not named-input or goal
repackaging: segment curl lemmas are at
`formalization/NSFormalization/Section3/T16/BallPotential.lean:68-110`,
segment congruence at
`formalization/NSFormalization/Section3/T16/BallPotential.lean:114-128`, and
the bump smoothness lemmas at
`formalization/NSFormalization/Section3/T16/BallPotential.lean:132-172`.
The comparison with I02 is accurate: I02 requires whole-space regularity and
whole-space divergence (`formalization/NSFormalization/Section4/I02/Reference.lean:86-110`),
whereas the lane's local theorem uses only the ball hypotheses.  The probe
checks the three API field types and supplies a nonzero constant divergence-free
field (`research/T16/probes/ball_potential_closes.lean:29-45`,
`research/T16/probes/ball_potential_closes.lean:50-64`).

## 3. Gaps and hygiene

Gap 2 is explicitly out of scope (`research/T16/REPORT_351.md:35-36`).  A grep of
the entire `formalization/NSFormalization/Section4` tree found no
`periodicSet`/`lattice lift`/`correction_*` declaration, so this open-gap claim
is not contradicted by an existing Section 4 lemma.  No `sorry`, `admit`,
`axiom`, or `native_decide` token occurs in the new Lean module, and its only
heartbeat overrides are the two commented `400000` declarations
(`formalization/NSFormalization/Section3/T16/BallPotential.lean:174-183`,
`formalization/NSFormalization/Section3/T16/BallPotential.lean:229-239`).

The lane-351 commit itself changes only the new module and four new research
files (`git diff --name-only 88768071c0e7cc66f33498108773300b449a2e34^..88768071c0e7cc66f33498108773300b449a2e34`).
The requested diff against the moving integration ref also lists the inherited
lane-347 `LocalPotential.lean` and records; that is stacked-base history, not a
modification made by commit 88768071.  The branch is stale relative to the
current integration ref (`HEAD...origin/erenup/integration-section3 = 3 76`),
so the lead should synchronize the base before merge.  This is not a theorem
defect and no verification path is changed by lane 351.

## 4. Commands and results

All commands used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and ran `lake`
from `verification/`.

`lake build NSFormalization.Section3.T16.BallPotential` exited 0 and ended with
the exact line `Build completed successfully (9358 jobs).`  The only output was
the pre-existing replayed-source linter/deprecation warnings (71 lines total;
none points into `BallPotential.lean`).

`lake env lean ../formalization/NSFormalization/Section3/T16/BallPotential.lean`
exited 0 with 0 output.  The canonical probe likewise exited 0 with 0 output.

`lake env lean ../research/T16/axioms_ball_potential.lean` exited 0.  Exact
axiom output (all eight declarations) was:

```text
'NSFormalization.Section3.T16.curl_potential_of_segment' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.curl_centeredPotential_of_segment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T16.timePotential_congr_segment' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.contDiffOn_bumpSmul' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.contDiff_bumpSmul_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.timePotential_contDiffOn_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.spatialCurl_timePotential_on_ball' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T16.exists_potential_on_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`make check` exited 0 (43,333 output lines).  Its exact head began with
`python3 experiments/check_formalization_plan.py --check` and reported
`missing_copied_imports: []`; its exact tail was:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.048s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The same global architecture scan also printed `source_hashes_match: false`
and `Explicit axiom/admission tokens, all copied sources: 11`; these are
pre-existing copied-source diagnostics (the new module has none), and the
command still exited 0.

`scripts/gates.sh NSFormalization.Section3.T16.BallPotential` exited 0 and ended
exactly with:

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

Because `git diff --name-only origin/erenup/integration-section3...HEAD` has no
`verification/` path, the section-3 `check_contracts.py --base-ref` gate is not
required for this lane.  Running it manually against the moving ref reproduces
the expected stale-base error:

```text
AssertionError: Removed stable specification: verification/Contracts/V1/TorusLocalTheory.lean
```

Finally, the substantive negative mutation in
`research/T16/probes/rev351_negative.lean` flips the sign of the main radial
formula.  Lean exits 1 at line 34 with the expected mismatch: the reused proof
has `A (t, x) = ∫ ...` while the mutated goal requires
`A (t, x) = -∫ ...`; this is not an argument-dropping failure.

## Exact fixes

1. Rebase or merge the current `origin/erenup/integration-section3` into the
   stacked lane, retain the lane-351 five commit paths plus this review/probe,
   and rerun the mandatory gates before merge; the current branch is 76 commits
   behind and the moving-base contract check reports the missing
   `TorusLocalTheory` specification (`research/T16/REVIEW_351-T16-ball-potential.md:60-63,131-138`).
