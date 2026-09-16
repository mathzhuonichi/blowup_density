ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker claims six declarations: the four rapid/Schwartz results
`density_rapid`, `zeroIff_rapid`, `regularReference_rapid`, and
`schwartzDensity`, plus the guarded parametric `density` and `zeroIff`
(`research/R45/REPORT_257.md:5-16`).  It also claims that all six have only the
three standard logical axioms and that concrete `nu = T = 1`, `a = g = 0`
instances are inhabited (`research/R45/REPORT_257.md:29-34`).

Those mathematical claims are correct.  The only notes are stale bookkeeping
caused by the later merge of integration into this lane: the report still says
that `CompactClassRider.lean` is absent (`research/R45/REPORT_257.md:38-42`),
although it is now present and contains `regularReference_compact`
(`verification/Bindings/CompactClassRider.lean:26-46`), and it says no merge
was performed (`research/R45/REPORT_257.md:59`) although current HEAD is the
later integration merge `f6e879f`.  The same stale compact-rider statement
appears in `research/R45/COMPARISON.md:115-125`.  These do not affect the lane
commit `b3862a6` or its Lean results.

## 2. What is in Lean

### Statement fidelity

All six declarations exist with the claimed statements.

- `density_rapid` is at
  `verification/Bindings/RapidClassDensity.lean:33-39`.  After specializing
  `Y = forceClassRapid`, its binder order and conclusion are token-for-token
  the `density` field at `research/R45/Spec.lean:64-70`.
- `zeroIff_rapid` is at
  `verification/Bindings/RapidClassDensity.lean:67-72`; it is the rapid
  specialization of `research/R45/Spec.lean:84-90`, including the reverse
  implication and with no outer subcriticality hypothesis.
- `regularReference_rapid` is at
  `verification/Bindings/RapidClassDensity.lean:125-142`; it matches
  `research/R45/Spec.lean:130-147` after specializing `Y`, including the exact
  order of class membership, exact lifespan, force error, energy error, and
  history equality.
- `schwartzDensity` is at
  `verification/Bindings/RapidClassDensity.lean:214-220` and is verbatim the
  field at `research/R45/Spec.lean:104-110`; in particular it exposes no extra
  `a in initialClassR` premise.
- The guarded `density` and `zeroIff` are at
  `verification/Bindings/RapidClassDensity.lean:227-251` and match the full
  fields at `research/R45/Spec.lean:64-90`.

The mathematics matches the manuscript.  Theorem 4.1 states the threshold
`s_q = 2/q - 3/2`, density for fixed `a in X_R`, the zero-data iff, and the
regular-reference rider (`paper/sections/04-whole-space.tex:7-13`).  Corollary
4.5 replaces `F_R` by `F_c` or `F_rd` and explicitly includes Schwartz data
(`paper/sections/04-whole-space.tex:194-198`).  The contract's
`criticalOrder` is exactly `2/q - 3/2`
(`verification/Contracts/V1/Data.lean:256-259`), and the registered rapid and
Schwartz classes reproduce the paper definitions
(`verification/Contracts/V1/Data.lean:511-514,565-578`).

The proofs use the intended tree results:

- G2, `memForceR_of_memForceRapid`, is
  `formalization/NSFormalization/Section4/R41/ClassFacts.lean:1067-1076` and is
  used in both the insertion and non-density branches
  (`verification/Bindings/RapidClassDensity.lean:47-50,92-96,110-114`).
- G3, `memForceRapid_of_compact_difference`, is
  `formalization/NSFormalization/Section4/R41/ClassFacts.lean:1162-1169` and
  keeps the inserted witnesses in the rapid class
  (`verification/Bindings/RapidClassDensity.lean:59-63,201-204`).
- G4, the Schwartz-to-`initialClassR` inclusion, is
  `formalization/NSFormalization/Section4/R41/ClassFacts.lean:1189-1197` and is
  the only adapter used by `schwartzDensity`
  (`verification/Bindings/RapidClassDensity.lean:221-223`).
- The insertion constructor really requires the honest `a in initialClassR`,
  `MemForceR g`, and strict lifespan hypotheses
  (`verification/Bindings/InsertionFromData.lean:86-110`), while its exact
  lifespan and force convergence adapters are at
  `verification/Bindings/InsertionFromData.lean:112-131`.
- The zero-data converse uses an explicit positive excluded radius, not a
  vacuous negated density statement
  (`formalization/NSFormalization/Section4/R41/NonDensity.lean:46-69`).

There are no silent or isolated supplier hypotheses.  All hypotheses in the
six public statements are exactly Spec hypotheses.  The norms in the
conclusions are ENNReal-valued directly; there is no norm `.toReal` escape
(`verification/Contracts/V1/Data.lean:215-228,463-476`).  `T > 0`,
`0 <= tau`, and `tau < T` prevent the rider's time range from being empty
(`verification/Bindings/RapidClassDensity.lean:126-142`), and positive radii
are retained.  `RelativelyDense` requires a witness for every rapid target and
positive radius, and `breakdownSetIn` requires both class membership and a
lifespan bound (`verification/Contracts/V1/Data.lean:667-674,691-703`).

The supplied non-vacuity checks compile.  They prove rapid density at
`nu = T = 1`, obtain an actual rapid breakdown witness around `g = 0`, and
instantiate the rider with the transported zero classical solution
(`research/R45/axioms_rapid_class.lean:20-72`).

### Axioms and hygiene

The audit contains all six `#print axioms` commands
(`research/R45/axioms_rapid_class.lean:13-18`).  Its exact output was:

```text
'BlowupDensity.Bindings.density_rapid' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.zeroIff_rapid' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.regularReference_rapid' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.schwartzDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.density' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.zeroIff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

An anchored search found no declaration-level `sorry`, `admit`, `axiom`,
`native_decide`, or `set_option maxHeartbeats` in the new Lean files.  The
module's direct Lean run emits no linter warning, so there are also no unused
public binders.  `git diff --check origin/erenup/integration...HEAD` is clean.

The requested range command printed:

```text
$ git diff --name-only origin/erenup/integration...HEAD
formalization/NSFormalization/Section4/R41/ClassFacts.lean
research/R41D/ATTEMPTS_SMALL_GAPS.md
research/R41D/COMPARISON.md
research/R41D/REPORT_234.md
research/R41D/axioms_class_facts.lean
research/R45/ATTEMPTS_RAPID.md
research/R45/COMPARISON.md
research/R45/REPORT_257.md
research/R45/axioms_rapid_class.lean
verification/Bindings/RapidClassDensity.lean
```

This range includes stacked lane 234 because the current remote integration
ref has advanced and its merge-base with HEAD is `417c0cc`; no existing Lean
module has status `M`.  The lane's own commit confirms its actual scope:

```text
$ git diff --name-status b3862a6^..b3862a6
A research/R45/ATTEMPTS_RAPID.md
M research/R45/COMPARISON.md
A research/R45/REPORT_257.md
A research/R45/axioms_rapid_class.lean
A verification/Bindings/RapidClassDensity.lean
```

Thus the only existing file edited by lane 257 is the explicitly requested
comparison record; its Lean binding and audit are new files.

## 3. Gaps

No rapid-class mathematical field remains open.  The full guarded parametric
`regularReference` declaration is not part of this lane, exactly as the brief
directed for the original base.  The current tree now has the compact
specialization at `verification/Bindings/CompactClassRider.lean:29-46` and the
rapid specialization at
`verification/Bindings/RapidClassDensity.lean:125-142`, but still has no
combined theorem named `regularReference`.

The mandated whole-tree missing-lemma search was run:

```text
$ grep -rn -E 'regularReference(_rapid|_compact)?' formalization/NSFormalization/Section4 || true
```

It produced zero output.  A separate search of `verification/` found only the
two specialized declarations, not the combined one.  This is registration
work, not a missing rapid proof.

The review has three exact documentation-only fixes; no Lean fix is required:

1. Replace `research/R45/REPORT_257.md:38-42` with the one line: “No
   rapid-class mathematical field remains open and no hypothesis was isolated;
   the guarded parametric `regularReference` combination remains registration
   work, while `CompactClassRider.lean` arrived later through integration.”
2. Replace `research/R45/REPORT_257.md:59` with the one line: “The worker made
   no push, merge, or rebase before commit `b3862a6`; HEAD later received the
   integration merge `f6e879f`.”
3. Replace `research/R45/COMPARISON.md:117-125` with the one line: “After the
   later integration merge supplied `CompactClassRider.lean`, the remaining
   R45 work is the final guarded `regularReference` combination and four-field
   API registration; no rapid-class mathematical field is open.”

## 4. Commands and results

All Lean/Lake commands sourced `scripts/lean-env.sh`; Lake ran only from
`verification/` and `LEAN_NUM_THREADS=6` was set.  Large generated closure JSON
is hundreds of kilobytes, so exact terminal tails are pasted below, consistent
with the repository's review-log size rule.

1. `cd verification && LEAN_NUM_THREADS=6 lake build Bindings.RapidClassDensity`
   exited 0.  It replayed only inherited upstream linter warnings; there was no
   warning for `RapidClassDensity`.  Exact final output:

   ```text
   Build completed successfully (10612 jobs).
   ```

2. `cd verification && LEAN_NUM_THREADS=6 lake env lean Bindings/RapidClassDensity.lean`
   exited 0 with exactly zero output.

3. `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R45/axioms_rapid_class.lean`
   exited 0 with exactly the six axiom lines pasted in part 2; the three
   non-vacuity examples also elaborated.

4. `LEAN_NUM_THREADS=6 make check` exited 0.  Exact terminal tail:

   ```text
         "Tests.MainThresholds"
       ]
     },
     "base_compatibility_checked": false,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.044s

   OK
   python3 experiments/check_work_queue.py
   30 work items: ownership, contract registration and task cards consistent.
   ```

5. `LEAN_NUM_THREADS=6 make test` exited 0.  It replayed inherited warnings and
   printed a standard-axioms success line for every registered suite.  Exact
   final line:

   ```text
   info: Tests/MainThresholds.lean:15:0: Contract BlowupDensity.Tests.checkedMainThresholds: checked; standard logical axioms only
   ```

6. `LEAN_NUM_THREADS=6 scripts/gates.sh Bindings.RapidClassDensity` exited 0.
   Exact terminal tail:

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

7. `LEAN_NUM_THREADS=6 python3 experiments/check_contracts.py --base-ref origin/erenup/integration`
   exited 0.  Its generated JSON had 346102 output tokens; exact final fields:

   ```text
     "base_compatibility_checked": true,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   ```

8. Negative probe: `research/R45/probes/rev257_widen_history.lean:16-35`
   substantively widens the main rider history from `[0,tau]` to `[0,T]`.
   `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R45/probes/rev257_widen_history.lean`
   exited 1 as required, with this exact error:

   ```text
   ../research/R45/probes/rev257_widen_history.lean:34:2: error: Type mismatch
     regularReference_rapid nu hnu T hT q hq s hs a ha g hg delta hdelta v tau htau0 htauT r eta hr heta
   has type
     ∃ f ∈ forceClassRapid,
       ∃ u,
         maximalLifespanR nu a f = ENNReal.ofReal T ∧
           forceSobolevENorm q s (f - g) < r ∧
             energyENorm T (u.velocity - v.velocity) < eta ∧
               ∀ (t : ℝ),
                 0 ≤ t → t ≤ tau → ∀ (x : NavierStokes.ProblemStatement.Space), u.velocity (t, x) = v.velocity (t, x)
   but is expected to have type
     ∃ f ∈ forceClassRapid,
       ∃ u,
         maximalLifespanR nu a f = ENNReal.ofReal T ∧
           forceSobolevENorm q s (f - g) < r ∧
             energyENorm T (u.velocity - v.velocity) < eta ∧
               ∀ (t : ℝ),
                 0 ≤ t → t ≤ T → ∀ (x : NavierStokes.ProblemStatement.Space), u.velocity (t, x) = v.velocity (t, x)
   ```

9. The anchored forbidden-token/heartbeat search and
   `git diff --check origin/erenup/integration...HEAD` both exited 0 with exactly
   zero output.
