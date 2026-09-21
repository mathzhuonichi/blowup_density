ACCEPT

# Lane 321-T11-U10-U11-restart-horizon review

## What the lane claims

The worker claims that `restart` is the `PeriodicContinuationAPI.restart` field,
conditional on the single amended input `PeriodicQuantitativeLocalInput'`, and
that the first three local-theory fields are assembled from the zero-time
specialization (`research/T11/REPORT_321.md:5-40`).  The claimed `restart`
statement is exactly the canonical field at
`research/T11/probes/api_on_canonical.lean:101-111`: it has the order
`ν,hν,f∈forceClassT,S,hS,K,hK`, the H¹ bound
`periodicSobolevENorm 1 a' ≤ K`, and returns a solution for
`timeShiftT t₀ f` together with `PeriodicLocalRegularity`.

The claimed local-theory field types match the canonical structure at
`research/T11/probes/api_on_canonical.lean:44-75`: `horizon` is a real-valued
function, `solution` uses the same selected horizon, and `regularity` uses that
solution at that same horizon.  The paper motivation is also the stated one:
the proposition gives local existence and a common interval for all Sobolev
orders (`paper/sections/02-preliminaries.tex:105-120`), while the appendix says
the H¹ restart duration is uniform as `t₀ ↑ S` and higher-order regularity holds
on the same intervals (`paper/sections/appendix-a-local-theory.tex:146-156`).

## What is in Lean

The implementation has the exact field statement at
`formalization/NSFormalization/Section3/T11/Restart.lean:70-81`.  It applies
the allowed input without restating it, choosing
`M m := forceSobolevENormT 1 (m : ℝ) f`
(`formalization/NSFormalization/Section3/T11/Restart.lean:82-94`).  Finiteness of
each M m is supplied by the tree lemma
`forceSobolevENormT_ne_top` (`formalization/NSFormalization/Section3/T10/ForcePaths.lean:144-148`).
The only shift estimate used is the correctly oriented tail inequality
`forceSobolevENormT_timeShift_le`
(`formalization/NSFormalization/Section3/T11/Restart.lean:27-51`), whose measure-theory
analogue is the existing `lintegral_enorm_shift_le`
(`formalization/NSFormalization/Section4/A04/ForceShift.lean:19-34`); shifted
smoothness and periodicity are proved at
`formalization/NSFormalization/Section3/T11/Restart.lean:53-63`, and zero shift at
`formalization/NSFormalization/Section3/T11/Restart.lean:65-68`.

The zero-time extraction uses the finite smooth datum norm from
`periodicSobolevENorm_ne_top_smooth`
(`formalization/NSFormalization/Section3/T11/CriterionBridge.lean:57-62`) and
transports the whole dependent solution/regularity package before rewriting
the zero shift (`formalization/NSFormalization/Section3/T11/Restart.lean:96-113`).
The horizon defaults to `1` outside
the admissible class and is selected by `Classical.choose` inside it
(`formalization/NSFormalization/Section3/T11/Restart.lean:115-159`); the selected
solution and regularity are then exposed at
`formalization/NSFormalization/Section3/T11/Restart.lean:161-177`.  The requested
partial assembly is explicitly a three-field `PeriodicLocalTheoryInitialAPI`
(`formalization/NSFormalization/Section3/T11/Restart.lean:179-199`), not a
claim that the five later fields already exist.

The sole named input is exactly the imported amendment, with no weakening or
extra premise: `formalization/NSFormalization/Section3/T11/LocalExistence.lean:23-29`.
The module's non-vacuity example has a nonzero datum, force, and solution
(`formalization/NSFormalization/Section3/T11/Restart.lean:201-211`; the underlying
witness is constructed at
`formalization/NSFormalization/Section3/T11/LocalExistence.lean:654-663`).
The conformance probe copies all four target shapes at
`research/T11/probes/restart_closes.lean:16-64`, and the guarded axiom audit
covers every exported declaration and projection at
`research/T11/axioms_restart.lean:1-91`.

## Gaps

The API result is intentionally conditional on
`PeriodicQuantitativeLocalInput'`; discharging that input remains U9d/U9e work,
as recorded in the worker report
(`research/T11/REPORT_321.md:56-61`) and the source definition
(`formalization/NSFormalization/Section3/T11/LocalExistence.lean:23-29`).  The full API's other fields are not claimed by
this lane.  There is no report claim that a required lemma is absent from the
tree; nevertheless, a whole-`Section4` grep for the named input, the partial
API, and the shift estimate found no conflicting declaration (the only
`restart` hits are unrelated restart wiring in A02/A04).  No existing module
is modified: `git diff --name-only origin/erenup/integration-section3...HEAD`
prints exactly:

```text
formalization/NSFormalization/Section3/T11/Restart.lean
research/T11/ATTEMPTS_RESTART.md
research/T11/REPORT_321.md
research/T11/T11_SPLIT.md
research/T11/axioms_restart.lean
research/T11/probes/restart_closes.lean
```

Hygiene checks found no forbidden declaration (`sorry`, `admit`, `axiom`, or
`native_decide`) in the implementation or positive probe; the audit file's
literal `#print axioms` text is expected.  There is no `maxHeartbeats` option
in the lane module.
The substantive negative probe
`research/T11/probes/rev321_negative.lean:12-26` changes the main H¹ datum
constant `1` to `2`.  Running it fails as required, with the exact error:

```text
exit=1
../research/T11/probes/rev321_negative.lean:25:2: error: Type mismatch
  restart H
has type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ f ∈ forceClassT,
        ∀ (S : ℝ),
          0 ≤ S →
            ∀ (K : ℝ≥0∞),
              K ≠ ∞ →
                ∃ δ,
                  0 < δ ∧
                    ∀ t₀ ∈ Icc 0 S,
                      ∀ a' ∈ initialClassT,
                        periodicSobolevENorm 1 a' ≤ K → ∃ w, PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w
but is expected to have type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ f ∈ forceClassT,
        ∀ (S : ℝ),
          0 ≤ S →
            ∀ (K : ℝ≥0∞),
              K ≠ ∞ →
                ∃ δ,
                  0 < δ ∧
                    ∀ t₀ ∈ Icc 0 S,
                      ∀ a' ∈ initialClassT,
                        periodicSobolevENorm 2 a' ≤ K → ∃ w, PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w
```

This is a substantive statement mutation, not argument deletion.  The
positive probe and the implementation's nonzero witness provide the requested
non-vacuity check.

## Commands and results

All commands used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and ran Lake
from `verification/`:

```text
LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Restart
Build completed successfully (9980 jobs).

LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/Restart.lean
(no output; exit 0)

LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/restart_closes.lean
(no output; exit 0)

LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_restart.lean
(no output; exit 0; #guard_msgs verified every expected
[propext, Classical.choice, Quot.sound] declaration)
```

From the worktree root:

```text
make check
RC=0
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.

bash scripts/gates.sh NSFormalization.Section3.T11.Restart
RC=0
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK

python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
RC=0
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

The mutation command was:

```text
LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/rev321_negative.lean
exit=1
../research/T11/probes/rev321_negative.lean:25:2: error: Type mismatch
```

The failed mutation is expected and is the negative-control result; all
required positive gates pass.
