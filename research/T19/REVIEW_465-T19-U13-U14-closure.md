ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker claims two canonical field theorems, `simultaneousPairConvergence`
and `closureInEnergy`, plus three energy helpers
(`research/T19/REPORT_465.md:3-67`).  It also claims that the implementation has
no residual gaps, named inputs, forbidden shortcuts, or heartbeat overrides
(`research/T19/REPORT_465.md:81-91`).

Those are the correct U13/U14 targets.  The paper defines the regular and
singular trajectory classes and states the energy-closure inclusion at
`paper/sections/03-torus.tex:540-545`, then requires one approximating pair
family converging in `E_T × L¹_tH^s_x` for every fixed `s < 1/2` at
`paper/sections/03-torus.tex:546-550`.  Its proof explicitly invokes the
insertion energy and force estimates and finite reference energy at
`paper/sections/03-torus.tex:552-554`; the time-embedding observation is at
`paper/sections/03-torus.tex:556-561`.

The reconciled canonical fields spell this out at
`formalization/NSFormalization/Section3/T19/Density.lean:157-189`, with the
paper's `R_{a,T}` and `S_{a,T}` represented by honest classical-solution,
finite-energy, and blow-up predicates at
`formalization/NSFormalization/Section3/T19/Density.lean:31-47`.

## 2. What is in Lean

### Statement fidelity

Both main declarations exist with exactly the claimed types:

- `simultaneousPairConvergence` is at
  `formalization/NSFormalization/Section3/T19/Closure.lean:65-85` and is
  token-for-token the canonical field at
  `formalization/NSFormalization/Section3/T19/Density.lean:169-189`.
- `closureInEnergy` is at
  `formalization/NSFormalization/Section3/T19/Closure.lean:142-148` and is
  token-for-token the canonical field at
  `formalization/NSFormalization/Section3/T19/Density.lean:159-165`.
- The worker's two literal restatements close using only `exact` at
  `research/T19/probes/closure_closes.lean:10-40`.

The three helper statements reported by the worker also exist exactly as
reported: `energyENormT_congr_Ico` at
`formalization/NSFormalization/Section3/T19/Closure.lean:13-15`,
`energySlices_of_smooth` at `:30-32`, and `energyENormT_sub_comm` at `:44-46`.

The mathematics follows the requested route.  U13 builds the genuine T18
insertion at `formalization/NSFormalization/Section3/T19/Closure.lean:86-87`;
the upstream constructor and its exact-force/lifespan/solution/blow-up/energy
exports are at `formalization/NSFormalization/Section3/T19/Threading.lean:126-161`.
The reference is identified with its zero extension on the actual energy slab
at `formalization/NSFormalization/Section3/T19/Closure.lean:88-101`.  This is a
valid simplification of the older uniqueness route: `extendByZero` was built
from the supplied reference itself, so no second solution needs identifying.

The per-scale singular trajectory is assembled at
`formalization/NSFormalization/Section3/T19/Closure.lean:102-120`.  Its finite
energy uses the genuine T18 triangle inequality
(`formalization/NSFormalization/Section3/T18/EnergyRate.lean:175-183`) and the
reference finiteness theorem
(`formalization/NSFormalization/Section3/T19/Bookkeeping.lean:154-160`), while
its blow-up and exact lifespan come from the T18 exports.  Energy convergence
uses the positive powers `ε^(1/2)` and `ε^(3/2)` at
`formalization/NSFormalization/Section3/T19/Closure.lean:121-139`.  The full
subcritical force limit is the already-proved split between negative and
nonnegative orders at
`formalization/NSFormalization/Section3/T19/Threading.lean:196-222`.

U14 honestly unpacks `RegularTrajectoryT`, invokes U13, intersects the
right-neighborhood event with the nonempty `Ioo` window, and reverses the
difference at `formalization/NSFormalization/Section3/T19/Closure.lean:149-157`.

### Hypothesis and non-vacuity audit

No hypothesis was silently added: the main types are the canonical field types,
and every named positivity/class-membership premise is passed into the actual
insertion or U13 construction.  There is no `.toReal = 0` guard or related
escape in either implementation (the only `toReal` occurrences in the
canonical T19 module belong to the separate mixed-region fields at
`formalization/NSFormalization/Section3/T19/Density.lean:117-138`).  The
existential `ε₀` has `0 < ε₀`, and the reviewer probe constructs the explicit
point `ε₀/2 ∈ Ioo 0 ε₀` at
`research/T19/probes/rev465_mutation.lean:42-45`.  It also exhibits a positive
finite ENNReal radius at `research/T19/probes/rev465_mutation.lean:47-49`.

More strongly, the reviewer probe uses viscosity `1`, zero admissible initial
datum, zero admissible force, and the repository's genuine rest solution to
apply U13 and obtain a nonempty family of `SingularTrajectoryT` witnesses
(`research/T19/probes/rev465_mutation.lean:51-85`).  Thus the outer premises and
the family conclusion are jointly inhabited, not merely the interval.

### Negative mutation

The substantive mutation widens the main U13 Sobolev range from `s < 1/2` to
`s < 3/4` (`research/T19/probes/rev465_mutation.lean:12-39`).  With the
`fail_if_success` wrapper temporarily removed, the unchanged theorem fails for
the expected threshold mismatch:

```text
../research/T19/probes/rev465_mutation.lean:36:6: error: Type mismatch
  simultaneousPairConvergence
has type
  ∀ a ∈ initialClassT,
    ∀ (ν : ℝ),
      0 < ν →
        ∀ (T : ℝ),
          0 < T →
            ∀ g ∈ forceClassT,
              ∀ (δ : ℝ),
                0 < δ →
                  ∀ (reference : ClassicalSolutionT ν a g (T + δ)),
                    ∃ ε₀,
                      0 < ε₀ ∧
                        ∃ u f,
                          (∀ ε ∈ Ioo 0 ε₀,
                              f ε ∈ forceClassT ∧
                                maximalLifespanT ν a (f ε) = ENNReal.ofReal T ∧
                                  (∃ w, w.velocity = u ε) ∧ SingularTrajectoryT ν a T (u ε)) ∧
                            Tendsto (fun ε => energyENormT T fun z => u ε z - reference.velocity z) (𝓝[>] 0) (𝓝 0) ∧
                              ∀ s < 1 / 2, Tendsto (fun ε => forceSobolevENormT 1 s fun z => f ε z - g z) (𝓝[>] 0) (𝓝 0)
but is expected to have type
  ∀ a ∈ initialClassT,
    ∀ (ν : ℝ),
      0 < ν →
        ∀ (T : ℝ),
          0 < T →
            ∀ g ∈ forceClassT,
              ∀ (δ : ℝ),
                0 < δ →
                  ∀ (reference : ClassicalSolutionT ν a g (T + δ)),
                    ∃ ε₀,
                      0 < ε₀ ∧
                        ∃ u f,
                          (∀ ε ∈ Ioo 0 ε₀,
                              f ε ∈ forceClassT ∧
                                maximalLifespanT ν a (f ε) = ENNReal.ofReal T ∧
                                  (∃ w, w.velocity = u ε) ∧ SingularTrajectoryT ν a T (u ε)) ∧
                            Tendsto (fun ε => energyENormT T fun z => u ε z - reference.velocity z) (𝓝[>] 0) (𝓝 0) ∧
                              ∀ s < 3 / 4, Tendsto (fun ε => forceSobolevENormT 1 s fun z => f ε z - g z) (𝓝[>] 0) (𝓝 0)
```

The restored probe encodes this with `fail_if_success` and typechecks with zero
output.

### Hygiene

The forbidden-token/heartbeat scan of the implementation, worker probe,
reviewer probe, and axiom file returns no matches.  There is no
`set_option maxHeartbeats`.  `git show --name-status HEAD` shows the lane commit
adds the new `Closure.lean` module and research records and modifies only
`T19_SPLIT.md`; it does not modify an existing Lean module.  The broader
`git diff --name-status origin/erenup/integration-section3...HEAD` also contains
lane 464's new `DensityEngine.lean`, but every Lean entry is `A`, never `M`.
No path below `verification/` was touched.

The source comments and canonical docstrings agree with the paper citations;
in particular, the canonical closure documentation points to
`03-torus.tex:540-561` at
`formalization/NSFormalization/Section3/T19/Density.lean:141-149`.

## 3. Gaps

There is no mathematical, statement, proof, axiom, or build gap.  The worker
report explicitly declares no gap (`research/T19/REPORT_465.md:81-85`), so the
requested whole-`Section4` verification of any "not in the tree" claim is not
applicable.  A whole-tree name search was nevertheless run and found no hidden
competing implementation of these T19 declarations.

One exact hygiene fix remains, hence `ACCEPT-WITH-NOTES`:

1. Delete the extra blank line at EOF
   `research/T19/probes/closure_closes.lean:41`.  The reproducer is
   `git diff --check HEAD^..HEAD`, which exits 2
   with exactly:

```text
research/T19/probes/closure_closes.lean:41: new blank line at EOF.
```

This is non-mathematical and does not affect any Lean gate.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, ran `lake` only from
`verification/`, and used `LEAN_NUM_THREADS=6`.

1. `lake build NSFormalization.Section3.T19.Closure` — exit 0.  The raw command
   replayed only pre-existing dependency warnings, no warning from
   `Closure.lean`; its exact final output was:

```text
Build completed successfully (10659 jobs).
```

2. `lake env lean ../formalization/NSFormalization/Section3/T19/Closure.lean`
   — exit 0, exact output: none.

3. `lake env lean ../research/T19/probes/closure_closes.lean` — exit 0, exact
   output: none.

4. `lake env lean ../research/T19/axioms_u13_u14.lean` — exit 0, exact output:

```text
'NSFormalization.Section3.T19.energyENormT_congr_Ico' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.energySlices_of_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.energyENormT_sub_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.simultaneousPairConvergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.closureInEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
```

5. `make check` — exit 0.  Exact tail:

```text
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

6. `BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6
   scripts/gates.sh NSFormalization.Section3.T19.Closure` — exit 0.  It reran
   `make check`, built the module, ran all registered contract tests and the
   mutation suite, and checked base compatibility.  Exact final output:

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

7. `python3 experiments/check_contracts.py --base-ref
   origin/erenup/integration-section3 | tail -n 3` — exit 0, exact output:

```text
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

8. Final reviewer probe:
   `lake env lean ../research/T19/probes/rev465_mutation.lean` — exit 0, exact
   output: none.

9. State/hygiene commands:

```text
$ git branch --show-current
erenup/465-T19-U13-U14-closure

$ git diff --name-only origin/erenup/integration-section3...HEAD -- verification
(no output)

$ rg -n '\b(sorry|admit|axiom|native_decide)\b|set_option\s+maxHeartbeats' \
    formalization/NSFormalization/Section3/T19/Closure.lean \
    research/T19/probes/closure_closes.lean \
    research/T19/probes/rev465_mutation.lean \
    research/T19/axioms_u13_u14.lean
(no output)
```

The pre-existing modified brief remains untouched.  The only reviewer-created
files are `research/T19/probes/rev465_mutation.lean` and this review.
