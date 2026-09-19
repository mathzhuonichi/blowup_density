ACCEPT

## 1. What the lane claims

The worker claims four canonical fields for the explicit sum
`assembledVelocity d := finiteVelocitySum (fun j => (d.component j).velocity)`:
regional agreement, regional terminal-time blow-up, the squared energy bound,
and the exact squared dissipation identity
(`research/T24/REPORT_469.md:5-28`). It claims no Ub4 assembled-solution or
Ub7 full-record assembly (`research/T24/REPORT_469.md:53-58`).

The claims are faithful to both the brief and the paper:

- The paper fixes finitely many disjoint interior balls and requires separate
  blow-up in each (`paper/sections/03-torus.tex:697-701`), constructs the finite
  sum (`paper/sections/03-torus.tex:706-712`), says that the sum equals its own
  component on each ball (`paper/sections/03-torus.tex:714`), and gives exactly
  `<= M^2 * sum epsilon` for energy and `= D^2 * sum epsilon` for dissipation
  (`paper/sections/03-torus.tex:715-718`).
- The canonical raw API has the same four types: `region_agreement` on
  `Ico 0 T` (`formalization/NSFormalization/Section3/T24/Multiple.lean:175-182`),
  `SpeedUnboundedAtOn T B_j` (`formalization/NSFormalization/Section3/T24/Multiple.lean:183-190`),
  the energy inequality (`formalization/NSFormalization/Section3/T24/Multiple.lean:191-197`),
  and the dissipation equality with the original `D` (`formalization/NSFormalization/Section3/T24/Multiple.lean:198-204`).
- The registered/local energy meanings are honest extended norms: an essential
  supremum on `Ioo 0 T` and an `L2_t L2_x` gradient norm
  (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:327-341`;
  `verification/Contracts/V1/TorusLocalTheory.lean:231-247`).
- T15 supplies the exact component identities, not surrogate assumptions:
  `energyEssSupT = ofReal (epsilon^(1/2) * M)`
  (`formalization/NSFormalization/Section3/T15/Energy.lean:168-203`) and
  `energyGradientT = ofReal (epsilon^(1/2) * D)`
  (`formalization/NSFormalization/Section3/T15/Energy.lean:205-248`).

No silent premise was added. Each public theorem is parametrized only by the
existing `RegionsData` bundle (`formalization/NSFormalization/Section3/T24/MultipleRegions.lean:14-16`).
That bundle already carries `0 < T`, `0 < N`, positive radii, interior balls,
and pairwise disjointness (`formalization/NSFormalization/Section3/T24/MultipleComponents.lean:15-39`),
plus genuine packet data rather than a named analytic placeholder. The scale is
strictly positive and satisfies `epsilon^2 < T`
(`formalization/NSFormalization/Section3/T24/MultipleComponents.lean:98-110`).
There is no `top.toReal = 0` route and no empty-family or empty-interval escape.

## 2. What is in Lean

All four claimed declarations exist with the exact types:

- `assembledVelocity` is definitionally the requested finite sum
  (`formalization/NSFormalization/Section3/T24/MultipleRegions.lean:18-20`).
- `region_agreement` has the exact quantifier order and domains
  (`formalization/NSFormalization/Section3/T24/MultipleRegions.lean:22-35`).
  Its proof uses `component_support` and pairwise disjointness, whose source
  statement is precisely cube-vanishing outside the prescribed ball
  (`formalization/NSFormalization/Section3/T24/MultipleComponents.lean:123-135`).
- `region_blowup` has the exact `SpeedUnboundedAtOn` target
  (`formalization/NSFormalization/Section3/T24/MultipleRegions.lean:37-67`).
  T15's existing theorem is global (`formalization/NSFormalization/Section3/T15/Blowup.lean:22-60`);
  the lane correctly retains the pre-periodization witness and proves its ball
  membership from scaled support before applying regional agreement. This is
  stronger than merely reusing the global conclusion and matches the brief.
- `energy_bound` is stated at
  `formalization/NSFormalization/Section3/T24/MultipleRegions.lean:129-150`.
  Squared slice norms add by pointwise disjointness
  (`formalization/NSFormalization/Section3/T24/MultipleRegions.lean:69-112`),
  then each component is bounded almost everywhere by its essential supremum.
  This correctly respects that T15 gives an essential-supremum identity, not a
  constant-in-time slice identity.
- `dissipation_bound` is stated at
  `formalization/NSFormalization/Section3/T24/MultipleRegions.lean:283-318`.
  The proof differentiates the finite sum, localizes component gradients on the
  cube interior, removes the null cube boundary, and interchanges the finite sum
  with the time integral using the genuine rescaled-dissipation measurability
  (`formalization/NSFormalization/Section3/T24/MultipleRegions.lean:152-267`).

The field-conformance file repeats the four canonical targets and closes each by
`exact` (`research/T24/probes/regions_energy_closes.lean:15-35`). The worker's
status lines accurately mark Ub5/Ub6 done and describe the actual proof routes
(`research/T24/T24_SPLIT.md:314-330`).

The reviewer non-vacuity probe supplies an actual one-region `RegionsData`
instance from the registered viscosity-one packet and the canonical interior
chart ball (`research/T24/probes/rev469_nonvacuity.lean:18-54`). It also proves
that the index family, time interval, and ball are inhabited and extracts an
actual regional blow-up witness (`research/T24/probes/rev469_nonvacuity.lean:56-74`).

## 3. Gaps

There is no gap relative to Ub5/Ub6. Ub4 and Ub7 are explicitly outside this
lane, so they are not hidden residuals. The paper's bounded-domain/no-slip
branch is outside the canonical torus API and outside this brief; the reviewed
four torus fields are complete.

The worker report declares no missing Section4 lemma or other "not in the tree"
claim, so the mandatory whole-Section4 missing-lemma grep has no target and is
not applicable.

The substantive negative check changes the main dissipation coefficient from
`E^2` to `E^2 + 1`, retaining all binders
(`research/T24/probes/rev469_wrong_dissipation_constant.lean:3-22`). Replaying
the shipped theorem fails for exactly the intended constant mismatch:

```text
../research/T24/probes/rev469_wrong_dissipation_constant.lean:22:2: error: Type mismatch
  RegionsData.dissipation_bound d
has type
  energyGradientT d.T d.assembledVelocity ^ 2 = ENNReal.ofReal (E ^ 2 * ∑ j, d.ε j)
but is expected to have type
  energyGradientT d.T d.assembledVelocity ^ 2 = ENNReal.ofReal ((E ^ 2 + 1) * ∑ j, d.ε j)
```

Hygiene is clean. A case-insensitive scan of the implementation, canonical
probe, axiom file, and reviewer probes for whole-word
`sorry|admit|axiom|native_decide` and for `maxHeartbeats` produced no output.
There is no heartbeat override. `git diff --check` produced no output.
`git diff --diff-filter=M --name-only origin/erenup/integration-section3...HEAD -- '*.lean'`
also produced no paths (only Git's multiple-merge-base warning), so no existing
Lean module is modified. `git show --name-status --format= HEAD` shows the lane
commit adds `MultipleRegions.lean` and the research artifacts and modifies only
`T24_SPLIT.md`.

## 4. Commands and results

Every Lean command below used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and
ran Lake from `verification/`.

1. Required dependency closure:

   ```text
   $ lake build NSFormalization.Section3.T24.MultipleComponents NSFormalization.Section3.T15.Blowup NSFormalization.Section3.T15.Energy
   Build completed successfully (10050 jobs).
   ```

2. Lane module build:

   ```text
   $ lake build NSFormalization.Section3.T24.MultipleRegions
   Build completed successfully (10051 jobs).
   ```

   Exit 0. Lake replayed pre-existing dependency linter warnings; there was no
   line, warning, or error attributed to `MultipleRegions`.

3. Direct module and canonical-probe checks:

   ```text
   $ lake env lean ../formalization/NSFormalization/Section3/T24/MultipleRegions.lean
   <no output>
   $ lake env lean ../research/T24/probes/regions_energy_closes.lean
   <no output>
   ```

   Both exited 0.

4. Axiom file, exit 0, exact output:

   ```text
   'NSFormalization.Section3.T24.RegionsData.assembledVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T24.RegionsData.region_agreement' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T24.RegionsData.region_blowup' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T24.RegionsData.enorm_sq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T24.RegionsData.slice_energy_additive' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T24.RegionsData.component_energy_sq' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T24.RegionsData.energy_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T24.RegionsData.component_slice_contDiff' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T24.RegionsData.component_gradient_support' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T24.RegionsData.gradient_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T24.RegionsData.gradient_enorm_sq_sum' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T24.RegionsData.slice_gradient_additive' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T24.RegionsData.component_gradient_rate' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T24.RegionsData.component_dissipation_sq' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T24.RegionsData.dissipation_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

5. Reviewer non-vacuity probe, exit 0, exact output:

   ```text
   'Rev469Nonvacuity.domains_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound]
   'Rev469Nonvacuity.blowup_has_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
   'Rev469Nonvacuity.concrete_regions_data_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

6. Negative probe, expected exit 1, exact output:

   ```text
   ../research/T24/probes/rev469_wrong_dissipation_constant.lean:22:2: error: Type mismatch
     RegionsData.dissipation_bound d
   has type
     energyGradientT d.T d.assembledVelocity ^ 2 = ENNReal.ofReal (E ^ 2 * ∑ j, d.ε j)
   but is expected to have type
     energyGradientT d.T d.assembledVelocity ^ 2 = ENNReal.ofReal ((E ^ 2 + 1) * ∑ j, d.ε j)
   ```

7. `make check`, exit 0. Because its contract-closure JSON is very large, the
   command was rerun with `set -o pipefail` and `tail -12`; exact output:

   ```text
     },
     "base_compatibility_checked": false,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.042s

   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

8. The worker's additional reported checks were also rerun: `lake test` exited
   0 with all registered contract checks reporting standard logical axioms, and
   `make test-mutations` exited 0 with this exact final output:

   ```text
   implementation_refactor: accepted
   admitted_proof: rejected as required
   extra_axiom: rejected as required
   weakened_hypothesis: rejected as required
   Mutation suite passed. This is an infrastructure check, not a PDE proof.
   ```

9. Required base comparison, exit 0, exact output:

   ```text
   $ git diff --name-only origin/erenup/integration-section3...HEAD
   warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 84cbedb39e289aaafdd85cc42b42139dfc66e615
   NEXT_SESSION.md
   PLAN.md
   collaboration/briefs/465-T19-U13-U14-closure.md
   collaboration/briefs/466-T19-U10-U11-U12-projection.md
   collaboration/briefs/467-T24-UbCAN-Ub1-Ub3-multiple-regions.md
   formalization/NSFormalization/Section3/T19/Threading.lean
   formalization/NSFormalization/Section3/T24/MultipleRegions.lean
   logs/AGENT_RUNS.csv
   research/T19/ATTEMPTS_U0.md
   research/T19/REPORT_461.md
   research/T19/REVIEW_461-T19-U0-insertion-from-reference.md
   research/T19/T19_SPLIT.md
   research/T19/axioms_u0.lean
   research/T19/probes/rev461_negative_lifespan.lean
   research/T19/probes/rev461_nonvacuity.lean
   research/T19/probes/threading_closes.lean
   research/T24/ATTEMPTS_UB5_UB6.md
   research/T24/REPORT_469.md
   research/T24/T24_SPLIT.md
   research/T24/axioms_ub5_ub6.lean
   research/T24/probes/regions_energy_closes.lean
   ```

   The branch has multiple merge bases and includes inherited lane/integration
   additions. The lane's own `git show --name-status HEAD` marks
   `MultipleRegions.lean` as `A`, not `M`; the only `M` in the lane commit is
   `research/T24/T24_SPLIT.md`. A separate `--diff-filter=M -- '*.lean'` query
   returned no paths.

10. Neither the lane commit nor the base comparison touches `verification/`.
   Therefore the review rule's conditional `scripts/gates.sh` and
   `check_contracts.py --base-ref origin/erenup/integration-section3` gates are
   not applicable; `make check`, `lake test`, and the mutation suite above were
   nevertheless rerun.

Fixes: none.
