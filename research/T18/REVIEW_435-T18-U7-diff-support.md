ACCEPT-WITH-NOTES

Exact one-line fix: after `# REPORT 435`, insert `> The original sections 1–4 below are superseded in full by “Continuation fix final report (lead ruling)” at line 101.`

## What the lane claims

The current, appended final report claims the lead-ruled theorem with one explicit raw packet-support premise (`research/T18/REPORT_435.md:101-125`), the Spec-form discharge from `PacketImportAPI.velocity_support` (`research/T18/REPORT_435.md:127-148`), and no remaining U7 residual (`research/T18/REPORT_435.md:141-148`). Those claims are accurate. The report's older opening still says that the theorem is absent and presents the pre-ruling residual as current (`research/T18/REPORT_435.md:28-30,44-67`); the one-line supersession marker above is needed so the file has only one current account.

The mathematical target is faithful. The paper says that, for every `t<T`, `u_ε-v` is supported in a ball of diameter `O(ε)` inside the chosen ball (`paper/sections/03-torus.tex:287-295`). The reconciled torus spelling deliberately replaces the false single bounded ball for the periodic lift by `periodicSet (ball x₀ (ε·ρ))`, together with containment of the representative ball in the chart (`research/T18/RECONCILIATION.md:49-50,63-65`). `periodicSet` is exactly the union over integer lattice translates (`formalization/NSFormalization/Section3/T16/LocalPotential.lean:68-75`).

The four Spec fields are `diffSupportRadius`, its strict positivity, the support inclusion, and chart inclusion (`research/T18/Spec.lean:1861-1882`). Their canonical realizations are:

- `diffSupportRadius` at `formalization/NSFormalization/Section3/T18/Support.lean:35-41`;
- `diffSupportRadius_pos` at `formalization/NSFormalization/Section3/T18/Support.lean:49-56`;
- `velocityDifference_support` at `formalization/NSFormalization/Section3/T18/Support.lean:169-195`;
- `diffSupport_in_chart` at `formalization/NSFormalization/Section3/T18/Support.lean:197-208`.

The conclusion of `velocityDifference_support` is the Spec field exactly after replacing Spec objects by `InsertionData` projections: the binders remain `∀ ε ∈ Ioc 0 (ε₀ data), ∀ t ∈ Ico 0 data.place.T`, the function is the actual `velocity data ε - data.reference.velocity`, and the target is the same open ball inside `periodicSet` (`Support.lean:175-182`; `Spec.lean:1873-1876`). The raw premise is exactly the registered packet clause (`verification/Contracts/V1/Packet.lean:218-221`), and the assembly-shaped probe discharges it directly with `P.velocity_support` (`research/T18/probes/u7_closes.lean:74-97`).

No hypothesis is vacuous or misleading. The raw premise is used to obtain support in `Kstar` via `carrier_subset` (`Support.lean:134-142`; the placement field is at `Section3/T15/Scaling.lean:153-157`). The common scale threshold is positive (`Section3/T18/Insertion.lean:98-103`), and `place.T` is positive (`Section3/T15/Scaling.lean:108-115`). The reviewer witness chooses `ε=ε₀ data` and `t=0`, proving both quantified domains are simultaneously inhabited (`research/T18/probes/rev435_nonvacuity.lean:6-9`).

## What is in Lean

All declarations claimed by the current final report exist. Besides the four fields, the module contains `packetCarrierRadius_spec` (`Support.lean:43-47`), `diffSupportRadius_eq` (`Support.lean:49-51`), `slice_tsupport_subset_spacetime_tsupport` (`Support.lean:58-70`), `correction_slice_support` (`Support.lean:72-117`), and `periodizedScaledVelocity_support` (`Support.lean:119-167`).

The radius is honest: `place.Kstar` lies in the cutoff plateau and hence in the origin ball of radius `D.θRadius` (`Support.lean:43-47`; the threaded facts are `Section3/T16/LocalPotential.lean:120-124`). Thus `packetCarrierRadius := D.θRadius` really is a carrier radius, and `max D.θRadius packetCarrierRadius` reduces to the same strictly positive radius (`Support.lean:37-56`). The chart inclusion uses the strict cutoff placement estimate and `ball_in_chart` (`Support.lean:203-208`; `Section3/T16/LocalPotential.lean:130-132`; `Section3/T17/Correction.lean:87-96`).

For the packet term, the proof invokes the actual raw slice-support transport theorem (`Section3/T15/Placement.lean:115-157`), compactness of `Kstar`, the closed lattice-lift support lemma (`Section3/T16/Assembly.lean:197-225`), and monotonicity of `periodicSet` (`Section3/T16/Assembly.lean:241-246`). For the full difference it unfolds the actual insertion velocity (`Section3/T18/Insertion.lean:59-62`) and applies `tsupport_add` to the correction and packet bounds (`Support.lean:183-195`). This avoids the open-ball closure error identified in the brief.

The conformance probe copies all four Spec-form fields and constructs them with no residual premise once a registered packet is supplied (`research/T18/probes/u7_closes.lean:60-97`). Every `#print axioms` in `research/T18/axioms_u7.lean:5-12` prints exactly `[propext, Classical.choice, Quot.sound]`.

Hygiene passes for the lane files: the forbidden-token/max-heartbeat search over `Support.lean`, the conformance and axiom files, and both reviewer probes produced no output. There is no `set_option maxHeartbeats`. `Support.lean` is absent from `origin/erenup/integration-section3`, so it is a new module; the continuation changes only that lane-owned module and research files. The exact requested three-dot comparison warns that there are two merge bases and chooses the older `324c1cb1`, so it lists stacked/inherited T20/T22/T24 and verification files. The unambiguous U7 range `git diff --name-status 7fb2adc1..HEAD` contains only:

```text
A	formalization/NSFormalization/Section3/T18/Support.lean
A	research/T18/ATTEMPTS_U7.md
A	research/T18/REPORT_435.md
M	research/T18/T18_SPLIT.md
A	research/T18/axioms_u7.lean
A	research/T18/probes/u7_closes.lean
```

In particular, this lane did not touch `verification/` and did not modify an existing source module. The later brief expressly permits continuation edits to the lane's own `Support.lean`.

The current final report declares no missing theorem. For completeness, the superseded claim that the raw clause was not retained was checked both at the records (`Section3/T15/Scaling.lean:201-203`; `Section3/T18/Insertion.lean:37-57`) and with the required whole-tree searches. Exact output:

```text
$ grep -rn -E 'ScalingAPI\.velocity_support|periodizedScaledVelocity_support|scaledVelocity_tsupp_subset|latticeLift_sliceSupport_closed' formalization/NSFormalization/Section4
[no output]
$ grep -rn -E 'velocityDifference_support|packetCarrierRadius|diffSupportRadius' formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/R42/Lifespan.lean:159:`InsertionFamilyAPI.velocityDifference_support`), this is the compact-support
```

The R42 hit is the distinct whole-space API, not the missing torus theorem or a `ScalingAPI.velocity_support` projection.

## Gaps

There is no mathematical or Lean gap in U7. The only requested fix is the one-line report supersession marker stated above; it prevents the obsolete `REPORT_435.md:28-30,44-67` from contradicting the final report at `:101-148`.

The substantive negative mutation replaces the proved radius by half the radius (`research/T18/probes/rev435_negative_half_radius.lean:8-19`). It fails for the expected reason, not by dropping an argument:

```text
../research/T18/probes/rev435_negative_half_radius.lean:19:2: error: Type mismatch
  velocityDifference_support data hsupp ε hε t ht
has type
  (tsupport fun x => velocity data ε (t, x) - data.reference.velocity (t, x)) ⊆
    periodicSet (ball data.place.x₀ (ε * diffSupportRadius data))
but is expected to have type
  (tsupport fun x => velocity data ε (t, x) - data.reference.velocity (t, x)) ⊆
    periodicSet (ball data.place.x₀ (ε * (diffSupportRadius data / 2)))
```

An extra current-base contract diagnostic fails because this old worktree does not contain a stable contract added later to the moving integration branch. It is not a U7 gate: `git diff --name-only 7fb2adc1..HEAD` has no `verification/` path. The failure is recorded rather than hidden:

```text
AssertionError: Removed stable specification: verification/Contracts/V1/ConservativeForcing.lean
```

`origin/erenup/integration-section3` contains that file at commit `8bb95ef8`, while this lane split predates it. No contract or verification fix belongs in this lane.

## Commands and results

All Lean commands were run from `verification/` after sourcing `scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6` for the build.

1. `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T18.Support` exited 0. It replayed pre-existing upstream linter warnings and emitted none from `Support.lean`; the exact final line was:

   ```text
   Build completed successfully (10018 jobs).
   ```

2. `lake env lean ../formalization/NSFormalization/Section3/T18/Support.lean` exited 0 with exactly zero output.

3. `lake env lean ../research/T18/probes/u7_closes.lean` exited 0 with exactly zero output.

4. `lake env lean ../research/T18/probes/rev435_nonvacuity.lean` exited 0 with exactly zero output.

5. `lake env lean ../research/T18/axioms_u7.lean` exited 0 with exact output:

   ```text
   'NSFormalization.Section3.T18.packetCarrierRadius_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T18.diffSupportRadius_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T18.diffSupportRadius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T18.slice_tsupport_subset_spacetime_tsupport' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T18.correction_slice_support' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T18.periodizedScaledVelocity_support' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T18.velocityDifference_support' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T18.diffSupport_in_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

6. Root `make check` exited 0. Exact terminal tail:

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

7. The negative probe command exited 1 with the expected exact error quoted in the Gaps section.

8. Although no U7 commit touches `verification/`, I additionally ran `BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T18.Support`. Its module build, `make test`, and mutation suite passed; exact mutation output was:

   ```text
   == make test-mutations
   extra_axiom: rejected as required
   weakened_hypothesis: rejected as required
   Mutation suite passed. This is an infrastructure check, not a PDE proof.
   == check_contracts
   ```

   It then exited 1 with the moving-base error quoted below. The separately requested diagnostic `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` reproduced exactly:

   ```text
   Traceback (most recent call last):
     File "/data_8T/ping/blowup_density/.claude/worktrees/435-T18-U7-diff-support/experiments/check_contracts.py", line 153, in <module>
       print(json.dumps(check(base=args.base_ref), indent=2))
                        ^^^^^^^^^^^^^^^^^^^^^^^^^
     File "/data_8T/ping/blowup_density/.claude/worktrees/435-T18-U7-diff-support/experiments/check_contracts.py", line 143, in check
       check_compatibility(root, base, contracts)
     File "/data_8T/ping/blowup_density/.claude/worktrees/435-T18-U7-diff-support/experiments/check_contracts.py", line 62, in check_compatibility
       assert (root / path).is_file(), f'Removed stable specification: {path}'
              ^^^^^^^^^^^^^^^^^^^^^^^
   AssertionError: Removed stable specification: verification/Contracts/V1/ConservativeForcing.lean
   ```
