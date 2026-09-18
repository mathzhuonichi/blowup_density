REJECT

## 1. What the lane claims

The r1 completion says that `Placement.lean` proves thirteen declarations from
the raw packet clauses: velocity/pressure support on `Ico 0 T`, force support at
every time, affine-image/ball/cube containment, and compact support of all three
kinds of slice (`research/T15/REPORT_376.md:15-48`). It also says that the
worker probe is a `PlacementData` consumer at `ε = ε₀/2`, and that its concrete
bump probe supplies a nonzero slice while firing the main theorem at the honest
time `t = 1/2` (`research/T15/REPORT_376.md:50-66`).

The old r0 summary was not removed: it still says that the module has only
three theorems under assumed transported-support hypotheses and leaves raw
transport as a gap (`research/T15/REPORT_376.md:3-13`). Those statements are
false of r1 and directly contradict the appended completion
(`research/T15/REPORT_376.md:17-22,68-78`).

The mathematical target is the paper's fixed compact `K_*`, the containment
`x₀ + εK_* ⊆ B`, and the three rescalings
(`paper/sections/03-torus.tex:101-118`), followed by the single supported copy
statement, with velocity/pressure used for `t<T`
(`paper/sections/03-torus.tex:120`). The reconciled placement data have the
exact fixed `Kstar`, compactness, packet-carrier, force-projection, scale, and
ball/cube fields (`research/T15/Spec.lean:560-643`). The immediate U3 consumer
quantifies velocity and pressure over **every** real `t<T`, not merely
`t∈Ico 0 T` (`research/T15/Spec.lean:665-685,698-718`).

## 2. What is in Lean

### Declaration audit

All thirteen reported names exist. Their actual statements are:

- `scaledActivation_eq` is the expected window equality
  (`formalization/NSFormalization/Section3/T15/Placement.lean:51-56`).
- `affineImage_compact`, `affineImage_subset_ball`, and
  `ball_subset_interior_cube` have the advertised image/ball/cube statements
  (`formalization/NSFormalization/Section3/T15/Placement.lean:60-83`).
- `scaledVelocity_tsupp_subset` and `scaledPressure_tsupp_subset` take the raw
  `Ico 0 1` slice-support clause, carrier compactness and `carrier ⊆ Kstar`, but
  conclude only for `t∈Ico 0 T`
  (`formalization/NSFormalization/Section3/T15/Placement.lean:100-136`). Their
  proofs correctly reuse `delayed_full_support` and
  `delayed_pressure_support`, whose exact source statements are at
  `formalization/NSFormalization/Source/PacketScaling.lean:335-352,409-426`.
- `scaledForce_tsupp_subset` concludes the advertised affine-image inclusion at
  every real time (`formalization/NSFormalization/Section3/T15/Placement.lean:150-166`).
- The three `*_slice_hasCompactSupport` declarations have exactly
  `HasCompactSupport` conclusions (`formalization/NSFormalization/Section3/T15/Placement.lean:172-203`).
  This is compactness of the corresponding `tsupport`; the proofs correctly use
  a closed subset of the compact affine image.
- The three `*_slice_subset_cube` declarations compose support, `eps_space`,
  and `chartBall_in_cube` as claimed
  (`formalization/NSFormalization/Section3/T15/Placement.lean:212-264`).

The rescaling used in these statements is faithful: `scaledVelocity`,
`scaledPressure`, and `scaledForce` have the paper's inverse spatial scale and
the powers `ε⁻¹`, `ε⁻²`, `ε⁻³`
(`formalization/NSFormalization/Section3/T15/Bridges.lean:56-76`), and the rfl
bridges to the upstream parabolic definitions are at
`formalization/NSFormalization/Section3/T15/Bridges.lean:106-125`. The cited
Section 4 precedent really does prove the velocity slice result on `Ico 0 T`
(`formalization/NSFormalization/Section4/I03/Energy.lean:195-204`).

### Blocking fidelity findings

1. **The velocity/pressure placement API is too narrow for the stated U2
   consumer.** Every velocity/pressure support, compact-support, and cube
   theorem requires `t∈Ico 0 T`
   (`formalization/NSFormalization/Section3/T15/Placement.lean:105,127,178,190,222,241`).
   The report calls this “exactly the paper's `t<T`”
   (`research/T15/REPORT_376.md:33-35`), but it silently adds `0≤t`. U3's exact
   fields quantify over every real `t<T`
   (`research/T15/Spec.lean:671-685,704-718`), so the shipped U2 theorem cannot
   directly discharge its negative-time cases. `PlacementData.eps_time`
   supplies the missing positivity of `T-ε²`
   (`research/T15/Spec.lean:631-636`); before activation the existing tree lemma
   makes the velocity slice empty
   (`formalization/NSFormalization/Section4/I02/Support.lean:67-78`), and the
   generic scalar version is available through `zeroPast_dilate_early`
   (`formalization/NSFormalization/Source/PacketScaling.lean:300-305`). Thus
   this is missing composition in this lane, not a missing analytic lemma.

2. **The force support clause is not verbatim and is unused.**
   `PacketAPI.force_support` is
   `CompactPositiveTimeSupport force`
   (`verification/Contracts/V1/Packet.lean:210-214`), defined as both
   `HasCompactSupport f` and positive-time support
   (`verification/Contracts/V1/Packet.lean:132-135`). The lane theorem instead
   accepts only `_hf : HasCompactSupport f` and never uses it
   (`formalization/NSFormalization/Section3/T15/Placement.lean:150-166`). The
   report incorrectly identifies the packet field itself with
   `HasCompactSupport f` (`research/T15/REPORT_376.md:36-41`). Passing the raw
   packet clause verbatim reproduces this error in
   `research/T15/probes/rev376_contract_shape.lean:12-19`:

   ```text
   ../research/T15/probes/rev376_contract_shape.lean:19:51: error: Application type mismatch: The argument
     hf
   has type
     NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f
   but is expected to have type
     HasCompactSupport ?m.38
   in the application
     scaledForce_tsupp_subset hε hKstar_compact hf
   ```

   The worker probe hides the mismatch by projecting `.1`
   (`research/T15/probes/placement_closes.lean:80-85`). This violates the
   brief's verbatim raw-clause requirement and the review requirement against
   unused mathematical binders.

3. **The claimed non-vacuity application is actually a zero slice.** For
   `T=1`, `ε=1/2`, activation is `t₀=3/4`. The worker proves a nonzero value at
   `t=1` (`research/T15/probes/rev376_nonvacuity.lean:55-62`), which is outside
   the main theorem's `Ico 0 1` window, then invokes the main theorem at
   `t=1/2` (`research/T15/probes/rev376_nonvacuity.lean:64-80`), before
   activation. The reviewer probe checks that the latter slice is zero
   (`research/T15/probes/rev376_honest_nonvacuity.lean:31-34`). It also supplies
   the correct non-vacuity check: the same bump is nonzero at `t=7/8` and the
   lane theorem applies to that exact slice
   (`research/T15/probes/rev376_honest_nonvacuity.lean:36-59`). This confirms
   the theorem itself is satisfiable, but the report's description of the
   shipped probe is false.

4. **`placement_closes` is not an instantiation from a `PlacementData P`, nor
   an explicit raw placement witness.** It takes arbitrary
   `chartCenter`, `x₀`, `chartRadius`, `ε₀`, `T`, `Kstar` and all needed
   containments as separate hypotheses
   (`research/T15/probes/placement_closes.lean:40-52`); two purported placement
   fields are deliberately unused (`_hchartRadius_pos`, `_hε₀_le`, lines 43 and
   50). Its derived conclusions are valid, but it establishes neither an
   actual `PlacementData` consumer nor the deliverable's fallback “raw data with
   explicit numbers.”

### Negative mutation and hygiene

The substantive mutation doubles the spatial scale in the main velocity
conclusion (`research/T15/probes/rev376_negative.lean:7-19`). It fails for the
expected `ε` versus `2ε` image mismatch:

```text
../research/T15/probes/rev376_negative.lean:19:2: error: Type mismatch
  scaledVelocity_tsupp_subset hε hcarrier_compact hvel hcarrier_subset ht
has type
  (tsupport fun x => scaledVelocity u ?m.62 T ε (t, x)) ⊆ (fun y => ?m.62 + ε • y) '' Kstar
but is expected to have type
  (tsupport fun x => scaledVelocity u x₀ T ε (t, x)) ⊆ (fun y => x₀ + (2 * ε) • y) '' Kstar
```

No changed Lean file contains `sorry`, `admit`, `axiom`, `native_decide`, or
`maxHeartbeats`. The sole changed formalization module is new; no existing
formalization module was modified. All thirteen declarations print exactly
`[propext, Classical.choice, Quot.sound]`.

## 3. Gaps

Required fixes before acceptance:

1. Add velocity and pressure support/compact-support/cube wrappers for every
   `t<T`, consuming `PlacementData.eps_time` (or its exact raw clause), with a
   negative-time/pre-activation branch; keep the current `Ico 0 T` lemmas as
   internal helpers if desired.
2. Make the public force declarations accept the verbatim
   `CompactPositiveTimeSupport f` clause and use it honestly (for example via
   `parabolicForce_support hf.1`), then pass `P.force_support` rather than
   `P.force_support.1`; alternatively isolate a minimal no-`hf` core lemma and
   expose a verbatim packet-facing wrapper with no dead binder.
3. Replace `placement_closes` by an actual
   `BlowupDensity.T15.Draft.PlacementData P` consumer, or by the permitted
   fallback with explicit raw geometric data. Make the nonzero theorem
   application use an active presingular time such as `t=7/8`, as demonstrated
   by the reviewer probe.
4. Rewrite `REPORT_376.md` as one accurate four-part report: remove the stale
   r0 claims, state the exact time domains and force hypothesis, and describe
   the probe that actually exists.

The lane report's only remaining “not in the tree” claim is that a concrete
`PlacementData` inhabitant is deferred to U15
(`research/T15/REPORT_376.md:68-78`). The required whole-Section4 search was:

```text
$ rg -n 'PlacementData|chartBall_in_cube|eps_space|Kstar|Kstar_compact|carrier_subset|force_projection_subset|fundamentalCube.*Metric.ball|Metric.ball.*fundamentalCube' formalization/NSFormalization/Section4
<0 output>
$ rg -n 'delayed_full_support|delayed_pressure_support|parabolicForce_support|scaled_slice_hasCompactSupport|scaled_smoothOn' formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/I03/Energy.lean:181:theorem scaled_smoothOn ...
formalization/NSFormalization/Section4/I03/Energy.lean:193:  slice_contDiff_of_slab (scaled_smoothOn hP x₀ hε) ht
formalization/NSFormalization/Section4/I03/Energy.lean:197:theorem scaled_slice_hasCompactSupport ...
formalization/NSFormalization/Section4/I03/Energy.lean:201:  have hsupp := delayed_full_support ...
formalization/NSFormalization/Section4/I03/Energy.lean:320:      (scaled_slice_hasCompactSupport ...)
formalization/NSFormalization/Section4/R42/Assembly.lean:85:  obtain ⟨y, hy, rfl⟩ := parabolicForce_support ...
```

This supports only the narrow claim that Section4 has no assembled T15
placement witness. It also confirms that the support-transport ingredients
themselves are already present, as the corrected r1 report says.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`; every `lake` command
was run from `verification/` with `LEAN_NUM_THREADS=6`.

### Module build

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Placement
build_exit=0
build_lines=82
⚠ [8778/9168] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
...
ℹ [9874/9897] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [9891/9897] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
Build completed successfully (9897 jobs).
```

The build succeeds, but it is not literally silent: all 82 lines are replayed
upstream diagnostics; none is from `Placement.lean`.

### Direct typechecks and probes

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T15/Placement.lean
module_exit=0
<0 output>
$ LEAN_NUM_THREADS=6 lake env lean ../research/T15/probes/placement_closes.lean
placement_closes_exit=0
<0 output>
$ LEAN_NUM_THREADS=6 lake env lean ../research/T15/probes/rev376_nonvacuity.lean
rev376_nonvacuity_exit=0
<0 output>
$ LEAN_NUM_THREADS=6 lake env lean ../research/T15/probes/rev376_honest_nonvacuity.lean
EXIT=0
<0 output>
```

The negative mutation exits 1 with the scale mismatch pasted above. The
verbatim-force-clause shape probe also exits 1 with the application mismatch
pasted above; that second failure is the reproducing error for this verdict.

### Axiom audit

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T15/axioms_u2.lean
'NSFormalization.Section3.T15.scaledActivation_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.affineImage_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.affineImage_subset_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.ball_subset_interior_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.scaledVelocity_tsupp_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.scaledPressure_tsupp_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.scaledForce_tsupp_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.scaledVelocity_slice_hasCompactSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.scaledPressure_slice_hasCompactSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.scaledForce_slice_hasCompactSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.scaledVelocity_slice_subset_cube' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.scaledPressure_slice_subset_cube' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.scaledForce_slice_subset_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
axioms_exit=0
```

### Repository check

`make check` exited 0. Its exact head/tail (47,563 lines total) were:

```text
$ LEAN_NUM_THREADS=6 make check
make_check_exit=0
make_check_lines=47563
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 611,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
...
      "NavierStokes.WaveEdgeExtension",
      "NavierStokes.WaveEnvelopeTransport",
      "NavierStokes.WaveInteractionBounds",
      "NavierStokes.WaveStateRegularity",
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.Localization"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.059s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

### Hygiene and conditional gates

```text
$ git diff --name-status origin/erenup/integration-section3...HEAD
A formalization/NSFormalization/Section3/T15/Placement.lean
A research/T15/ATTEMPTS_U2.md
A research/T15/REPORT_376.md
A research/T15/REVIEW_376-T15-U2-placement.md
M research/T15/T15_SPLIT.md
A research/T15/axioms_u2.lean
A research/T15/probes/placement_closes.lean
A research/T15/probes/rev376_negative.lean
A research/T15/probes/rev376_nonvacuity.lean
$ rg -n '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats' <all changed/reviewer Lean files>
<0 output>
$ git diff --check origin/erenup/integration-section3...HEAD
diff_check_exit=0
```

No file under `verification/` was touched, so the brief's conditional
`scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` commands do
not apply. The unconditional architecture-only `check_contracts.py` invoked by
`make check` passed, as shown above.

---

## Fix note (lane 376 r2, worker)

All three r2 blocking findings are addressed in the rewritten
`Section3/T15/Placement.lean` and probes.

1. **Time domain widened to every `t < T`.** `scaledVelocity_tsupp_subset` and
   `scaledPressure_tsupp_subset` now take `ht : t < T` (not `t ∈ Ico 0 T`),
   matching `velocity_singleCopy`/`pressure_singleCopy`
   (`research/T15/Spec.lean:704-718`). The proof splits at the activation
   `t_ε = T-ε²`: pre-activation (`t ≤ t_ε`) gives an identically zero slice via
   `Source.PacketScaling.zeroPast_dilate_early` (`scaled*_slice_eq_zero`,
   `tsupport_subset_of_slice_zero`); the active window (`t_ε < t < T`) has source
   time in `(0,1)` and uses `parabolic_support`/`dilate_support`. All
   `*_slice_hasCompactSupport` and `*_slice_subset_cube` velocity/pressure
   wrappers likewise take `t < T`.

2. **Verbatim force clause, used.** `scaledForce_tsupp_subset` (and the force
   compact-support/cube wrappers) now take
   `NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f`, and the proof
   uses `hf.1` through `Source.PacketScaling.parabolicForce_support`. No `_hf`
   dead binder remains. `research/T15/probes/rev376_contract_shape.lean` (the
   reviewer's reproducing error) now typechecks (EXIT 0).

3. **Concrete active-time probe.** `research/T15/probes/placement_closes.lean` is
   rewritten as an explicit geometric instance (bump velocity/pressure supported
   in `closedBall 0 (1/4)`, `x₀ = chartCenter = (1/2,1/2,1/2)`, chart radius
   `3/8`, `ε₀ = 1`, `T = 1`). It proves `pc_chartBall_in_cube` and `pc_eps_space`
   and fires the velocity/pressure cube + compact-support lemmas at the **active**
   time `t = 7/8`, plus a genuinely nonzero velocity slice there. The reviewer's
   `rev376_honest_nonvacuity.lean` and `rev376_contract_shape.lean` are kept
   (with the `ht : ... < 1` adaptation for the new signature) and committed;
   `rev376_nonvacuity.lean`'s final example is relabelled as the pre-activation
   zero-slice case, and `rev376_negative.lean`'s hypothesis is `t < T` so its
   only failure is the intended `ε` vs `2ε` scale mismatch.

4. **REPORT rewritten.** `research/T15/REPORT_376.md` is a single accurate
   four-part report (stale r0/r1 claims removed), stating the exact time domains
   and the verbatim force hypothesis.

All 16 declarations depend on exactly `[propext, Classical.choice, Quot.sound]`;
module builds with 0 errors/0 warnings; `make check` passes.
