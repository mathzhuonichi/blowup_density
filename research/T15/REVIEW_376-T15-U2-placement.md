ACCEPT-WITH-NOTES

## 1. What the lane claims

The final r2 report claims 16 declarations proving the U2 placement chain for
the canonical rescaled velocity, pressure, and force: slice support in
`(fun y => x₀ + ε • y) '' Kstar`, its containment in the chart ball and then
`interior fundamentalCube`, and compact support of every relevant slice
(`research/T15/REPORT_376.md:3-55`). It claims the exact consumer domains
`t < T` for velocity/pressure and every `t : ℝ` for force
(`research/T15/REPORT_376.md:23-47`).

That is the requested mathematics. The paper chooses one compact `K_*`
covering the packet carrier and the spatial projection of the force support,
requires `x₀ + εK_* ⊆ B`, defines the three inverse-scale rescalings, and then
states that the torus sees one supported copy
(`paper/sections/03-torus.tex:101-120`). The reconciled raw data are exactly
`Kstar_compact`, `carrier_subset`, `force_projection_subset`, and `eps_space`,
with `chartBall_in_cube` providing the strict cube containment
(`research/T15/Spec.lean:560-643`). The immediate consumers quantify over all
`t < T` for velocity/pressure and all real `t` for force
(`research/T15/Spec.lean:704-729`).

## 2. What is in Lean

### Statement-fidelity audit

All 16 reported declarations exist. Their source statements agree with the
final report:

- `scaledActivation_eq`, the zero-slice helper, and the three affine/cube
  geometry declarations are at
  `formalization/NSFormalization/Section3/T15/Placement.lean:52-92`.
- The pre-activation velocity and pressure slices are identically zero at
  `formalization/NSFormalization/Section3/T15/Placement.lean:96-111`.
- `scaledVelocity_tsupp_subset` takes `0 < ε`, compact `carrier`, the verbatim
  `Ico 0 1` velocity-support clause, `carrier ⊆ Kstar`, and `t < T`, and has the
  claimed affine-image conclusion
  (`formalization/NSFormalization/Section3/T15/Placement.lean:128-157`).
- `scaledPressure_tsupp_subset` has the same exact shape for pressure
  (`formalization/NSFormalization/Section3/T15/Placement.lean:165-195`).
- `scaledForce_tsupp_subset` takes the verbatim
  `CompactPositiveTimeSupport f`, compact `Kstar`, and the raw spatial
  projection clause, for every `t : ℝ`
  (`formalization/NSFormalization/Section3/T15/Placement.lean:207-227`). The
  hypothesis is used through `parabolicForce_support hf.1` at line 222; it is
  not a dead named premise. The packet contract spells the same force,
  compact-carrier, velocity-support, and pressure-support clauses at
  `verification/Contracts/V1/Packet.lean:206-225`.
- The three `HasCompactSupport` declarations are exactly at
  `formalization/NSFormalization/Section3/T15/Placement.lean:231-264`; this is
  precisely compactness of the corresponding `tsupport`.
- The three strict-cube inclusions have the reported `eps_space` and
  `chartBall_in_cube` hypotheses and the correct time domains at
  `formalization/NSFormalization/Section3/T15/Placement.lean:271-325`.

The definitions being transported are also faithful to the paper: the source
point uses `ε⁻¹` in space and `(ε⁻¹)^2` in time, while the three amplitudes are
`ε⁻¹`, `ε⁻²`, and `ε⁻³`
(`formalization/NSFormalization/Section3/T15/Bridges.lean:57-76`). Their `rfl`
bridges to `parabolicVelocity`, `parabolicPressure`, and `parabolicForce` are at
`formalization/NSFormalization/Section3/T15/Bridges.lean:108-125`.

The proof route is genuine rather than a repackaged goal. The active branches
use the existing `parabolic_support` and scalar `dilate_support`
(`formalization/NSFormalization/Source/PacketScaling.lean:186-206,393-405`),
and the force branch uses the spacetime support transport
(`formalization/NSFormalization/Source/PacketScaling.lean:525-548`). The cited
Section 4 precedent really supplies the analogous velocity compact-slice
result (`formalization/NSFormalization/Section4/I03/Energy.lean:178-204`).
The U3 tree lemmas do consume chart-ball support in the advertised manner
(`formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean:306-352`),
while HaarBridge accepts the stronger direct interior support form
(`formalization/NSFormalization/Section3/T15/HaarBridge.lean:149-158`).

No `⊤.toReal = 0`, totalized norm, or empty-interval shortcut occurs here.
The explicit bump probe uses `ε = ε₀/2 = 1/2`, active time `t = 7/8`, proves
the geometric containments, and proves the scaled velocity is nonzero at the
center (`research/T15/probes/placement_closes.lean:74-98,103-134`). The
reviewer non-vacuity probe independently applies the main support theorem to
that active nonzero slice
(`research/T15/probes/rev376_honest_nonvacuity.lean:36-59`).

### Negative check and hygiene

The substantive mutation changes the main velocity conclusion from scale
`ε` to `2 * ε` (`research/T15/probes/rev376_negative.lean:7-19`). It fails at
exactly that changed constant:

```text
../research/T15/probes/rev376_negative.lean:19:2: error: Type mismatch
  scaledVelocity_tsupp_subset hε hcarrier_compact hvel hcarrier_subset ht
has type
  (tsupport fun x => scaledVelocity u ?m.57 T ε (t, x)) ⊆ (fun y => ?m.57 + ε • y) '' Kstar
but is expected to have type
  (tsupport fun x => scaledVelocity u x₀ T ε (t, x)) ⊆ (fun y => x₀ + (2 * ε) • y) '' Kstar
```

The changed/reviewer Lean files contain no `sorry`, `admit`, `axiom`,
`native_decide`, or `maxHeartbeats`. The only changed formalization module is
new, so no existing module was modified. All 16 declarations have exactly the
required transitive axioms.

## 3. Gaps and notes

The report's only deferred mathematical item is constructing a full
`PlacementData` witness for the selected abstract packet
(`research/T15/REPORT_376.md:77-87`). That is explicitly assigned to U15
(`research/T15/T15_SPLIT.md:172-181`), not U2. The required whole-Section4
search confirms the narrow claim:

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

Three documentation-only fixes remain; none changes a theorem or proof:

1. At `research/T15/probes/rev376_contract_shape.lean:7-10`, replace the stale
   failure comment by the exact one-line comment
   `/- Reviewer shape check: the theorem accepts CompactPositiveTimeSupport f verbatim; this application must typecheck without projecting .1. -/`.
2. At `research/T15/probes/placement_closes.lean:8-11`, replace the claim that
   the geometry realizes every `PlacementData` field by
   `This permitted raw-data fallback realizes the U2-relevant geometric hypotheses with concrete numbers; it is not a full PlacementData witness.`
   In particular, with `T = ε₀ = 1`, the full `eps_time` field would be false at
   `ε = 1`; the probe does not use or claim that field in Lean.
3. At `research/T15/REPORT_376.md:63-65`, replace “fires the velocity/pressure
   cube+compact-support lemmas” by “fires the velocity cube and compact-support
   lemmas and the pressure cube lemma”; the actual conjunction is exactly
   `research/T15/probes/placement_closes.lean:103-121`.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, from `verification/`,
with `LEAN_NUM_THREADS=6`.

### Build and direct checks

`LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Placement` exited 0.
It emitted 82 lines, all replayed diagnostics from pre-existing upstream
modules; `Placement.lean` emitted no diagnostic. Exact head and tail:

```text
⚠ [8778/9106] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [insert, coord]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9835/9897] Replayed NSFormalization.Source.RealSobolev
...
⚠ [9859/9897] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9862/9897] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
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

Each of the following exited 0 with exactly zero output:

```text
lake env lean ../formalization/NSFormalization/Section3/T15/Placement.lean
lake env lean ../research/T15/probes/placement_closes.lean
lake env lean ../research/T15/probes/rev376_contract_shape.lean
lake env lean ../research/T15/probes/rev376_honest_nonvacuity.lean
lake env lean ../research/T15/probes/rev376_nonvacuity.lean
```

The axioms file exited 0 with this exact output:

```text
'NSFormalization.Section3.T15.scaledActivation_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.tsupport_subset_of_slice_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.affineImage_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.affineImage_subset_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.ball_subset_interior_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.scaledVelocity_slice_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.scaledPressure_slice_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
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
```

### Repository gate

`LEAN_NUM_THREADS=6 make check` exited 0. Its output had 47,563 lines; per the
repository review-log rule, here are the exact head and tail rather than the
full generated contract closure:

```text
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
[47,523 generated middle lines omitted]
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
Ran 13 tests in 0.181s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The copied-source `BoundaryCorollary.lean` notice is pre-existing and outside
the lane; the changed-file token scan is empty.

### Diff and conditional gates

```text
$ git diff --name-status origin/erenup/integration-section3...HEAD
A formalization/NSFormalization/Section3/T15/Placement.lean
A research/T15/ATTEMPTS_U2.md
A research/T15/REPORT_376.md
A research/T15/REVIEW_376-T15-U2-placement.md
M research/T15/T15_SPLIT.md
A research/T15/axioms_u2.lean
A research/T15/probes/placement_closes.lean
A research/T15/probes/rev376_contract_shape.lean
A research/T15/probes/rev376_honest_nonvacuity.lean
A research/T15/probes/rev376_negative.lean
A research/T15/probes/rev376_nonvacuity.lean
$ rg -n '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats' <changed/reviewer Lean files>
<0 output>
$ git diff --check origin/erenup/integration-section3...HEAD
<0 output; exit 0>
$ git diff --name-only origin/erenup/integration-section3...HEAD | rg '^verification/'
<0 output; exit 1>
```

No `verification/` file was touched. Therefore the brief's conditional
`scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates do not
apply; the unconditional architecture check run by `make check` passed.
