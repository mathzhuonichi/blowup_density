ACCEPT

## 1. What the lane claims

The worker report claims five public deliverables: the concrete `correctionData`, its definitional correction identity, the T17 `correctionForce`, the force-transport theorem `force_eq`, and periodicity of that force (`research/T17/REPORT_373.md:5-14`). It also claims the supporting translation, germ-locality, vanishing, and support lemmas listed there (`research/T17/REPORT_373.md:13-14`). Those claims match the declarations in the submitted module:

- `correctionData` is exactly `localPotentialData v x₀ T θ η O θR ε₀` (`formalization/NSFormalization/Section3/T17/Transport.lean:244-246`), and `correctionData_correction` states exactly
  `(correctionData ...).correction ε = latticeLift (physicalCorrection v x₀ T θ η ε)` (`formalization/NSFormalization/Section3/T17/Transport.lean:250-253`). This agrees definitionally with T16's witness (`formalization/NSFormalization/Section3/T16/Assembly.lean:405-413`).
- `correctionForce` has exactly the Spec's five terms, in the same order (`formalization/NSFormalization/Section3/T17/Transport.lean:255-266`; `research/T17/Spec.lean:723-733`). The paper defines `H_ε` as `∂ₜw_ε - νΔw_ε + (v·∇)w_ε + (w_ε·∇)v + (w_ε·∇)w_ε` (`paper/sections/03-torus.tex:218-225`). The local operator spelling therefore has the requested mathematical content. Section 4's source operator swaps only the two middle additive terms (`formalization/NSFormalization/Source/Insertion.lean:91-95`), and `correctionForce_eq_source` states and proves their equality (`formalization/NSFormalization/Section3/T17/Transport.lean:268-274`).
- `force_eq` has the exact reported concrete identity and explicitly lists periodicity, local smoothness, cutoff smoothness/compact support/support, disjoint-copy geometry, and scale hypotheses (`formalization/NSFormalization/Section3/T17/Transport.lean:278-291`). These are the pointwise versions of the T16 hypotheses used to obtain smoothness and support (`formalization/NSFormalization/Section3/T16/Assembly.lean:157-164`, `formalization/NSFormalization/Source/PhysicalRemoval.lean:56-60`) and the single-copy reduction (`formalization/NSFormalization/Section3/T16/LatticeLift.lean:136-166`).
- `correctionForce_periodic` states `IsPeriodicOn univ` for exactly the concrete force under the same hypotheses (`formalization/NSFormalization/Section3/T17/Transport.lean:403-415`), using the unconditional lift periodicity theorem (`formalization/NSFormalization/Section3/T16/LatticeLift.lean:127-132`).
- The report's supporting declarations all exist with the described statements: the four operator translation laws (`formalization/NSFormalization/Section3/T17/Transport.lean:64-140`), force germ congruence and translation (`formalization/NSFormalization/Section3/T17/Transport.lean:142-189`), force vanishing/support (`formalization/NSFormalization/Section3/T17/Transport.lean:191-237`), and smoothness of the applied spatial derivative (`formalization/NSFormalization/Section3/T17/Transport.lean:92-101`). Their model tree lemmas are the cited T16 `spatialDivergence_translate` (`formalization/NSFormalization/Section3/T16/LatticeLift.lean:179-190`), `latticeLift_sliceSupport` (`formalization/NSFormalization/Section3/T16/LatticeLift.lean:273-324`), and `isPeriodicOn_sub_latticeVector` (`formalization/NSFormalization/Section3/T16/LatticeLift.lean:328-341`). The cited Section 4 slice congruence also exists (`formalization/NSFormalization/Section4/I02/Reference.lean:54-63`).

No hidden named `Prop` input was introduced. Every hypothesis of `force_eq` is visible and used in its proof: smoothness/support build `hWcd` and `hWtsupp` (`formalization/NSFormalization/Section3/T17/Transport.lean:293-301`), the radius bounds isolate one copy (`formalization/NSFormalization/Section3/T17/Transport.lean:302-335`), and periodicity/local smoothness identify the two reference cross-terms (`formalization/NSFormalization/Section3/T17/Transport.lean:337-378`). `O` and `ε₀` are intentionally metadata fields of `CutoffData`; the correction projection is definitionally independent of them in T16 (`formalization/NSFormalization/Section3/T16/Assembly.lean:410-413`), so their absence from the proof is not a vacuity device. There are no ENNReal exponents or interval-valued conclusions here, hence no `⊤.toReal = 0` issue. The inequalities are jointly satisfiable on a nonempty cylinder and positive-radius ball in the reviewer probe (`research/T17/probes/rev373_nonvacuity.lean:23-41`), with a genuinely nonzero periodic reference (`research/T17/probes/rev373_nonvacuity.lean:14-21`).

## 2. What is in Lean

The implementation proves the transport identity pointwise. Inside a periodic copy it obtains a neighborhood germ equal to one translate and reduces both sides to the central copy (`formalization/NSFormalization/Section3/T17/Transport.lean:313-378`). Outside every copy it proves both forces vanish (`formalization/NSFormalization/Section3/T17/Transport.lean:379-401`). This is mathematically the requested locality/translation route and avoids cross-copy terms in the nonlinear advection.

Hygiene is clean. The lane changes exactly one formalization path, and that path is new relative to the base:

```text
$ git diff --name-only origin/erenup/integration-section3...HEAD -- formalization
formalization/NSFormalization/Section3/T17/Transport.lean
$ git cat-file -e origin/erenup/integration-section3:formalization/NSFormalization/Section3/T17/Transport.lean
fatal: path 'formalization/NSFormalization/Section3/T17/Transport.lean' does not exist in 'origin/erenup/integration-section3'
```

The complete lane diff is:

```text
formalization/NSFormalization/Section3/T17/Transport.lean
research/T17/ATTEMPTS_U2.md
research/T17/REPORT_373.md
research/T17/T17_SPLIT.md
research/T17/axioms_u2.lean
research/T17/probes/transport_closes.lean
```

Forbidden-token and heartbeat scans returned no matches:

```text
forbidden_rg_exit=1
heartbeat_rg_exit=1
```

This covers `sorry`, `admit`, `axiom`, `native_decide`, and `maxHeartbeats` in the submitted module, probe, and axiom file. The submitted axiom file audits eight central theorems (`research/T17/axioms_u2.lean:8-15`); an exhaustive reviewer audit covers all fifteen definitions/theorems (`research/T17/probes/rev373_axioms_all.lean:3-17`), and every one prints exactly `[propext, Classical.choice, Quot.sound]`.

## 3. Gaps

There is no mathematical U2 gap. The report's only assembly note is that `correctionData` currently takes plain `x₀ T`, with a `PlacementData` projection wrapper deferred (`research/T17/REPORT_373.md:18-19`). That is explicitly allowed by the lane brief while canonical formalization-side `PlacementData` is unavailable. The required whole-tree checks produced no relevant pre-existing replacement:

```text
$ grep -RIn 'PlacementData' formalization/NSFormalization/Section4
(no output)
$ grep -RIn 'PlacementData' formalization/NSFormalization/Section3/T15
(no output)
$ grep -RInE 'structure PlacementData|def PlacementData|theorem force_eq|correctionData' \
    formalization/NSFormalization/Section3/T16 formalization/NSFormalization/Source \
    formalization/NSFormalization/Section4/I02 formalization/NSFormalization/Paper1/Correction*.lean
(no output)
```

The reviewer mutation changes the main conclusion by flipping the sign of the transported force (`research/T17/probes/rev373_mutation.lean:14-29`). Lean rejects it at the application of the real theorem, rather than because an argument was removed:

```text
../research/T17/probes/rev373_mutation.lean:27:2: error: Type mismatch
  force_eq hv hvsm hθsm hηsm hθcs hηcs hθsupp hηsupp hr2 hε hεspace hεtime
has type
  correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε =
    latticeLift (NSFormalization.Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε))
but is expected to have type
  correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε =
    -latticeLift (NSFormalization.Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε))
```

## 4. Commands and results

All `lake` commands were run from `verification/` after loading `../scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

`lake build NSFormalization.Section3.T17.Transport` exited 0. Its exact output was the following; every warning is replayed from an upstream module, and there is no warning from `Transport.lean`:

```text
⚠ [8778/9167] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9321/9361] Replayed NSFormalization.Source.RealSobolev
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
  Complex.smul_re

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_im]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused:
  Complex.smul_im

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_re]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9325/9361] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9332/9361] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9335/9361] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9345/9361] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9348/9361] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9360/9361] Replayed NSFormalization.Section3.T16.Assembly
warning: NSFormalization/Section3/T16/Assembly.lean:327:12: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: NSFormalization/Section3/T16/Assembly.lean:332:11: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Section3/T16/Assembly.lean:362:11: `if_pos` has been deprecated: Use `ite_eq_left` instead
Build completed successfully (9361 jobs).
```

Direct elaboration of the submitted module and probe both exited 0 with zero output:

```text
$ lake env lean ../formalization/NSFormalization/Section3/T17/Transport.lean
(no output)
$ lake env lean ../research/T17/probes/transport_closes.lean
(no output)
```

The submitted axiom audit exited 0 with exactly:

```text
'NSFormalization.Section3.T17.correctionData_correction' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.correctionForce_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.force_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.correctionForce_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.source_force_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.source_correctionForce_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.source_correctionForce_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.spatialLaplacian_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The exhaustive reviewer axiom audit also exited 0; all fifteen printed the same three axioms. The concrete full-theorem non-vacuity probe exited 0 with zero output:

```text
$ lake env lean ../research/T17/probes/rev373_nonvacuity.lean
(no output)
```

`make check` exited 0. The exact captured output is 45,708 lines because `check_contracts.py` emits its closure JSON; its exact head and tail are:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 604,
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
...
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.PacketImport"
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
45 work items: ownership, contract registration and task cards consistent.
```

No path under `verification/` appears in `git diff --name-only origin/erenup/integration-section3...HEAD`, so the brief's conditional `scripts/gates.sh` and `check_contracts.py --base-ref origin/erenup/integration-section3` gates do not apply. (`make check` nevertheless ran the ordinary architecture-mode `check_contracts.py`, as shown above.)

Fixes: none.
