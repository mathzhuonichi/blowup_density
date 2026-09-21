ACCEPT

## 1. What the lane claims

The worker claims a definitions-only U1 module: ten T15 rescaling/periodization
definitions, six bridge/formula theorems, and the two completed-density drift
checks (`research/T15/REPORT_362.md:5-27`).  It also claims that the conformance
probe copies the packet-specialized Spec definitions token-for-token and checks
the four registered contract spellings by `rfl`
(`research/T15/REPORT_362.md:31-40`).  It explicitly does not claim any U2--U15
analytic result or a `ScalingAPI` witness (`research/T15/REPORT_362.md:42-50`).

These are accurate claims.  There are no hidden hypotheses: the bridge
theorems quantify only over their data and have no premises
(`formalization/NSFormalization/Section3/T15/Bridges.lean:108-147`).  In
particular, there is no positivity assumption, empty interval, or finiteness
assumption that could make a statement vacuous.  The `ENNReal.toReal ⊤ = 0`
endpoint convention occurs openly in the copied formula, not as a hypothesis:
the Spec records it at `research/T15/Spec.lean:545-547`, the contract records it
at `verification/Contracts/V1/Correction.lean:155-160`, and the module copies
the same expression at
`formalization/NSFormalization/Section3/T15/Bridges.lean:78-79`.

## 2. What is in Lean

Statement fidelity is exact.

- The manuscript defines `t_ε = T - ε²` and the three amplitude/source scalings
  at `paper/sections/03-torus.tex:101-120`, and defines
  `α(p,q) = -3 + 3/p + 2/q` at
  `paper/sections/03-torus.tex:122-138`.  The module definitions are the same
  formulas at
  `formalization/NSFormalization/Section3/T15/Bridges.lean:56-102`.
- The source point is time-first, with time scaled by `(ε⁻¹)²` and space by
  `ε⁻¹`, exactly as the reconciled Spec at `research/T15/Spec.lean:423-449`.
  The module has the same order at
  `formalization/NSFormalization/Section3/T15/Bridges.lean:56-76`.
- The three main bridge statements are precisely
  `scaledVelocity = parabolicVelocity ε⁻¹ (T-ε²) x₀ (zeroPastField u)`,
  `scaledPressure = parabolicPressure ε⁻¹ (T-ε²) x₀ (zeroPastField p)`, and
  `scaledForce = parabolicForce ε⁻¹ (T-ε²) x₀ f`
  (`formalization/NSFormalization/Section3/T15/Bridges.lean:106-125`).  These
  targets are the upstream definitions at
  `formalization/NSFormalization/Source/ParabolicScaling.lean:92-99` and exactly
  the registered bindings at `verification/Bindings/Correction.lean:65-74` and
  `verification/Bindings/Scaling.lean:36-46`.  The registered copied
  definitions themselves are at
  `verification/Contracts/V1/Correction.lean:141-160` and
  `verification/Contracts/V1/Scaling.lean:98-116`.
- The normalized-pressure theorem subtracts the T10 slice mean pointwise
  (`formalization/NSFormalization/Section3/T15/Bridges.lean:132-137`), matching
  the Spec exactly (`research/T15/Spec.lean:485-496`).
- T13's spatial periodizer is the sum in
  `formalization/NSFormalization/Section3/T13/Localization.lean:40-43`; the
  vendor spacetime periodizer is the same sum at
  `vendor/NavierStokesAndEuler/NavierStokes/PeriodicLocalization.lean:57-63`.
  Consequently the pointwise theorem at
  `formalization/NSFormalization/Section3/T15/Bridges.lean:141-147` has the
  correct shape and is genuinely `rfl`.  Lane 352's corresponding theorem is
  `latticeLift_eq_periodize` at
  `formalization/NSFormalization/Section3/T16/LatticeLift.lean:75-79` in commit
  `2f121e8c`; that stacked file is not an ancestor of this lane, but its theorem
  has the same definitional content and is not required as an import here.
- The two completion bridges at
  `formalization/NSFormalization/Section3/T15/Bridges.lean:31-52` match the Spec
  examples at `research/T15/Spec.lean:409-419`.  Their canonical definitions
  are `formalization/NSFormalization/Section4/B01/Compact.lean:83-96` and
  `formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:621-624`.
- Every `example ... := rfl` requested from the Spec occurs at
  `research/T15/Spec.lean:411-419,453-467,493-496,551-552`.  The module promotes
  their upstream/formula forms at
  `formalization/NSFormalization/Section3/T15/Bridges.lean:37-52,108-147`, and
  the direct contract forms occur in
  `research/T15/probes/api_on_canonical.lean:132-159`.
- The packet-specialized definitions in the probe
  (`research/T15/probes/api_on_canonical.lean:47-82`) agree token-for-token with
  `research/T15/Spec.lean:423-489,545-547`; all ten module comparisons are `rfl`
  (`research/T15/probes/api_on_canonical.lean:84-127`).  Thus changing an
  amplitude, sign, source point, or lattice convention would break the probe.

The negative check changes the main force bridge's start time from
`T - ε²` to `T + ε²`
(`research/T15/probes/rev362_mutated_force_time.lean:10-15`).  Lean rejects the
`rfl` proof for exactly that mismatch.  The separate non-vacuity probe uses the
nonzero constant field `coordinateVector 0` and proves that its rescaling at
`ε = 1` is nonzero (`research/T15/probes/rev362_nonvacuity.lean:8-20`).

Hygiene also passes.  The lane adds one formalization module and does not modify
an existing Lean module.  The module does not import `Contracts.*`
(`formalization/NSFormalization/Section3/T15/Bridges.lean:1-6`).  No changed or
review-probe Lean file contains a `sorry`, `admit`, `axiom` declaration, or
`native_decide`; none sets `maxHeartbeats`.  The axiom audit lists every public
declaration in the canonical module
(`research/T15/axioms_u1.lean:13-31`), and each prints exactly
`[propext, Classical.choice, Quot.sound]`.

## 3. Gaps

The reported gap is scoped correctly: this lane supplies only U1 definitions
and drift bridges, while the Spec's analytic fields start with placement and
lattice obligations at `research/T15/Spec.lean:554-738` and continue through
solution, energy, mixed, Sobolev, and convergence fields at
`research/T15/Spec.lean:741-909`.  The status file makes the same limited claim
at `research/T15/T15_SPLIT.md:205-217`.

As required, I searched all of `formalization/NSFormalization/Section4` for the
exact missing T15 names: `PlacementData`, `Kstar_compact`,
`force_projection_subset`, the three `*_summable`, the three `*_singleCopy`,
`packetEnergyIdentity`, `packetDissipationIdentity`, `packetMixedScaling`,
`pressureSlice_integrable`, `forceSobolev_memLp`, `packetSobolevBound`, and
`forceConvergence`.  There were no hits.  Searches for the generic
`ScalingAPI` found only Section 4 comments/references in
`Section4/R42/Lifespan.lean:139`, `Section4/R42/SolutionOnShorter.lean:70`, and
`Section4/D01/ForceClass.lean:410,418`; none is a T15 torus witness or any of the
missing fields.  The gap statement is therefore honest and does not overlook a
same-named Section 4 theorem.

## 4. Commands and results

All `lake` commands were run from `verification/` after
`. scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

`lake build NSFormalization.Section3.T15.Bridges` exited 0.  Its exact output
was the following; every diagnostic is a replayed upstream diagnostic, and
there is no diagnostic from the reviewed module:

```text
⚠ [8778/9303] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9835/9896] Replayed NSFormalization.Source.RealSobolev
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
⚠ [9839/9896] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9846/9896] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9849/9896] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9859/9896] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9862/9896] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
ℹ [9874/9896] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [9891/9896] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
Build completed successfully (9896 jobs).
```

These commands each exited 0 with exactly zero output:

```text
lake env lean ../formalization/NSFormalization/Section3/T15/Bridges.lean
lake env lean ../research/T15/probes/api_on_canonical.lean
lake env lean ../research/T15/probes/rev362_nonvacuity.lean
```

`lake env lean ../research/T15/axioms_u1.lean` exited 0 and printed:

```text
'NSFormalization.Section3.T15.completedDense_eq_via' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.completedDenseHomogeneous' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.completedDenseHomogeneous_eq_via' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.scaledStartTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.scaledSourcePoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.scaledVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.scaledPressure' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.scaledForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.alphaT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.periodizedScaledVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.periodizedScaledPressure' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.periodizedScaledForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.normalizedScaledPressure' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.scaledVelocity_eq_parabolicVelocity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.scaledPressure_eq_parabolicPressure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.scaledForce_eq_parabolicForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.alphaT_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.normalizedScaledPressure_formula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.periodize_eq_vendor' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The deliberate mutation command exited 1 with the expected exact error:

```text
../research/T15/probes/rev362_mutated_force_time.lean:15:2: error: Tactic `rfl` failed: The left-hand side
  scaledForce f x₀ T ε
is not definitionally equal to the right-hand side
  parabolicForce ε⁻¹ (T + ε ^ 2) x₀ f

f : VelocityField
x₀ : Space
T ε : ℝ
⊢ scaledForce f x₀ T ε = parabolicForce ε⁻¹ (T + ε ^ 2) x₀ f
exit_code=1
```

`make check` exited 0.  Its output is 45,708 lines because
`check_contracts.py` prints all registered closures; to avoid reproducing a
1,884,846-byte inventory, here are the exact first 23 and last 24 lines:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 600,
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
[45,661 closure-inventory lines omitted]
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

The pre-existing copied-source `BoundaryCorollary.lean` notice and
`source_hashes_match: false` are inventory data, not failures; `make check`
returned 0.  The lane's exact diff from
`origin/erenup/integration-section3...HEAD` is:

```text
formalization/NSFormalization/Section3/T15/Bridges.lean
research/T15/ATTEMPTS_U1.md
research/T15/COMPARISON.md
research/T15/REPORT_362.md
research/T15/T15_SPLIT.md
research/T15/axioms_u1.lean
research/T15/probes/api_on_canonical.lean
```

No file under `verification/` was touched, so the conditional
`scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates are
not applicable.  `make check` did run the ordinary architecture-only
`check_contracts.py`, whose output above records
`"base_compatibility_checked": false`.  Finally, `git diff --check
origin/erenup/integration-section3...HEAD` exited 0 with no output.

No fixes required.
