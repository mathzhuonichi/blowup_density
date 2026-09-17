ACCEPT

## 1. What the lane claims

The worker reports three exact `TorusDataAPI` field proofs and four reusable
bridge lemmas (`research/T10/REPORT_284.md:5-34`), with no residual hypothesis or
gap (`research/T10/REPORT_284.md:48-59`). It also claims a zero-field
non-vacuity check (`research/T10/REPORT_284.md:45-46`) and standard axioms for
all seven declarations (`research/T10/REPORT_284.md:73-75`).

Those are the right obligations for this lane. The physical representation is
the repository's explicit choice to keep fields on `Space = R³` and bridge them
to `UnitAddTorus (Fin 3)` (`collaboration/SECTION3_PLAN.md:14-18`). The paper's
torus context is at `paper/sections/03-torus.tex:1-4`; its actual mean removal is
at `paper/sections/03-torus.tex:395-411`.

## 2. What is in Lean

### Statement fidelity

| Claimed declaration | Implementation | Required statement/evidence | Result |
|---|---:|---:|---|
| `torusLift_injective` | `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:65` | `research/T10/probes/api_on_canonical.lean:95` | Exact binders, hypotheses, and conclusion. |
| `torusLift_surjective` | `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:74` | `research/T10/probes/api_on_canonical.lean:107` | Exact binders, witness, conjunction, and equality. |
| `mean_decomposition` | `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:95` | `research/T10/probes/api_on_canonical.lean:119` | Exact binders and both conjuncts. |
| `periodic_shift_int` | `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:30` | lane brief's exported integer-shift lemma | Exact requested shift `sum i, (k i : Real) • coordinateVector i`. |
| `torusLift_apply_of_periodic` | `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:44` | lane brief's quotient-evaluation lemma | Exact quotient image and pointwise equality. |
| `isPeriodicSpatial_torusLift_comp` | `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:52` | lane brief's pullback lemma | Pullback of every torus field is periodic. |
| `meanT_const` | `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:90` | lane brief's constant-mean lemma | Exact normalized mean identity. |

The lane's conformance examples repeat all three API fields and all four bridge
signatures (`research/T10/probes/physical_bridge_closes.lean:14-48`). The API
mean definitions are literal Bochner integral, constant mean, subtraction of
the mean, and equality of the resulting mean to zero
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:116-149`), matching
the paper's definitions `bar g`, `m`, `v = u-m`, and `h = g-bar g`
(`paper/sections/03-torus.tex:395-401`).

The cited reuse is accurate. Integer lattice invariance is already proved at
`formalization/NSFormalization/Paper1/FourierReconstructionAdapter.lean:27-45`,
quotient-fiber constancy at `:47-62`, and evaluation of the canonical lift at
every physical point at `:64-73`. The lift itself uses the `(0,1]^3`
representative (`formalization/NSFormalization/Paper1/TorusCube.lean:20-26`).
Mathlib defines the measurable equivalence at
`verification/.lake/packages/mathlib/Mathlib/Analysis/Fourier/AddCircleMulti.lean:146-166`
and explicitly normalizes `UnitAddCircle` Haar measure to a probability measure
at `:27-38`; the finite product instance is what closes `meanT_const`.

No hypothesis is vacuous. Both periodicity hypotheses are used by injectivity
(`PhysicalBridge.lean:68-71`); surjectivity quantifies over an arbitrary entire
torus function (`PhysicalBridge.lean:75-85`); and mean decomposition assumes
actual Bochner integrability rather than an `ENNReal.toReal` or empty-domain
guard (`PhysicalBridge.lean:95-109`). The periodicity binder in
`mean_decomposition` is intentionally named `_hz` and is logically redundant
for this elementary integral identity (`PhysicalBridge.lean:100`), but it is
present because the API requires it; it neither makes the theorem vacuous nor
constitutes a silently added premise.

The worker's zero instance is at
`research/T10/probes/physical_bridge_closes.lean:50-60`. The stronger reviewer
probe supplies a concrete nonzero constant field, proves it is nonzero, and
discharges periodicity and integrability
(`research/T10/probes/rev284_nonvacuity.lean:16-33`).

### Hygiene

`git diff --name-status origin/erenup/integration-section3...HEAD` reports only
five added files; no pre-existing module is modified:

```text
A	formalization/NSFormalization/Section3/T10/PhysicalBridge.lean
A	research/T10/ATTEMPTS_PHYSICAL_BRIDGE.md
A	research/T10/REPORT_284.md
A	research/T10/axioms_physical_bridge.lean
A	research/T10/probes/physical_bridge_closes.lean
```

The whole-word prohibited-token/heartbeat scan over all lane Lean files and
review probes produced no output. `git diff --check
origin/erenup/integration-section3...HEAD` also produced no output. There is no
`maxHeartbeats` setting. `git diff --name-only ... -- verification` produced no
output, so the conditional `scripts/gates.sh` and base-ref contract gate do not
apply to this lane.

## 3. Gaps

There is no correctness or interface gap in this lane. The report makes no
"not in the tree" claim, so the mandatory Section4 missing-lemma search is not
triggered. As an additional check, searching the complete
`formalization/NSFormalization/Section4` tree for the five relevant bridge/main
names produced no output; the reused facts are instead present at the cited
Paper1 locations above.

The substantive mutation flips the reconstruction target from `z` to `-z`
(`research/T10/probes/rev284_mutation.lean:16-21`). It is not an argument-dropping
test. Lean rejects reuse of the real theorem with exactly the expected mismatch:

```text
../research/T10/probes/rev284_mutation.lean:21:2: error: Type mismatch
  mean_decomposition
has type
  ∀ (z : SpatialField),
    IsPeriodicSpatial z →
      Integrable (torusLift z) periodicTorusMeasure →
        (∀ (x : Space), constantPartT z x + meanZeroPartT z x = z x) ∧ IsMeanZeroT (meanZeroPartT z)
but is expected to have type
  ∀ (z : SpatialField),
    IsPeriodicSpatial z →
      Integrable (torusLift z) periodicTorusMeasure →
        (∀ (x : Space), constantPartT z x + meanZeroPartT z x = -z x) ∧ IsMeanZeroT (meanZeroPartT z)
```

The passing companion probe additionally proves this mutation genuinely false
for `coordinateVector 0`, rather than merely incompatible with this proof
(`research/T10/probes/rev284_nonvacuity.lean:35-46`).

## 4. Commands and results

All commands used `. scripts/lean-env.sh` (spelled `../scripts/lean-env.sh` from
`verification/`), ran Lake only from `verification/`, and used
`LEAN_NUM_THREADS=6`.

1. Module build:

```text
$ cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.PhysicalBridge
⚠ [8778/9129] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9320/9355] Replayed NSFormalization.Source.RealSobolev
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
⚠ [9324/9355] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9331/9355] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9334/9355] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9344/9355] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9347/9355] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (9355 jobs).
```

Exit code 0. Every warning is replayed from a pre-existing dependency; there is
no `PhysicalBridge` warning.

2. Direct elaboration:

```text
$ cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T10/PhysicalBridge.lean
```

Exit code 0, exactly zero output.

```text
$ cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake env lean ../research/T10/probes/physical_bridge_closes.lean
```

Exit code 0, exactly zero output.

3. Axiom audit:

```text
$ cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake env lean ../research/T10/axioms_physical_bridge.lean
'NSFormalization.Section3.T10.periodic_shift_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.torusLift_apply_of_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.isPeriodicSpatial_torusLift_comp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T10.torusLift_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.torusLift_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.meanT_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.mean_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit code 0. Every declaration has exactly the allowed set.

4. Repository check:

```text
$ . scripts/lean-env.sh && LEAN_NUM_THREADS=6 make check
```

Exit code 0. The full output is the repository's 439,894-character contract
closure manifest; following `logs/LESSONS.md`, it is not pasted wholesale. An
exact 30-line tail from a second exit-0 run is:

```text
      "NavierStokes.ValidDyadicBandCover",
      "NavierStokes.VariableGaugeMean",
      "NavierStokes.ViscousPropagator",
      "NavierStokes.VolterraAnalyticBounds",
      "NavierStokes.VolterraParity",
      "NavierStokes.VolterraRegularity",
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
      "Tests.CompletedDensity"
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

The full run also reports the known repository baseline
`Paper1/BoundaryCorollary.lean:90` token and `source_hashes_match: false`; neither
file is changed by this lane.

5. Reviewer probes:

```text
$ cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake env lean ../research/T10/probes/rev284_nonvacuity.lean
```

Exit code 0, exactly zero output.

```text
$ cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake env lean ../research/T10/probes/rev284_mutation.lean
```

Exit code 1 with the expected sign-mismatch diagnostic pasted in Part 3.

Required fixes: none.
