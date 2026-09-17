ACCEPT

# Review 283 — T10 canonical periodic-data module

## 1. What the lane claims

The worker claims a complete definitions-only realization of amended
`research/T10/Spec.lean`, excluding only `TorusDataAPI`, plus a verbatim API
probe and definitional reuse of the five existing `Paper1.TorusCube` objects
(`research/T10/REPORT_283.md:5-20`).  That claim is accurate.

Statement fidelity checks:

- The plan chooses physical unit-periodic fields on `R³`, coefficient analysis
  on `lp (Fin 3 → ℤ) 2`, and the D01 datum architecture
  (`collaboration/SECTION3_PLAN.md:14-18`).  The module implements precisely this:
  the reused torus layer is at
  `formalization/NSFormalization/Section3/T10/PeriodicData.lean:35-44`, physical
  periodicity is at `:49-56`, and the coefficient carriers are at `:60-94`.
- The paper specifies the squared inhomogeneous weight
  `1 + 4π²|k|²`, the Fourier coefficient convention, componentwise vector
  norms, and the homogeneous zero-mode convention at
  `paper/sections/01-introduction.tex:80-107`.  The matching Lean definitions
  occur at `PeriodicData.lean:60-68`, `:102-112`, and `:153-174`.
- The paper defines `X_T`, `F_T`, compact positive-time support, periodic
  velocity/pressure, the zero-mean pressure gauge, lifespan, and breakdown at
  `paper/sections/02-preliminaries.tex:7-46`; the corresponding declarations are
  at `PeriodicData.lean:226-253` and `:257-317`.
- The paper's periodic Leray symbol is identity at `k = 0` and
  `I - k⊗k/|k|²` otherwise (`paper/sections/02-preliminaries.tex:75-87`).
  The coefficient formula and graph predicate have exactly that form at
  `PeriodicData.lean:178-206`.
- The paper's energy quantity is
  `L∞(0,T;L²) + L²(0,T;L²)` of the gradient
  (`paper/sections/01-introduction.tex:141-150`).  The physical and coefficient
  spellings use the open interval `Ioo 0 T` at `PeriodicData.lean:319-348`.
- Lead amendment 1 requires Haar integrability in both datum predicates and an
  extra physical `MemLp 2` premise in `parseval_forward`
  (`research/T10/RECONCILIATION.md:28-55`).  Those conjuncts are present at
  `PeriodicData.lean:100-106`, `:162-169`, and
  `research/T10/probes/api_on_canonical.lean:61-73`.

No hypothesis was silently added to make a claim vacuous.  There is no
`.toReal` inequality in this layer; the norms remain `ℝ≥0∞`.  The half-open/open
solution intervals are guarded by `horizon_pos : 0 < T`
(`PeriodicData.lean:257-277`), and the API restriction field separately requires
`0 < S` (`api_on_canonical.lean:241-254`).  The `s` index of
`PeriodicSobolev` is intentionally phantom and explicitly documented as such
(`PeriodicData.lean:86-94`); it is not a theorem hypothesis.  A reviewer
non-vacuity probe constructs `IsPeriodicDatum s 0 0` for every real `s` and a
concrete nonempty slab `Ioo 0 1`
(`research/T10/probes/rev283_nonvacuity.lean:11-30`).

## 2. What is in Lean

There are 50 named declarations in the module, exactly the 51 named
declarations in `Spec.lean` minus `TorusDataAPI`.  The two anonymous contract
abbreviation examples at `research/T10/Spec.lean:33-42` are not module
declarations and are correctly excluded, as documented at
`research/T10/CANONICAL.md:66-70`.

Exact comparison results:

```text
$ diff [Spec.lean:63-70] [PeriodicData.lean:49-56]
<no output>
$ sha256sum [the two periodicity blocks]
568cd3dede624f756f31dcf7aac641c207bdaa13c6974daae790fd477c3b7502  -
568cd3dede624f756f31dcf7aac641c207bdaa13c6974daae790fd477c3b7502  -

$ diff [comment-stripped Spec declarations periodicFrequencyWeight through
  coefficientEnergyENormT] [the corresponding canonical declarations]
<no output>
$ sha256sum [those two normalized declaration blocks]
1c969575f6af0a8e4c756cd95d93c21d02e8ab1caed822223978beff5c0f1d1d  -
1c969575f6af0a8e4c756cd95d93c21d02e8ab1caed822223978beff5c0f1d1d  -

$ diff [Spec.lean:438-674] [api_on_canonical.lean:34-270]
<no output>
$ sha256sum [the two TorusDataAPI blocks]
cdb6f56f387ef8fa82d3958e1c10328e4c9e3d96f490c0d659f7e21a813d8033  -
cdb6f56f387ef8fa82d3958e1c10328e4c9e3d96f490c0d659f7e21a813d8033  -
```

The five exceptions are genuine reuse, not drift.  Their source declarations
are `formalization/NSFormalization/Paper1/TorusCube.lean:20-26` and `:75-77`,
and all five identifications are checked by `rfl` at
`research/T10/probes/api_on_canonical.lean:13-26`.  The imported field
abbreviations and sole local `ClassicalSolutionR` restatement are in
`formalization/NSFormalization/Section4/A02/SolutionClass.lean:61-76` and
`:112-147`, imported through `Section4/A02/Restrict.lean:1`; the contract-to-A02
fieldwise conversion evidence is at `verification/Bindings/Uniqueness.lean:59-83`.
The gradient source is the contract-identical definition at
`formalization/NSFormalization/Section4/I02/Energy.lean:36-46`, with its `rfl`
bridge at `verification/Bindings/Correction.lean:88-91`.

Hygiene is clean.  The committed delta contains only new files:

```text
$ git diff --name-only origin/erenup/integration-section3...HEAD
formalization/NSFormalization/Section3/T10/PeriodicData.lean
research/T10/ATTEMPTS_CANONICAL.md
research/T10/CANONICAL.md
research/T10/REPORT_283.md
research/T10/probes/api_on_canonical.lean
```

`rg` over those five files found no whole-word `sorry`, `admit`, `axiom`, or
`native_decide`; it also found no `maxHeartbeats`/`set_option` in either Lean
deliverable and no `Contracts.*` or `Bindings.*` import in the formalization
module.  `git diff --check origin/erenup/integration-section3...HEAD` produced
zero output.  Citations checked above match the paper and source tree.

## 3. Gaps

No blocking mathematical, statement, build, axiom, or hygiene gap was found.

The worker's only missing-path report is accurate:

```text
$ test -e verification/Bindings/Data.lean
verification/Bindings/Data.lean: absent
```

The distributed bridge replacements are identified at
`research/T10/CANONICAL.md:72-89` and exist at the cited binding locations.
Neither `REPORT_283.md` nor `CANONICAL.md` declares any lemma to be "not in the
tree"; `REPORT_283.md:28` explicitly says there is no requested mathematical
gap.  Therefore the mandatory whole-`Section4` missing-lemma grep has no target
and is not applicable.  The older future-work inventory in
`research/T10/COMPARISON.md:92-148` is a proof-lane plan, not a claim that those
lemmas are absent from the tree and not a deliverable of this definitions lane.

The substantive negative check changes the paper's Bessel coefficient from
`4` to `5` (`research/T10/probes/rev283_negative_weight.lean:10-16`).  It fails
for the intended reason, not from a dropped argument:

```text
../research/T10/probes/rev283_negative_weight.lean:16:2: error: Tactic `rfl` failed: The left-hand side
  periodicFrequencyWeight k
is not definitionally equal to the right-hand side
  1 + 5 * Real.pi ^ 2 * ∑ i, ↑(k i) ^ 2

k : PeriodicFrequency
⊢ periodicFrequencyWeight k = 1 + 5 * Real.pi ^ 2 * ∑ i, ↑(k i) ^ 2
```

Reviewer-only probes added under the allowed prefix are
`rev283_axioms.lean`, `rev283_nonvacuity.lean`, and
`rev283_negative_weight.lean`.  No lane Lean module or worker record was edited.

## 4. Commands and results

All Lake commands were run from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

### Canonical module build

Command:

```text
. ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.PeriodicData
```

Exit code `0`; exact output:

```text
⚠ [8778/9208] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9318/9352] Replayed NSFormalization.Source.RealSobolev
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
⚠ [9322/9352] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9329/9352] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9332/9352] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9342/9352] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9345/9352] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (9352 jobs).
```

Every warning is replayed from an upstream module; none points into
`Section3/T10/PeriodicData.lean`.

### Direct elaboration and API probe

```text
$ lake env lean ../formalization/NSFormalization/Section3/T10/PeriodicData.lean
<zero output; exit 0>
$ lake env lean ../research/T10/probes/api_on_canonical.lean
<zero output; exit 0>
$ lake env lean ../research/T10/probes/rev283_nonvacuity.lean
<zero output; exit 0>
```

### Axiom audit

The audit file is `research/T10/probes/rev283_axioms.lean:1-55`.
`PeriodicFrequency = Fin 3 → ℤ` is axiom-free; every `#print axioms` in the
file produced exactly the required triple.  Exit code `0`; exact output:

```text
'NSFormalization.Section3.T10.PeriodicTorus' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.periodicTorusMeasure' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.torusLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.periodicFourierCoeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.IsPeriodicSpatial' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.IsPeriodicOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.periodicFrequencyWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.PeriodicScalarData' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.PeriodicVectorData' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.realPeriodicSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.PeriodicSobolev' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.periodicSobolevDataNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.IsPeriodicDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.periodicSobolevENorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.meanT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.constantPartT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.meanZeroPartT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.meanDecompositionT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.meanZeroPeriodicSobolev' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.IsMeanZeroT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.periodicAngularFrequencySq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.homogeneousDatumWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.IsPeriodicHomogeneousDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.periodicHomogeneousENorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.periodicDerivativeSymbol' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.IsSolenoidalPeriodicDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.periodicLeray' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.IsPeriodicLerayDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.IsPeriodicReweight' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.IsPeriodicSobolevPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.forceSobolevENormT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.initialClassT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.MemForceT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.forceClassT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.pressureMeanT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.PressureGaugeT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.normalizePressureT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.ClassicalSolutionT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.maximalLifespanT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.RegularThroughT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.breakdownSetInT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.breakdownSetT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.RelativelyDenseT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.energyEssSupT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.energyGradientT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.energyENormT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.coefficientEnergyEssSupT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.coefficientEnergyGradientT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.coefficientEnergyENormT' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Repository gate

Command from the worktree root:

```text
. scripts/lean-env.sh && LEAN_NUM_THREADS=6 make check
```

Exit code `0`.  The full mechanically generated output is 42,730 lines /
1,759,574 bytes with SHA-256
`0d2b93e5a4515c42f98b3fb0ccfdcb58939c24c08c4833a3a33e09bd0cca6414`.
To avoid embedding 42,000 contract-closure entries, here are the exact first
and last 24 lines:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 551,
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
… [42,682 generated closure lines omitted; hash above] …
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
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The copied-source `BoundaryCorollary.lean:90` entry is pre-existing and outside
the all-new committed delta shown above; it is informational in this gate.

`scripts/gates.sh` and
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
were not required: the conditional trigger is a change under `verification/`,
and the committed name-only delta contains none.
