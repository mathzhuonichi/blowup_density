# T10 physical bridge attempts (lane 284)

## Repository search and successful route

Before deciding whether a bridge lemma was absent, searches covered all paths
required by the lane brief:

- `formalization/NSFormalization/Paper1/TorusCube.lean`;
- `formalization/NSFormalization/Paper1/Periodic*.lean`;
- `formalization/NSFormalization/Section4/D01/`;
- Mathlib's `Analysis/Fourier/AddCircleMulti.lean`,
  `Analysis/Fourier/AddCircle.lean`, `MeasureTheory/Group/AddCircle.lean`, and
  `Analysis/Normed/Lp/lpSpace.lean` in
  `verification/.lake/packages/mathlib/Mathlib/`.

`TorusCube.lean` supplies the canonical `(0,1]³` lift and the Haar/cube
integration bridge.  `AddCircleMulti.lean` supplies
`UnitAddTorus.measurableEquivPiIoc`, its two inverse identities, and the product
probability-measure construction.  The required arbitrary-point quotient
bridge was already proved in
`formalization/NSFormalization/Paper1/FourierReconstructionAdapter.lean`:

- `unitPeriods_integer_translate` proves invariance under every integer
  lattice shift by combining the three coordinate periods;
- `unitPeriods_eq_of_torus_eq` proves constancy on quotient fibers using
  `AddCircle.coe_eq_zero_iff`;
- `torusLift_coe_of_unitPeriods` evaluates the canonical lift at the quotient
  image of every physical point.

`PhysicalBridge.lean` exports these facts in canonical T10 vocabulary as
`periodic_shift_int` and `torusLift_apply_of_periodic`.  Surjectivity uses the
explicit pullback `x ↦ Z (fun i ↦ (x i : UnitAddCircle))`; its lift is `Z`
by `measurableEquivPiIoc.symm_apply_apply`.  Mean normalization uses Mathlib's
probability instance for the finite product of unit additive circles.

There is no residual named hypothesis.  In particular, none of the three API
fields was weakened or made conditional on an auxiliary bridge premise.

## Failed elaborations and exact diagnostics

The first direct check preceded building the newly landed canonical module:

```text
../formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:1:0: error: object file '/data_8T/ping/blowup_density/.claude/worktrees/284-T10-physical-bridge/formalization/.lake/build/lib/lean/NSFormalization/Section3/T10/PeriodicData.olean' of module NSFormalization.Section3.T10.PeriodicData does not exist
```

After building `PeriodicData`, the imported reconstruction adapter likewise
needed its object file built once:

```text
../formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:1:0: error: object file '/data_8T/ping/blowup_density/.claude/worktrees/284-T10-physical-bridge/formalization/.lake/build/lib/lean/NSFormalization/Paper1/FourierReconstructionAdapter.olean' of module NSFormalization.Paper1.FourierReconstructionAdapter does not exist
```

The first integer-shift wrapper used `convert h using 1`; `convert` generated
an equality in the result type `E`, so `ext` was applied to the wrong goal:

```text
../formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:36:2: error: No applicable extensionality theorem found for type
  E

Note: Extensionality theorems can be registered by marking them with the `[ext]` attribute
../formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:58:28: warning: This simp argument is unused:
  Pi.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [coordinateVector, hji]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:87:67: error: unsolved goals
c : Space
⊢ ∫ (y : PeriodicTorus), Paper1.torusLift (fun x => c) y ∂periodicTorusMeasure = c
```

Resolution: first prove the shift-vector equality in `Space`, rewrite by that
equality, and then apply the existing theorem.  The unused simplifier argument
was removed.  The constant-mean proof now explicitly unfolds the underlying
`Paper1.torusLift`, allowing the probability-measure simplifier to apply.

An intermediate cube-integral proof did not yet tell the simplifier the unit
cube's product volume:

```text
../formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:90:67: error: unsolved goals
c : Space
⊢ volume.real (Icc 0 1) • c = c
```

That route is mathematically valid using `Real.volume_Icc_pi`, but became
unnecessary once the product probability instance was exposed directly.

The first probe run occurred before the new module had been built:

```text
../research/T10/probes/physical_bridge_closes.lean:1:0: error: object file '/data_8T/ping/blowup_density/.claude/worktrees/284-T10-physical-bridge/formalization/.lake/build/lib/lean/NSFormalization/Section3/T10/PhysicalBridge.olean' of module NSFormalization.Section3.T10.PhysicalBridge does not exist
```

Finally, the concrete zero-field probe asked `simp` to prove integrability, but
the lift had not been unfolded:

```text
../research/T10/probes/physical_bridge_closes.lean:60:4: error: `simp` made no progress
```

Resolution: use Mathlib's `integrable_zero` directly; definitional reduction
identifies the lifted zero field.

## Trust and non-vacuity

The conformance file prints exactly
`[propext, Classical.choice, Quot.sound]` for all seven exported theorems.  The
probe instantiates `mean_decomposition` with the concrete zero spatial field,
including actual periodicity and integrability proofs.
