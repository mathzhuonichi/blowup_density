# Attempts: T10 datum basics

## Source search

The requested searches covered:

- `formalization/NSFormalization/Paper1/TorusCube.lean`;
- all `formalization/NSFormalization/Paper1/Periodic*.lean` files;
- `formalization/NSFormalization/Section4/D01/`;
- Mathlib's `Analysis/Fourier/AddCircleMulti.lean`,
  `Analysis/Fourier/AddCircle.lean`,
  `MeasureTheory/Group/AddCircle.lean`, and
  `Analysis/Normed/Lp/lpSpace.lean`.

The useful declarations were `lp.single`, `lp.single_apply_self`,
`lp.single_apply_ne`, `WithLp.toLp`, `WithLp.ofLp_injective`,
`UnitAddTorus.orthonormal_mFourier`, `UnitAddTorus.mFourier_zero`,
`MeasureTheory.Integrable.eval_piLp`, `MeasureTheory.eval_integral_piLp`, and
`ContinuousLinearMap.integral_comp_comm`.  There is no
`mFourierCoeff_const` in the searched tree, so
`periodicFourierCoeff_const` was proved from orthonormality.  The only existing
constant-coefficient linearity theorem found was the one-dimensional
`AddCircle.fourierCoeff.add`, not the required multivariate statement.

## Failed paths and exact diagnostics

### 1. Unqualified `SpatialField`

Opening only `NavierStokes.ProblemStatement` left `SpatialField` to
auto-implicit elaboration instead of selecting the A02 abbreviation.  The
first diagnostic was:

```text
error: NSFormalization/Section3/T10/DatumBasics.lean:23:52: Application type mismatch: The argument
  z
has type
  SpatialField
but is expected to have type
  Section4.A02.SpatialField
in the application
  IsPeriodicDatum s z
```

Resolution: explicitly open
`NSFormalization.Section4.A02 (SpatialField)`.

### 2. Trying to unfold the Section3 abbreviation by its Paper1 name

The initial constant-coefficient proof attempted to unfold the reused alias
directly and failed with:

```text
error: NSFormalization/Section3/T10/DatumBasics.lean:47:9: Tactic `unfold` failed to unfold `Paper1.periodicFourierCoeff` in
  periodicFourierCoeff (fun x => c) k = if k = 0 then c else 0
```

Resolution: first `change` the goal to
`UnitAddTorus.mFourierCoeff`, then unfold that definition.

### 3. Treating the coefficient integrand as a syntactic subtraction

Before simplifying scalar multiplication over subtraction, `integral_sub`
reported:

```text
error: NSFormalization/Section3/T10/DatumBasics.lean:68:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∫ (a : ?m.54), ?m.60 a - ?m.61 a ∂?m.59
in the target expression
  ∫ (t : UnitAddTorus (Fin 3)), (UnitAddTorus.mFourier (-k)) t • (fun y => torusLift f y - torusLift g y) t =
    (∫ (t : UnitAddTorus (Fin 3)), (UnitAddTorus.mFourier (-k)) t • torusLift f t) -
      ∫ (t : UnitAddTorus (Fin 3)), (UnitAddTorus.mFourier (-k)) t • torusLift g t
```

Resolution: normalize with `simp only [smul_sub]` first.

### 4. Private local Haar `MeasureSpace` instances

`AddCircleMulti`, `Paper1.TorusCube`, and this module each install a local
normalized-Haar `MeasureSpace UnitAddCircle`.  Their induced product measures
are definitionally equal, but the private instance constants do not unify at
the default elaborator transparency.  A direct use of bounded scalar
multiplication failed with:

```text
error: NSFormalization/Section3/T10/DatumBasics.lean:79:4: Type mismatch: After simplification, term
  Integrable.bdd_smul hf 1 hm hb
 has type
  @Integrable ℂ PseudoMetricSpace.toUniformSpace.toTopologicalSpace SeminormedAddGroup.toContinuousENorm
    (UnitAddTorus (Fin 3)) MeasurableSpace.pi ((fun x => (UnitAddTorus.mFourier (-k)) x) • torusLift f)
    periodicTorusMeasure
but is expected to have type
  @Integrable ℂ PseudoMetricSpace.toUniformSpace.toTopologicalSpace SeminormedAddGroup.toContinuousENorm
    (UnitAddTorus (Fin 3)) MeasureSpace.pi.toMeasurableSpace
    (fun t => (UnitAddTorus.mFourier (-k)) t • torusLift f t) volume
```

Trying to rewrite only the measurable-space instance also failed because the
measure depends on it:

```text
error: NSFormalization/Section3/T10/DatumBasics.lean:77:8: Tactic `rewrite` failed: motive is not type correct:
  fun _a => Integrable (fun t => (UnitAddTorus.mFourier (-k)) t • torusLift f t) volume
Error: Application type mismatch: The argument
  volume
has type
  Measure (UnitAddTorus (Fin 3))
but is expected to have type
  autoParam (Measure (UnitAddTorus (Fin 3))) Integrable._auto_1
```

Resolution: expose `MeasureTheory.MeasureSpace.pi`, put the hypotheses in the
explicit product-Haar spelling, and use `convert ... using 1 <;> rfl`.  Kernel
reduction then identifies both private local instance realizations.  No named
hypothesis remains.

### 5. Running consumers before the module build

The first probe/audit invocation preceded `lake build` and therefore failed
with:

```text
error: object file '.../formalization/.lake/build/lib/lean/NSFormalization/Section3/T10/DatumBasics.olean' of module NSFormalization.Section3.T10.DatumBasics does not exist
```

Resolution: build `NSFormalization.Section3.T10.DatumBasics` before running
the standalone consumer files.

## Final construction

For `meanZero_datum`, the removed mode is

```lean
WithLp.toLp 2 (fun i ↦ lp.single 2 (0 : PeriodicFrequency) (A.1 i 0)).
```

It has conjugate-reflection symmetry because `A.1 i 0` is real under `star`.
Subtracting it stays in `lp 2` automatically.  The zero coefficient is the
coordinate of `meanT z` by `eval_integral_piLp` and
`Complex.ofRealCLM.integral_comp_comm`; all nonzero constant coefficients
vanish by multivariate Fourier orthonormality.

There are no residual hypotheses or proof gaps.
