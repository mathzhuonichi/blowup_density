# T15 U10 attempts — pressure normalization

Lane 447, 2026-09-19.  Targets: the literal
`ScalingAPI.pressureSlice_integrable` field and the
`ClassicalSolutionT.pressure_gauge` obligation for
`normalizedScaledPressure`.

## Route that closed

1. `scaledPressure_slice_contDiff` transports the raw packet clause
   `ContDiffOn ℝ ∞ (zeroPastField p) (Iio 1 ×ˢ univ)` through the exact
   parabolic pressure rescaling.  The window identity
   `(T-ε²)+((ε⁻¹)²)⁻¹=T` puts every `t<T` slice inside that slab.
2. Placement gives
   `tsupport (scaledPressure ... (t,·)) ⊆ interior fundamentalCube`.
   `supportedInCube_of_tsupport_subset_interior` and the vendor theorem
   `contDiff_periodize` turn the lattice sum into a smooth (hence continuous)
   real spatial function.  `T13.latticeVector_eq_lattice` is the necessary
   propositional bridge between the two otherwise identical lattice embeddings.
3. The canonical representative map used by `torusLift` is only measurable,
   not continuous.  Complexification plus `Paper1.memLp_torusLift` gives an
   honest `L¹` lift; taking `Complex.re` proves the required real-valued
   `Integrable` statement.
4. `normalizePressureT_pressureGauge` expands the normalization, applies
   `integral_sub` using that integrability guard, and uses `integral_const`
   together with `measure_univ = 1`.  `pressure_gauge` composes this algebraic
   lemma with `pressureSlice_integrable` on `Ico 0 place.T`.

No named input, placeholder, goal alias, new axiom, or heartbeat override was
introduced.

## Failed approaches and exact errors

### 1. Wrong parabolic-window exponent and unavailable slice helper

The first draft accidentally inverted `((ε⁻¹)²)²` instead of `(ε⁻¹)²`, and
referred to an I03 helper not imported by the closure.  Lean reported:

```text
error: NSFormalization/Section3/T15/Pressure.lean:42:60: unsolved goals
p : PressureField
x₀ : Space
T ε t : ℝ
hε : 0 < ε
hp : ContDiffOn ℝ ∞ (zeroPastField p) (Iio 1 ×ˢ univ)
ht : t < T
h :
  ContDiffOn ℝ ∞ (Source.dilateField (ε⁻¹ ^ 2) (ε⁻¹ ^ 2) ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField p))
    (Iio (T - ε ^ 2 + (ε⁻¹ ^ 2)⁻¹) ×ˢ univ)
⊢ T - ε ^ 2 + ε ^ 4 = T

error: NSFormalization/Section3/T15/Pressure.lean:45:9: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  T - ε ^ 2 + ((ε⁻¹ ^ 2) ^ 2)⁻¹
in the target expression
  ContDiffOn ℝ ∞ (Source.dilateField (ε⁻¹ ^ 2) (ε⁻¹ ^ 2) ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField p))
    (Iio (T - ε ^ 2 + (ε⁻¹ ^ 2)⁻¹) ×ˢ univ)

error: NSFormalization/Section3/T15/Pressure.lean:46:8: Unknown identifier `NSFormalization.Section4.I03.slice_contDiff_of_slab`
```

The same draft left the constant time coordinate of a composition ambiguous:

```text
error: NSFormalization/Section3/T15/Pressure.lean:85:19: don't know how to synthesize implicit argument `f`
⊢ Space → SpaceTime

error: NSFormalization/Section3/T15/Pressure.lean:85:32: don't know how to synthesize implicit argument `f`
⊢ Space → ℝ

error: NSFormalization/Section3/T15/Pressure.lean:85:47: don't know how to synthesize placeholder
⊢ ℝ

error: NSFormalization/Section3/T15/Pressure.lean:85:9: failed to infer `have` declaration type
```

This was fixed by proving the standard slice-composition argument locally and
giving the composite function the explicit point `((0 : ℝ), x)`.

### 2. Vendor and T13 lattice vectors are propositionally, not definitionally, equal

After the periodizer proof itself closed, `simpa` could not cross the two
lattice-vector spellings:

```text
error: NSFormalization/Section3/T15/Pressure.lean:95:4: Type mismatch: After simplification, term
  hslice
 has type
  @ContDiff ℝ DenselyNormedField.toNontriviallyNormedField Space (PiLp.normedAddCommGroup 2 fun x => ℝ)
    (PiLp.normedSpace 2 ℝ fun x => ℝ) ℝ Real.normedAddCommGroup RCLike.toInnerProductSpaceReal.toNormedSpace ∞ fun x =>
    ∑' (n : NavierStokes.PeriodicLocalization.Lattice),
      scaledPressure p place.x₀ place.T ε (t, x - NavierStokes.PeriodicLocalization.lattice n)
but is expected to have type
  @ContDiff ℝ DenselyNormedField.toNontriviallyNormedField Space (PiLp.normedAddCommGroup 2 fun x => ℝ)
    (PiLp.normedSpace 2 ℝ fun x => ℝ) ℝ Real.normedAddCommGroup RCLike.toInnerProductSpaceReal.toNormedSpace ∞ fun x =>
    ∑' (n : PeriodicFrequency), scaledPressure p place.x₀ place.T ε (t, x - latticeVector n)
```

Adding `latticeVector_eq_lattice` to the restricted simplification set closes
the bridge without unfolding either lattice definition.

### 3. Mean-zero goal needed the canonical mean unfolded explicitly

After `integral_sub` and `integral_const`, a bare `rfl` did not unfold
`pressureMeanT`:

```text
error: NSFormalization/Section3/T15/Pressure.lean:133:2: Tactic `rfl` failed: The left-hand side
  ∫ (a : PeriodicTorus),
      torusLift (fun x => periodizedScaledPressure p place.x₀ place.T ε (t, x)) a ∂periodicTorusMeasure -
    pressureMeanT (periodizedScaledPressure p place.x₀ place.T ε) t
is not definitionally equal to the right-hand side
  0
```

`unfold pressureMeanT; exact sub_self _` closes the residual statement.

### 4. An unqualified local scalar-field name became an auto-implicit type

The first factoring of the gauge algebra used `SpaceTimeScalar` without
opening its canonical A02 namespace.  Lean therefore treated it as a new type
parameter and reported:

```text
error: NSFormalization/Section3/T15/Pressure.lean:127:37: Function expected at
  q
but this term has type
  SpaceTimeScalar

error: NSFormalization/Section3/T15/Pressure.lean:128:41: Application type mismatch: The argument
  q
has type
  SpaceTimeScalar
but is expected to have type
  Section4.A02.SpaceTimeScalar
in the application
  normalizePressureT q

error: NSFormalization/Section3/T15/Pressure.lean:132:53: Application type mismatch: The argument
  q
has type
  SpaceTimeScalar
of sort `Sort u_1` but is expected to have type
  Section4.A02.SpaceTimeScalar
of sort `Type` in the application
  pressureMeanT q
```

Opening `NSFormalization.Section4.A02 (SpaceTimeScalar)` fixes the intended
canonical type.

### 5. Concrete probe: normalization is slicewise even when the placement-only packet is not time-smooth

The concrete pressure from `placement_closes.lean` is time-independent, so its
past-zero extension is deliberately not smooth at `t=0`.  Proving each scaled
spatial slice smooth by splitting on its source time initially used a source
time with a syntactically different inverse-power form and an underconstrained
smul composition.  Lean reported:

```text
../research/T15/probes/pressure_closes.lean:143:61: error: unsolved goals
ε t : ℝ
hs : 0 < ε⁻¹ ^ 2 * (t - (1 - ε ^ 2))
x : Space
⊢ (ε ^ 2)⁻¹ * (t - (1 - ε ^ 2)) ≤ 0 → ε = 0 ∨ ↑pcBump (ε⁻¹ • (x - pcCenter)) = 0

../research/T15/probes/pressure_closes.lean:149:28: error: Application type mismatch: The argument
  ContDiff.smul contDiff_const (ContDiff.sub contDiff_id contDiff_const)
has type
  ContDiff ?m.207 ?m.215 ((fun x => ?m.172) • fun x => id x - ?m.216)
but is expected to have type
  ContDiff ℝ ∞ fun x => ε⁻¹ • (x - pcCenter)
```

The attempted `rwa [inv_pow]` was oriented the wrong way:

```text
../research/T15/probes/pressure_closes.lean:143:11: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ?a⁻¹ ^ ?n
in the target expression
  0 < (ε ^ 2)⁻¹ * (t - (1 - ε ^ 2))

../research/T15/probes/pressure_closes.lean:154:11: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ?a⁻¹ ^ ?n
in the target expression
  ¬0 < (ε ^ 2)⁻¹ * (t - (1 - ε ^ 2))
```

Using `simpa only [inv_pow] using hs` and a separately typed affine-map
`ContDiff` fact closes both branches.  Removing `pcPres` from the active-branch
simplifier was also invalid and produced the exact residual:

```text
../research/T15/probes/pressure_closes.lean:145:61: error: unsolved goals
ε t : ℝ
hs : 0 < ε⁻¹ ^ 2 * (t - (1 - ε ^ 2))
hs' : 0 < (ε ^ 2)⁻¹ * (t - (1 - ε ^ 2))
x : Space
⊢ pcPres ((ε ^ 2)⁻¹ * (t - (1 - ε ^ 2)), ε⁻¹ • (x - pcCenter)) = ↑pcBump (ε⁻¹ • (x - pcCenter)) ∨ ε = 0
```

The final probe unfolds `pcPres` only in that active branch and has zero
output.

## Audit

`research/T15/axioms_u10.lean` prints exactly
`[propext, Classical.choice, Quot.sound]` for all five declarations in the
module.
