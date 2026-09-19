# T15 U11 attempts — `solution` assembly

## Successful route

The nine raw `scalingStatement` clauses needed by U11 are exactly the union of
the U8–U10 inputs:

1. compactness of the common carrier;
2. velocity slice support in that carrier;
3. pressure slice support in that carrier;
4. compact positive-time support of the force;
5. force vanishing at nonpositive times;
6. smoothness of the past-zero velocity on `Iio 1 ×ˢ univ`;
7. smoothness of the past-zero pressure on `Iio 1 ×ˢ univ`;
8. the past-zero momentum equation below time one;
9. past-zero incompressibility below time one.

No raw force-smoothness, original (unextended) smoothness, initial-value,
energy, blow-up, quiet-time, or named-input clause is needed.

`periodizedVelocity_contDiffOn` supplies velocity smoothness.  The same U9
periodization helper applied to the pressure rescaling supplies raw pressure
smoothness.  The remaining normalization issue is not a new parametric
integral proof: `Paper1.integral_torusLift` identifies `pressureMeanT` with the
cube mean, after which
`Paper1.PeriodicPressureNormalization.normalizedPressure_contDiffOn` gives
joint smoothness on the half-open slab, including time zero.  Vendor
`unitSpatialPeriodsOn_periodize` gives both raw periods, and subtracting the
spatially constant mean preserves the pressure periods.

The constructor then uses U8 for `initial`, `divergence`, and `momentum`; U9
for `sobolev` and `pressure_gradient`; U10 for `pressure_gauge`; and the new
smoothness/periodicity lemmas for the remaining fields.  Its horizon proof
uses `place.eps_time place.ε₀ ⟨place.eps_pos, le_rfl⟩`, rather than the
redundant `place.time_pos` field.

## Resolved elaboration failures

The first build exposed unresolved aliases.  `SpaceTimeScalar` and
`SpatialField` had not been opened from `Section4.A02`, so Lean introduced
implicit type variables and reported:

```text
error: NSFormalization/Section3/T15/Solution.lean:30:23: Application type mismatch: The argument
  q
has type
  SpaceTimeScalar
but is expected to have type
  Section4.A02.SpaceTimeScalar
in the application
  normalizePressureT q

error: NSFormalization/Section3/T15/Solution.lean:120:26: failed to synthesize instance of type class
  OfNat SpatialField 0
```

Opening `NSFormalization.Section4.A02 (SpatialField SpaceTimeScalar)` fixed
both aliases; the next build passed.

The first registered-packet probe used the two extension-field names in the
wrong order.  Lean reported:

```text
../research/T15/probes/solution_closes.lean:135:57: error(lean.invalidField): Invalid field `extension_velocity_smooth`: The environment does not contain `BlowupDensity.Contracts.V1.PacketAPI.extension_velocity_smooth`
../research/T15/probes/solution_closes.lean:136:11: error(lean.invalidField): Invalid field `extension_pressure_smooth`: The environment does not contain `BlowupDensity.Contracts.V1.PacketAPI.extension_pressure_smooth`
```

The canonical fields are `velocity_extension_smooth` and
`pressure_extension_smooth`.  After correcting them, the probe passed with
zero output.

## Final status

No proof, statement, non-vacuity, axiom, or gate gap remains.  No named input,
placeholder, heartbeat override, or forbidden proof primitive was introduced.
