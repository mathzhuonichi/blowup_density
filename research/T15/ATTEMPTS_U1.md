# T15 U1 attempts and result (lane 362)

## Target

U1 is the canonical, definitions-only rescaling layer for `prop:scaling`.
The formalization module must not import `Contracts.*`; contract-facing
spellings are checked from a separate research probe.

## Successful route

1. Imported T10 `PeriodicData`, T13 `Localization`, the upstream parabolic
   scaling source, and the vendor periodizer.
2. Copied the T15 rescaling definitions over the canonical field types:
   `scaledStartTime`, `scaledSourcePoint`, `scaledVelocity`,
   `scaledPressure`, `scaledForce`, `alphaT`, the three periodized fields,
   and `normalizedScaledPressure`.
3. Proved the three rescaling bridges by `rfl` to
   `Source.parabolicVelocity`, `Source.parabolicPressure`, and
   `Source.parabolicForce`.  These are the upstream objects named by
   `Bindings/Correction.lean` and `Bindings/Scaling.lean` for the registered
   `scaledPacket`, `scaledPressure`, and `scaledForce`.
4. Proved the normalized-pressure formula by `rfl` through T10's
   `normalizePressureT`, and the lane-352 spatial-slice periodizer bridge by
   `rfl` to `NavierStokes.PeriodicLocalization.periodize`.
5. Retained the two completed-density drift checks using the canonical B01/D01
   vocabulary.  The homogeneous registered spelling has no separately named
   upstream declaration, so the module carries the exact copied abbreviation
   `completedDenseHomogeneous` and bridges it to its `CompletedDenseVia` form.
6. The probe copies the Spec's packet-specific definitions and checks every
   copy against the canonical module by `rfl`; it also checks the three
   contract spellings and `Contracts.V1.alpha` against the module.

## Resolved issues

The first draft accidentally shadowed T10's `pressureMeanT` and used an
unqualified `SpaceTimeField`, which produced type errors.  Removing the local
mean definition, explicitly opening A02's canonical field types, and using
T10's `normalizePressureT` made the definitions definitionally identical.
The vendor bridge must compare a spatial field to the vendor's spacetime
periodizer at `(t, x)`; the pointwise statement is exactly `rfl`.

## Gaps

U1 does not inhabit any `ScalingAPI` field.  Placement, summability and
single-copy arguments, torus/Euclidean norm bridges, PDE transport, solution
assembly, Sobolev bounds, convergence, and non-vacuity remain in U2--U15.
The contract's `alpha` is a copied contract definition rather than an
upstream declaration, so the canonical theorem is the formula theorem;
the contract equality is checked in the probe.
