# T13 contract-registration attempts (lane 379)

The accepted route was direct registration of the reconciled six-field
`LocalizationAPI` from `research/T13/Spec.lean`, using the already registered
`Contracts.V1.TorusData` periodic vocabulary and
`Contracts.V1.HomogeneousNorm.dotHomogeneousENorm`.

## Binding route

The ten T13 definitions newly restated here (`fundamentalCube`,
`SupportedInBall`, `periodize`, `fractionalRadialKernel`, `cFrac`,
`periodicKernel`, `latticeTail`, `IReal`, `ITorus`, and `gradientENorm`) are
definitionally equal to the canonical declarations in
`NSFormalization.Section3.T13`.  `latticeVector` is already owned at the same
root namespace by the frozen `T02.local_potential` V1 contract; its
`WithLp.toLp` body is definitionally equal to T13's
`EuclideanSpace.equiv.symm` spelling, so importing that contract and adding the
T13-specific `localization_latticeVector_eq` drift guard avoids two incompatible
owners for the same fully qualified declaration.  The co-import probe in
`research/T13/probes/contract_coimport.lean` checks this explicitly.

Whole-function `rfl` bridges elaborate for all eleven vocabulary definitions;
no pointwise bridge is needed because none has an unconstrained polymorphic
codomain.  The imported whole-space norm also has an explicit `rfl` drift guard
against `NSFormalization.Section4.D01.dotHomogeneousENorm`.

The contract and canonical `LocalizationAPI` structures are distinct
declarations, so the binding transports the proved
`NSFormalization.Section3.T13.localizationAPI` field by field.  This is a
proof-only `Prop` record transport; it introduces no witness conversion and no
new mathematical premise.  In particular, the registered declaration is not
an implication from a hypothesized API.

## Non-vacuity route

The test repeats lane 359's admissible ball centered at `(1/2,1/2,1/2)` with
radius `3/8`, and its `ContDiffBump` field supported inside radius `1/4`.  It
proves the field is smooth, supported, and nonzero at the center, then applies
the registered `localization` field at `s = 1/2` to obtain the uniform bound.

No theorem weakening, placeholder proposition, new axiom, or source-module
change was needed.
