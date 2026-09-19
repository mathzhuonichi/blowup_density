# U9 attempts and exact residuals

## Closure and migration

Built all 26 pre-existing T23 modules together before editing: success, 10695
jobs. There were no duplicate declarations, and no existing canonical module
was changed. Migrated lane 481's four declarations from its research probe to
`Bindings.BoundaryInsertion`, without importing the embedded historical Spec.
The initial migration compiled unchanged.

## Prescribed radius (resolved at supplier level)

481 returns `C.r = r/2`. Applying it with radius `2*r` would require local
reference regularity on `ball x₀ (2*r)`, which the prescribed-ball hypotheses
do not give. Added `exists_spatial_solenoidal_extension_between` in Assembly:
for `0 < s < r`, choose bump radii `s` and `(s+r)/2`. The proof retains the
original curl construction and gives agreement on `ball x₀ s`.
The migrated constructors now take explicit inner radius `ρ`, `0 < ρ`, and
`ρ < r`, and return `C.r = ρ`. Their estimates and same-C identities are
unchanged. The unused outer positivity argument in the first constructor was
renamed `_hr` after Lean reported its unused-variable warning.

## Same-D U2b/U3 seam (OPEN)

For the repaired statement, D must copy all seven supplier fields, including
`D.potential = C.potential` and `D.correction = C.correction` globally.
U3's `InsertedTriple.history`, `initial`, `velocity_smooth`,
`correction_force_mem`, `incompressible`, `momentum`, and solution constructor
consume:

```
LocalCorrectionCore reference.velocity u K place.x₀ r place.T δ D
```

This record's `potential_formula` is quantified over **all** `t x`, not just
the local reference cylinder. At the literal supplier cutoff this would imply

```
C.potential = timePotential reference.velocity C.x₀
```

`Assembly.supplierCutoff_core_requires_global_potential` checks that exact
implication. U2b instead proves local reference agreement and equality of the
correction/force on the positive scale interval. Its supplier potential is
computed from the spatial extension, whose exterior values need not equal the
original reference. No theorem identifying these global potentials is available
or justified by local agreement. Shrinking the scale threshold does not change
this all-space, scale-independent field.

This is an interface residual, not a counterexample to the intended corollary.
A viable continuation is to prove U3 against the operational correction facts
it actually uses, or to construct a local auxiliary cutoff and transfer the
U3 conclusions on the common scale interval to the literal supplier cutoff.
The latter must also preserve the globally quantified triple formulas; simply
identifying the two cutoff records or copying their potential field is invalid.
Existing canonical modules may only be edited for deduplication in this lane,
so no weakening of `LocalCorrectionCore` was performed.

Downstream: without this adapter, U3 solution/force facts at the selected D
are not supplied; U4 support/no-slip, U5 comparison, U6 rates and U8
lifespan/blowup have not been instantiated into one 48-field record. Their
previous conditional unit results remain intact. No named input was added to
assert these missing conclusions.

## Raw statement fidelity

`Boundary.boundaryInsertionStatement'` quantifies raw u,p,f,K,M,E with no packet
clauses. `DomainPlacementData` supplies geometry, not packet smoothness,
equations, energy identities or speed blowup. A theorem over raw packet fields
must explicitly include these clauses; a registered packet-indexed theorem
can discharge them by projections. The raw definition cannot be used as-is as
a proved statement merely by selecting the registered nonzero packet.
The canonical definition was left untouched under the editing restriction.

## Registration withheld

No contract or Tests file, registry entry, or T23 contracts list was added.
G0's existential repair and G1's unconditional box / explicit-IBP smooth scope
remain the intended owner-pending V1 wording. Neither requested final theorem
nor a full API non-vacuity instance is claimed by this partial delivery.

## Audit/probe diagnostics (resolved)

The guarded axiom output wrapped long names onto several lines:
`Docstring on #guard_msgs does not match generated message`. All sets were
already the exact standard three; `whitespace := lax` fixes formatting only.

The first concrete probe imported PacketImport alongside Scaling and hit:
`import Bindings.Packet failed, environment already contains
'BlowupDensity.Bindings.navierStokesResidual_eq' from Bindings.Scaling`.
This pre-existing collision is documented in `Bindings.InsertionFromData`.
The probe now consumes its existing `insertionFromData_packet` constructor,
which assembles the same upstream nonzero packet into the registered PacketAPI
vocabulary without the colliding Packet binding import. No existing binding
was edited or new packet witness assumed. This is a supplier non-vacuity probe
at T=delta=1, inner radius 1/4 and outer radius 1/3, with zero reference velocity;
it does not assert a unit-box ClassicalSolutionOmega or complete boundary API.
