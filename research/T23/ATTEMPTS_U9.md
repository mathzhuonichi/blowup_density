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

## Same-D U2b/U3 seam (historical; closed by G2 below)

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

## Continuation 487b: G2 potential seam CLOSED

The U3 use audit found **zero reads of `potential_formula`, `potential_smooth`,
`potential_curl`, or `correction_formula`** in Triple/Solution/PressureNormalization.
Triple reads correction smoothness, divergence, support, the time/space scale
bounds and both cross transports. PressureNormalization reads no core at all.
The weakest useful core therefore has no potential identity, even windowed.

Authorised edits: LocalCorrection adds `WindowedCorrectionCore`, the projection
`LocalCorrectionCore.toWindowed`, a coercion, and its support-in-cylinder lemma.
The original core and every existing U2 theorem statement remain unchanged.
Triple and Solution replace only their core hypotheses and the support helper;
all conclusions remain unchanged. PressureNormalization needs no edit.
Assembly proves `WholeSpaceCorrectionAPI.windowedCore` at the **literal**
`supplierCutoff`, using `local_match` and `local_crossTransport` on the open
cylinder. Potentials are never globally identified. U4's existing statements
remain unchanged; seven weaker windowed variants live in Assembly.Windowed.

Assembly now includes the complete 48-field `boundaryInsertionAPI`. It takes
internal raw supplier clauses, not an API or conclusion-shaped record. The
binding chooses I02/I03 from the given reference and discharges **every** such
clause from that same C/A/D, including both normalized q=1 estimates. The
closed prescribed ball supplies a larger outer ball via compact thickening,
so the supplier retains C.r = the original prescribed r, not r/2.

Resolved compiler diagnostics:
- Cross transport rewriting required unfolding `correctedBackground` before
  rewriting the correction family equality.
- `simpa only` did not normalize the registered norm wrappers. Explicit
  `change` to the canonical norm, then rewriting center/time, closed all three
  I03 energy and Sobolev conversions (as in the U6 probe).
- Implicit point inference in `hmatch ⟨ht,hx⟩` exhausted even a temporary
  diagnostic million-heartbeat budget. `@hmatch (t,x) ⟨ht,hx⟩` resolves it;
  no heartbeat override remains.
- Contract conversion namespaces were closed/reopened to avoid inheriting
  the proof-side `open` and ambiguous solution/cutoff names.

The registered contract uses packet-indexed vocabulary, so the raw canonical
statement's missing packet clauses are discharged by PacketAPI projections.
It preserves the complete repaired existential's matching identities and all
48 fields. The box and explicit-IBP branches are distinct definitions; the
registered V1 statement is their conjunction. The literal arbitrary-D statement
is not registered. The original research Spec and existing contracts/tests
remain untouched.

## Continuation non-vacuity and audits

`assembly_box_closes.lean` constructs a complete API on (0,1)^3, center
(1/2,1/2,1/2), chart radius 1/4, prescribed supplier radius 1/8, viscosity=T=δ=1,
zero datum/force/reference, and the registered nonzero packet. The reference
horizon is spelled `place.T + 1`; `2` is propositionally but not definitionally
equal under real addition. The probe separately proves the packet nonzero.
Both theorems and all 54 U9 declaration audits print exactly the standard three.
The contract check prints `checkedBoundaryInsertion: checked; standard logical
axioms only`. Full gate details are in REPORT_487b.md.

Backward-compatibility check: existing U3 research consumers use explicit
`C.toWindowed` at the nine changed hypothesis sites; their theorem statements
and embedded Spec are unchanged. The negative quiet-history probe also uses
this projection so its rejection still tests the endpoint, not core inference.
A `CoeOut` adapter is retained, but explicit projection is needed when the
consumer leaves the radius/cutoff metavariables hidden behind Spec aliases.
U4 and supplier probes compile unchanged. No lane 476/477/478/481/483–486
production statement was changed.
