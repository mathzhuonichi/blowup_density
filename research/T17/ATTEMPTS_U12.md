# U12 assembly attempt — lane 453

## Outcome

The precise G4 statement supplied in the lane instruction is false. The
counterexample is kernel checked in
`formalization/NSFormalization/Section3/T17/AssemblyObstruction.lean`.

## Geometry obstruction

Take `u = p = f = 0`, `K = Kstar = ∅`, `T = δ = ν = 1`, the
cube centre as both chart centre and placement point, chart radius `1/8`,
placement threshold `1/8`, and requested potential radius `r = 1/4`.
All placement conditions hold. Let the reference be the constant first
coordinate vector; it is nonzero, globally smooth, periodic and divergence free.
The packet-support condition is empty. Thus every stated G4 premise holds.

An API witness would imply that the ball of radius `1/4` is contained in the
concentric ball of radius `1/8`. The point displaced by `3/16` along the first
coordinate lies in the former and outside the latter. This contradiction is
independent of the cutoff data, so shrinking `ε₀` does not help.

## Required lead decision

Add the explicit ball-in-chart hypothesis to G4 (with all 45 fields unchanged).
The worker requested this amendment; no answer was available when recording
this result. The user-supplied G4 is treated as authoritative; the checkout's
SPEC_ISSUES.md contains only the earlier G1/G3 entry and RECONCILIATION.md does
not contain the advertised final lead amendment.

## Rejected approach

Deriving the U9 `hcube` premise from `CorrectionAPI.ball_in_chart`, as in the
existing probe, is valid for an already constructed API. It is circular when
constructing that same API. Placement's `x₀_mem` only guarantees existence of
some sufficiently small radius, not the universally quantified radius in G4.

## Registration

No false theorem, placeholder assembly, or registry entry was added. Existing
contract and test modules are unchanged. U12 remains blocked on the statement.

## Continuation — completed G4 (2026-09-19)

The user accepted the obstruction and supplied the final ball-in-chart and raw
packet support premises. The earlier blocked outcome is superseded. The old
counterexample module and import-only wrapper were removed; the same proof and
inline axiom prints now live in the standalone
`research/T17/probes/assembly_geometry_obstruction_module.lean`.

The final block suffices. `correctionAPI_of_smooth` fills all 45 fields at
`correctionData`. T16 supplies the cutoff/potential record; T13 supplies
`localizationAPI`; U3–U11 supply every profile, force, measure and norm field.
The energy/mixed `hcube` premise is `(closure_mono hball).trans
place.chartBall_in_cube`, with no circular use of the constructed API.
The packet support hypothesis is enlarged using `place.carrier_subset`.

T16's cutoff existence and `localPotentialAPI` constructor are used explicitly,
rather than destructuring an opaque existential and losing the concrete
`correctionData` formula. Set `ε₀ := min ε₁ place.ε₀`; positivity and all T16
inequalities survive by interval inclusion, and `place.eps_le_one` yields
`ε₀ ≤ 1`. This needs no new hypothesis or change to an existing proof module.

The contract uses registered T10/T11/T13/T14/T16 vocabulary and restates only
unregistered T15/T17 notions. Its `Packet` namespace copies the Spec record and
unamended statement byte-for-byte. The enclosing raw record retains the same
45 fields and supports the exact raw-field G4 statement. All restated function
definitions have `rfl` bridges; record-dependent statements have fieldwise
transports, with both API conversion round trips proved. No unamended existence
assertion is registered.

Non-vacuity is a full API, at the cube centre `(1/2,1/2,1/2)`, chart/requested
radius `1/4`, `ν=T=δ=1`, zero packet and reference `e₀ ≠ 0`. The witness carries
a positive threshold and the actual admissible scale `ε = D.ε₀`.

Routine elaboration fixes: opening both the vendor and contract field namespaces
in the binding made `Space`/`VelocityField` ambiguous; use the contract namespace.
The first textual fidelity check used a section marker absent from the Spec;
using the actual end-of-record marker confirms byte-for-byte equality. Neither
failure revealed a mathematical gap. Build, axiom and gate outputs are recorded
in the Continuation section of `REPORT_453.md`.
