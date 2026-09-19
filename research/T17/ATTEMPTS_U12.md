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
