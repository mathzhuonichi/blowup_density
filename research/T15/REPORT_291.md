# Lane 291 report — T15 blind draft A

## 1. What theorem was specified

`DraftA.lean` specifies Proposition 3.3, “Scaling at fixed viscosity,” from
`paper/sections/03-torus.tex:101-159`. For one T14 packet it fixes the chart,
`K_*`, placement center, singular time, and one sufficiently-small scale
range; defines the literal parabolic rescaling and its lattice periodization;
and states the periodic fixed-viscosity PDE, zero initial data, blow-up at
`T`, pressure normalization, both exact packet-energy identities, the exact
mixed-norm identity, and the `L¹_tH^s_x(T³)` bound. The “in particular”
subcritical convergence is a separate derived proposition, not an assumed API
field.

## 2. What Lean now contains

- Explicit `scaledVelocity`, `scaledPressure`, and `scaledForce` definitions
  with time first, exact amplitudes `ε⁻¹,ε⁻²,ε⁻³`, shift `T-ε²`, and the T14
  negative-time extension convention.
- Lattice-sum periodization definitions for vector and scalar fields, plus a
  mean-normalized pressure.
- `PlacementData`, which fixes `T`, the chart ball, `x₀`, compact `K_*`, one
  threshold `ε₀`, `2ε²<T`, and `x₀+εK_*⊂B` before the scale-dependent
  conclusions.
- A pointwise, anti-substitution `ScalingAPI` over the exact explicit fields.
  It uses T10's `energyEssSupT`, `energyGradientT`, `forceSobolevENormT`,
  `PressureGaugeT`, and `MemForceT`; T14's `PacketImportAPI` constants `M,D`;
  and carries T13's `LocalizationAPI` as a parameter.
- A torus `mixedLebesgueENormT` in the same measurable-path style as Section
  4. Explicit `MemLp` witness predicates accompany mixed and Sobolev norm
  claims, and the energy terms have a finiteness clause.
- `COMPARISON_A.md`, with the paper/I03 field map, design decisions,
  ambiguities, proof obligations, and existing `Paper1/` candidates.

The research file copies only the temporary T10/T13/T14 declarations needed
to elaborate independently. It imports no implementation module and asserts
no existence theorem.

## 3. Remaining gaps

This lane is statement-only, so no inhabitant of `ScalingAPI` is constructed.
The main implementation obligations are local finiteness and smoothness of the
lattice periodization, commutation with the Navier–Stokes residual, invariance
under pressure normalization, exact endpoint-aware changes of variables,
time-integrated use of T13 localization, and the negative-order monotonicity
needed for convergence below `s=0`. `COMPARISON_A.md` lists these separately.

One upstream naming mismatch remains intentional: the reconciled T13 file is
currently in namespace `BlowupDensity.T13.Spec`, while this lane brief asks
temporary copies to live in `BlowupDensity.T13.Draft`. Registration should
remove all copies and provide drift-checking bridges.

## 4. Commands run and results

- `cd verification && LEAN_NUM_THREADS=6 lake env lean
  ../research/T15/DraftA.lean` — passed with no output.
- `make check` — passed (the repository inventory still reports its known
  copied-source `BoundaryCorollary.lean` admission; the gate exits zero).
- `make test` — passed; only pre-existing upstream linter warnings were
  replayed.
- `make test-mutations` — passed all four mutation cases.
- Read the complete requested paper range `03-torus.tex:99-175`, T10/T13/T14
  reconciled specs, registered `Packet.lean` and `Scaling.lean`, and the heads
  of `PeriodicScalingBounds.lean`, `ScalingLimits.lean`, and
  `PeriodicPacketEndpointRates.lean`.
- Final staged-diff whitespace and forbidden-token scans passed before commit.
