# Lane 222 — S1b continuation record

The router left the uncommitted `EnergyIdentity.lean` draft. It was retained and
built successfully before further changes. The original brief was absent from
this checkout; the identical lane brief was read, without editing, from the
main checkout's `collaboration/briefs/222-R44-s1b-energy-identity.md`.

## Successful route

* `energyDatum` selects the unique physical Sobolev realization. Values outside
  the classical lifespan play no role. Uniqueness identifies the velocity with
  `lowerVectorL 2 s` of the smooth order-two path from lane 215. The force datum
  equals the lowering of any order-six force datum, hence of `MemForceR`'s path.
* `hasDerivAt_Y_sq` differentiates the actual `JWeight.Y`, locally replacing it
  by the norm of this path. `energyVelocity_momentum` transports A04's exact
  order-two momentum identity through the continuous linear lowering map.
* `inner_eq_jPairing` uses the two-source lowering transfer with total order one.
* `half_laplacian_component` transfers the two half-order slots to orders
  `-1` and `2`, moves one derivative by real skew-adjointness, and commutes it
  with lowering. The resulting pairing of orders `-2` and `3` is the squared
  norm at their mean order `1/2`. Summing components and directions and using
  `Z_sq_eq_sum_norm` proves `laplacian_jPairing` exactly.
* `pressure_jPairing_zero` pins the pressure datum to the Leray complement,
  lowers the order-two solenoidal velocity to order `3/2`, and applies
  self-adjointness. `Jmul` is the existing weighted-carrier reindexing.
* `energy_identity` constructs all momentum data, including pressure via
  D01's pressure-jet theorem. Its only inputs are positive viscosity, admissible
  force, a classical solution, and an interior time. No residual hypothesis.
* `zero_energy_terms` and the closed example in `axioms_s1b.lean` verify the
  zero-force, zero-solution case; every printed declaration has exactly the
  three permitted axioms.

## Failed attempts and repairs

* The existing integer-indexed Laplacian energy theorem cannot be instantiated
  at `m = 1/2`. Its component proof, rather than its natural-number binder, was
  reused with the lowering-transfer argument above.
* Ordinary `rw`/`norm_num` sometimes failed on numerically equal orders because
  the shared Sobolev carrier has a phantom order and the elaborated expression
  is not type-correct at the tactic's restricted transparency. The diagnostic
  was `Application type mismatch ... RealVectorSobolev (3 / 2 - 1) ...
  RealVectorSobolev (-1 / 2)`. Explicit ambient coercions, order-normalizing
  `erw`, and a locally typed pairing vector resolve these mismatches.
* Feeding an equality-transported datum (`h ▸ A`) directly to the integer
  Laplacian constructor exhausted 400000 heartbeats. Normalizing the order
  before supplying the datum avoids that transport. In the energy assembly,
  `rw [hl, hp]` also exhausted the budget by unfolding large selected data;
  `simp only [hl, hp]` performs the intended replacements cheaply.
* Two declarations retain commented, local 400000-heartbeat caps; all others
  use the default. No global option or forbidden proof placeholder was added.

## Lane 220 compatibility

Read-only inspection of `erenup/220-R44-s1c-trilinear` found
`TrilinearJ.lean`, whose `advectionJPairing h ha` expands to
`inner ℝ ha.advectionNegHalf (Jmul h.velocityThreeHalf)`.
The original draft's conflicting `advectionJPairing h N` was renamed
`energyAdvectionJPairing h N`. The expression is identical with
`N := ha.advectionNegHalf`; `energyDatum_eq ha.advectionNegHalf_isDatum`
identifies the canonical nonlinear datum used by `energy_identity`.
The physical advection spellings on a fixed velocity slice are definitionally
equal. Thus consumers rewrite this datum equality and unfold the two pairing
names; no estimate, physical Parseval hypothesis, or duplicate lane-220 module
is imported here. An integration adapter to the sibling structure remains a
name-level wiring step, not an analytic gap.

## Gates

See `REPORT_222.md` for final commands and outcomes. The conformance file also
serves as the requested zero-solution non-vacuity probe; the brief asks for no
separate mutation probe.
