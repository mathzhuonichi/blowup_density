# Lane 233 — G1 assembly from data

## Result

`BlowupDensity.Bindings.insertionLifespanV2_of_data` proves the exact G1
quantifier order and registered-contract existential, without a supplier
hypothesis. `insertionFromData_lifespan` rewrites the exact lifespan to the
original `a,T`; `insertionFromData_forceConvergence` rewrites the same family's
convergence to the original force `g`. All parameters remain universal.

## Successful supply chain

1. `Bindings.maximalPartial.regularThrough_iff` converts strict lifespan to
   `Data.RegularThrough ν a g T`. The similarly named standalone
   `maximalPartial_regularThrough_iff` is the A02/Data vocabulary bridge,
   not the strict-lifespan equivalence.
2. `maximalPartial.referenceLifespan` chooses `δ>0`, a contract
   `ClassicalSolutionR ν a g (T+δ)`, and **strict** lifespan beyond `T+δ`.
   A02 `Order.referenceLifespan` obtains this by halving a realized margin.
   Merely unpacking `RegularThrough` once would not guarantee the stronger
   regularity required by the V2 lifespan record.
3. The I01 packet exists for every positive viscosity:
   `Source.selected_packet_every_viscosity` plus I01 energy/quiet/extension
   lemmas supply precisely the `Bindings.packet` field assembly.
4. `Bindings.correction` already accepts the open-slab smoothness, divergence
   and momentum fields. Restrict `[0,T+δ)` smoothness to `(0,T+δ)`; choose
   centre zero and radius one. No compact-ball supplier or new analytic
   hypothesis is needed. V2 correction permits a prescribed compact plateau,
   but G1 does not prescribe one, and R42 `insertionFamily` already shrinks
   its threshold to accommodate the compact support of the packet force.
5. `scaling C thresholds` preserves `C`; `insertionFamily S R rfl rfl`
   preserves the reference and initial datum. `F.g`, `F.T`, `F.margin` are
   definitionally `C.g`, `C.T`, `C.δ`.
6. Convert the selected strict inequality at `T+δ` back to `RegularThrough`;
   `InsertionLifespan.insertionLifespanV2API F hg hregLong` then supplies the
   registered V2 record, including full-horizon solution, maximal identification
   and essential-supremum blow-up. All three alignment equalities are `rfl`.

## Failed route and local repair

Directly importing both existing packet and scaling bindings failed:

```text
import Bindings.Scaling failed, environment already contains
'BlowupDensity.Bindings.navierStokesResidual_eq' from Bindings.Packet
```

These two modules declare different bridges with the same fully qualified
name. Importing a wrapper around either would still import the collision.
The lane forbids edits to existing bindings, so the new file imports the
packet's four upstream implementation modules and repeats only its record
assembly as `insertionFromData_packet`. It uses exactly the existing
construction, not a different mathematical packet or an assumed existence.
This local duplication can be removed after a separately authorized cleanup
renames one conflicting bridge. It is not an open mathematical supplier input.

The Lake library is `Bindings`, not `BlowupDensity.Bindings`; the correct
build target is `Bindings.InsertionFromData`.

## Satisfiability and audit

No peeled hypothesis remains for I02/I03/R42. The proof uses an arbitrary
classical reference; it does not impose global smoothness across an artificial
endpoint or restrict the reference to zero/stationary fields.

The audit instantiates `ν=T=1`, `a=g=0`, using A04 `zeroSol` on horizon two
and the existing zero initial/force membership witnesses. This directly
proves the required strict lifespan inequality without importing the entire
R43 endpoint stack. A second audited theorem takes `ε=L.family.ε₀>0` and
proves `maximalLifespanR 1 0 (L.family.force ε)=ofReal 1`; thus both the
hypotheses and the insertion parameter range are inhabited. All four
implementation declarations and both audit declarations print exactly
`[propext, Classical.choice, Quot.sound]`.

Validation results are recorded in `REPORT_233.md`. No existing Lean module,
contract, binding or test was edited; `COMPARISON.md` is the explicitly
requested existing documentation update.
