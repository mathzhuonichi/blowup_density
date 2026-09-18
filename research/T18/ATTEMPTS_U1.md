# T18 U1 attempts and conformance notes

## Final representation

`NSFormalization.Section3.T18.InsertionData` is a single canonical bundle for
the eleven parameters of `PeriodicInsertionAPI` after eliminating the
contract-only `PacketImportAPI`. Its packet is represented by the six raw
fields needed in the T15 record types; it then carries the canonical
`PlacementData`, `ScalingAPI`, T10 `ClassicalSolutionT`, T16 `CutoffData`, T17
`CorrectionAPI`, and the three paper hypotheses `hδ`, `hg`, and `ha`.

The U1 substitution table is:

| Spec expression | canonical expression |
|---|---|
| `P.velocity`, `P.pressure`, `P.force` | `data.packetVelocity`, `data.packetPressure`, `data.packetForce` |
| `place`, `scaling` | `data.place`, `data.scaling` |
| `reference.velocity`, `reference.pressure` | `data.reference.velocity`, `data.reference.pressure` |
| `a`, `g`, `r`, `δ`, `D`, `correction` | the same-named `InsertionData` projections |
| `normalizePressureT` | canonical T10 `normalizePressureT` |

Thus the three formulas unfold definitionally. The threshold is
`min data.place.ε₀ data.D.ε₀`; its two upper bounds are `min_le_left` and
`min_le_right`.

## The cutoff-threshold positivity detail

`CutoffData` is deliberately data-only and has no `eps_pos` projection. The
proof `0 < data.D.ε₀` is the `LocalPotentialAPI.eps_pos` field carried by
`data.correction.potential`. Therefore `eps_pos` is exactly

```lean
lt_min data.place.eps_pos data.correction.potential.eps_pos
```

No new positivity hypothesis was added to `InsertionData`.

## Spec conformance probe

`probes/insertion_closes.lean` restates the 17-field Spec `PlacementData`, the
7-field Spec `CutoffData`, and the first eleven fields of
`PeriodicInsertionAPI`. It converts placement and cutoff data field by field,
projects an actual contract `PacketImportAPI` to the six raw packet fields,
and converts the contract T11 `ClassicalSolutionT` with
`Bindings.TorusLocalTheory.ofContract`. `insertionU1OfCanonical` fills every
Spec-form U1 field from the canonical definitions and theorems. The only
non-definitional vocabulary transports are the existing `rfl` bridges for
`forceClassT`, `initialClassT`, and `normalizePressureT`.

## Resolved elaboration attempts

The first module pass exposed three spelling/elaboration details, all fixed:

- `(nu := ν)` produced `Invalid argument name nu for function ScalingAPI`;
  the canonical implicit binder is Unicode `(ν := ν)`.
- `data.D.eps_pos` produced `Invalid field eps_pos`; the proof lives at
  `data.correction.potential.eps_pos`, as explained above.
- A bare tactic `rfl` did not introduce the two universal binders and reported
  `Expected the goal to be a binary relation`; explicit `intro ε z` followed
  by `rfl` closes each displayed formula.

The first probe pass also opened both contract and upstream field namespaces,
which reported `Ambiguous term Space` and `Ambiguous term VelocityField`.
Using the contract field aliases consistently removed the ambiguity; their
definitions are the canonical upstream types.

There are no unresolved proof or statement errors.

## Concrete non-vacuity search

A required `grep -rn` search over the T15/T17 probes and canonical modules
found no constructed full `PlacementData`, `ScalingAPI`, or `CorrectionAPI`.
The apparent T15 geometric witness is explicitly only a U2 fallback:
`placement_closes.lean` says it is not a full `PlacementData`, since its
displayed `T = ε₀ = 1` violates `eps_time` at `ε = 1`. T11 does contain
concrete classical reference solutions. A fully concrete `InsertionData`
therefore still lacks:

1. a full 17-field placement paired with a full 21-field `ScalingAPI` (the T15
   U15 assembly), and
2. a full 45-field `CorrectionAPI` (the T17 assembly).

The U1 construction itself is conditionally non-vacuous for every such
threaded pair, as the final `Nonempty` example in the probe verifies.
