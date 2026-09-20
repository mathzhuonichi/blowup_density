# T11 U1 — flow-conversion attempts

Lane: `308-T11-U1-flow-conversion`.

## Paths tried

1. Compared the bodies of
   `NSFormalization.Source.residual` in
   `formalization/NSFormalization/Source/Insertion.lean` and
   `NavierStokesR3.ProblemStatement.navierStokesResidual` in
   `vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean`.
   The proposed equality closed by `rfl`.
2. Compared `NSFormalization.Section3.T10.IsPeriodicOn` in
   `Section3/T10/PeriodicData.lean` and
   `NavierStokes.ProblemStatement.UnitSpatialPeriodsOn` in the pinned vendor
   problem statement.  The proposed equivalence closed by `Iff.rfl`.
3. Constructed `toFlow` and `ofFlow` by named fields.  Because the residual
   and periodicity types are definitionally equal, the corresponding proof
   fields transfer directly; no rewriting or cast is needed.
4. Tested both full structure round trips.  Lean accepts each by `rfl`,
   including structure eta and proof irrelevance.
5. Transported `MemForceT f` to `IsSmoothPeriodicForce f` using global
   smoothness restricted to each closed slab and periodicity restricted from
   `univ` to `Ici 0`.

## Errors

No target proof attempt produced a Lean error.  The module and exact-signature
probe elaborated on the first implementation pass.

An exploratory run of the unrelated pre-existing T12 axiom audit, used only
to inspect the repository's audit convention before the relevant dependency
had been built, printed exactly:

```text
../research/T12/axioms_spectral_gap.lean:1:0: error: object file '/data_8T/ping/blowup_density/.claude/worktrees/308-T11-U1-flow-conversion/formalization/.lake/build/lib/lean/NSFormalization/Section3/T12/SpectralGap.olean' of module NSFormalization.Section3.T12.SpectralGap does not exist
```

This was not a FlowConversion failure and required no source change.

## Residual named input

None.  U1 is unconditional.  No `def … : Prop` input hypothesis was added.

## Scope boundary

No lifespan equality is exported here: `T11_SPLIT.md` assigns
`maximalLifespanT = PeriodicLifespan.lifespan` to U15, after the three extra
`ClassicalSolutionT` fields are available uniformly for Paper 1 flows.
