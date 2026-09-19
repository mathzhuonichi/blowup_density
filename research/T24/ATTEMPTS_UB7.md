# T24b Ub7 assembly and registration attempts

## Successful route

`MultipleAssembly.lean` packages the thirty fields directly from one
`RegionsData`. The existence theorem introduces the complete raw
`multipleRegionsStatement` hypothesis list, builds the eight-field
`Section4.I03.PacketData` and the remaining `RegionsData` fields, and returns
`Nonempty` of that constructor. No clause is weakened and no extra premise is
used.

The registered record is the Spec's packet-indexed spelling. Its
`PlacementData`, `ScalingAPI`, and `ClassicalSolutionT` members are distinct
contract structures, so `Bindings/MultipleRegions.lean` uses the existing
fieldwise conversions in `Bindings.Scaling3` and
`Bindings.TorusLocalTheory`. Both whole-record round trips close by `rfl`.
The four restated function definitions have whole-function `rfl` drift guards.

## Authorized duplicate reconciliation

Lanes 468 and 469 both declared
`RegionsData.assembledVelocity := finiteVelocitySum (fun j ↦
(d.component j).velocity)`. As authorized by the lane lead note,
`MultipleRegions.lean` now imports `MultipleAssembled.lean` and its local
duplicate definition was deleted. Every Ub5/Ub6 theorem statement is
unchanged; the required closure build passed without any proof adjustment.

## Resolved diagnostics

1. The first contract draft wrote unqualified `ScalingAPI` inside
   `BlowupDensity.Contracts.V1`. Lean selected the older root declaration and
   reported:

   ```text
   Application type mismatch: The argument P has type PacketImportAPI ν
   but is expected to have type ℝ in the application ScalingAPI P
   ```

   The two structure fields now explicitly select
   `Scaling3.PlacementData`/`Scaling3.ScalingAPI`; all other field tokens are
   the Spec spelling.

2. A public alias without a signature left the viscosity implicit
   unconstrained:

   ```text
   don't know how to synthesize implicit argument ν
   Failed to infer type of definition multipleRegions
   ```

   Giving the wrapper its full packet/region signature fixed inference.

3. `Set.Pairwise`, `Set.closure`, and `Set.interior` were overqualified in that
   wrapper. In this Mathlib pin the required names are respectively
   `Pairwise`, `closure`, and `interior`; the original errors were an expected
   set argument for `Set.Pairwise` and `Unknown constant Set.closure` /
   `Set.interior`.

4. The first Tests shape examples did not open
   `Contracts.V1.TorusLocalTheory`, so `energyEssSupT` and `energyGradientT`
   were unknown. Opening the registered namespace fixed both examples. The
   checked declaration already printed `standard logical axioms only` in that
   failed build and continues to do so.

The concrete `N=1` probe uses the registered
`Bindings.packetImportFamily.select 1 one_pos`, the centre
`(1/2,1/2,1/2)`, radius `1/4`, and `T=1`. Cube containment is the coordinate
estimate from the existing T15/T17 non-vacuity probes; pairwise disjointness is
vacuous only because `Fin 1` has no distinct pair. The conclusion itself is
not vacuous: the selected API's `region_blowup 0` is read off explicitly.
