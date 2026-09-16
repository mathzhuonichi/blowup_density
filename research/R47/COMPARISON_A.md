# R47 Draft A — manuscript-to-Lean comparison

This draft was derived only from the authorized manuscript passages and the
registered V1 vocabulary.  It does not use another R47 draft or comparison.

## Paper clause → Lean field

| Paper text | Lean transcription | Notes |
|---|---|---|
| `04-whole-space.tex:297-299`, under the hypotheses of Theorem 4.2 and after fixing a finite family of grids, “The inserted solutions may be chosen” | `RGridAPI` parameters `ι`, `[Finite ι]`, `grids`, then field `family` | `family : InsertionFamilyAPI ν P` carries the regular reference and one chosen inserted family. The grid family is fixed before this witness is stored. |
| `04-whole-space.tex:298-302`, `A_h u_ε(t)=A_hv(t)` for every grid and `0≤t<T` | `velocityObservations` | Quantifier order is grid index `i`, admissible `ε`, then the time quantifier inside `IdenticalCellObservationsBefore`. Equality is of the complete observation functions, hence of every cell average. |
| `04-whole-space.tex:298-302`, `A_h g_ε(t)=A_hg(t)` for every grid and `0≤t<T` | `forceObservations` | Same order and same time interval as for velocity. |
| `04-whole-space.tex:303`, `T^ν_{max,ℝ}(a,g_ε)=T` | `lifespan` | `maximalLifespanR` is `ℝ≥0∞`-valued, so the real time is embedded by `ENNReal.ofReal`. |
| `04-whole-space.tex:303`, energy convergence in Proposition `prop:Renergy`; display at `:221-226` | `energyConvergence` | Literal `Tendsto` of `energyENorm T (u_ε-v)` along positive `ε→0`. |
| `04-whole-space.tex:303`, force convergences in Proposition `prop:Renergy`; display at `:224-226` | `forceConvergences` | Literal convergence of the displayed sum of the `L¹_tL²_x`, `L²_tH⁻¹_x`, and `L²_tḢ⁻¹_x` norms. |
| `04-whole-space.tex:303-304`, one ball contained in one cell of every grid | `ballContainedInEveryGrid` | The ball is the single ball already carried by `family`. The cell index may depend on the grid. |
| `04-whole-space.tex:303-304`, all velocity differences supported in that ball | `velocityDifference_support` | Restated explicitly with the same presingular time range as `InsertionFamilyAPI.velocityDifference_support`. |
| `04-whole-space.tex:303-304`, pressure support except for an optional spatially constant gauge | `pressureDifference_support` | Uses the concrete local predicate `PressureDifferenceSupportedInBallModuloGauge`; the gauge may depend on time but not on space. |
| `04-whole-space.tex:303-304`, all force differences supported in that ball | `forceDifference_support` | Uses the full spacetime support formulation of `InsertionFamilyAPI.forceDifference_ball`, so it is at least as explicit as the theorem sentence. |

## Vocabulary choices

- The draft quantifies over the registered `InsertionFamilyAPI` rather than
  repeating raw `a`, `g`, `v`, `π`, `u_ε`, `p_ε`, and `g_ε`.  This is the
  safest reading of “the inserted solutions”: the reference, scale threshold,
  three inserted fields, history, support, divergence-free difference, and
  convergence data are structurally one family.  Raw quantification would
  require many equality witnesses merely to say that all clauses concern the
  same construction.

- A finite family is represented by a finite type `ι` and a map
  `grids : ι → Data.Grid`, rather than by a `Finset`.  This needs no equality
  decision on real-valued grid parameters and preserves the ordinary notion of
  a finite indexed family.  Empty families and repeated grids are harmless.

- `Data.Grid`, `CartesianGrid.cell`, `Data.cellAverage`, and
  `Data.gridObservation` are already registered.  No local copies are made.
  `Data.Grid` already means a complete uniform Cartesian grid with positive
  per-axis widths, arbitrary offset, and half-open cells.

- `IdenticalCellObservationsBefore` is local and marked **needs
  registration** because the registered vocabulary has the observation map but
  no named spacetime equality predicate.  It is not a placeholder proposition:
  its body is the exact universally quantified equality of the two registered
  observation maps.

- `PressureDifferenceSupportedInBallModuloGauge` is local and marked **needs
  registration**.  It subtracts `c(t)` from the pressure difference before
  taking spatial support.  This matches the registered pressure convention,
  where a pressure gauge can depend on time while remaining spatially
  constant.

## Quantifier order

The structure parameters and fields encode:

1. viscosity `ν` and the registered packet `P`;
2. a finite index type `ι` and the prescribed family `grids : ι → Data.Grid`;
3. one chosen `family : InsertionFamilyAPI ν P`;
4. for each prescribed grid;
5. for each `ε ∈ (0, family.ε₀]`;
6. for every `t` satisfying `0 ≤ t < T`, the two observation equalities.

Thus one insertion family works simultaneously for the whole prescribed finite
grid family.  The statement does not choose a new insertion for each grid.

## Ambiguities resolved or retained

- **Meaning of “identical”.**  Draft A reads it as exact equality of every
  vector-valued cell average, for every admissible insertion scale and every
  presingular time.  It includes `t=0` and excludes `t=T`, exactly as
  `0≤t<T` says.  It does not assert equality of point values, pressure
  observations, or observations after `T`.

- **Which family.**  All fields project from the single stored `family`.  The
  theorem is read as permitting the Theorem 4.2 family to be chosen after the
  finite grids are prescribed.  `RGridAPI` is consequently a conclusion/output
  record; a later implementation theorem should construct an inhabitant from
  the raw regular-reference hypotheses.  It is not a claim that an arbitrary
  already-chosen insertion family can be retrofitted to arbitrary grids.

- **No arbitrary refinement.**  The finite map `grids` is fixed before the
  insertion family.  There is no quantifier over subsequent refinements and no
  limit as a mesh width tends to zero, consistent with
  `04-whole-space.tex:323-329` and the R47 task entry.

- **Common cell.**  “One cell of every grid” is read as one cell per grid, with
  a grid-dependent index `k`, all containing the same open insertion ball.
  The proof chooses the closure strictly inside each cell (`:306`), but the
  theorem statement says only that the ball is contained, so the field states
  only the latter.  Strengthening to closure containment is deliberately not
  imported from the proof.

- **Pressure gauge.**  The registered insertion record chooses a compact
  pressure representative, for which the local predicate is witnessed by
  `c=0`.  The theorem wording also permits changing that representative by a
  spatially constant gauge, so the public clause is stated modulo `c(t)`.

- **Support time range.**  Velocity and pressure are asserted only at
  presingular times, where the inserted classical solution is defined.  The
  registered force difference has global compact spacetime support; Draft A
  retains that stronger registered formulation.

- **API packaging.**  `InsertionFamilyAPI` is an instance-level record rather
  than a universally quantified theorem.  Draft A follows that registered
  packaging.  The universal construction from arbitrary raw regular-reference
  data is therefore expected at the eventual binding/theorem layer, not hidden
  as an extra clause in this statement-only refinement record.
