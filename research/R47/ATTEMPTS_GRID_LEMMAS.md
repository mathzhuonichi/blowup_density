# R47 grid lemmas — attempts and decisions

## Sources checked

- `Contracts/V1/Data.lean:754-784`: `Grid` is the existing per-axis
  `CartesianGrid`; `Grid.cell` is half-open, and `gridObservation` is the
  vector Bochner cell average.
- `paper/sections/04-whole-space.tex:286-320`: the common ball is chosen away
  from finitely many grids' faces; velocity mean zero comes from smooth compact
  solenoidality, while force mean zero comes from the integrated difference of
  the two momentum equations.
- `research/R47/RECONCILIATION.md` §4 and the reconciled lane-246 spec: the
  consumer needs plain `ball ⊆ cell`, `velocity_observations`, and the common
  support ball used by `velocity_support`.
- `Contracts/V1/Packet.lean`: there is no named packet `mean_zero` field.  The
  relevant exported premise is divergence freedom; the inserted-family
  contract separately exports `velocityDifference_divFree` and topological
  support containment.

## Successful route

`Paper3.GridGeometry.finite_grids_common_ball` already proves the stronger
statement that one positive ball lies in an *open cell interior* of every grid.
Because registered `Grid` is an abbreviation of `CartesianGrid`, the binding
uses that theorem directly and composes with
`cellInterior_subset_cell`.  The prescribed `x : Space` in the requested
interface is intentionally unused: neither the paper nor the reconciled spec
requires proximity to a prescribed point.

For locality, the cells are half-open and pairwise disjoint.  The proof handles
the containing cell by splitting the Bochner integral of `z₁ - z₂`, which
requires `IntegrableOn z₁` and `IntegrableOn z₂` there.  On every other cell,
topological support containment and pairwise disjointness give pointwise
equality, so no integrability hypothesis on that other cell is needed.

The explicit zero-integral hypothesis is the strongest common interface for
both paper applications:

- for velocity, smooth compact support plus `velocityDifference_divFree`
  gives zero component integrals via
  `Paper3.setIntegral_component_eq_zero`, hence zero vector integral;
- for force, divergence freedom is not asserted or needed.  Equation
  `eq:gridforce` and compact boundary support give its zero cell integral.

## Rejected / unnecessary routes

- Support containment by itself is insufficient on the containing cell: a
  compactly supported field can have nonzero mean.  Therefore no locality
  theorem omitting the zero-integral premise is true.
- Reusing only `CartesianGrid.cell_disjoint_interior` would force the binding
  to strengthen the reconciled `ball ⊆ cell` premise to `ball ⊆ cellInterior`.
  Instead the proof establishes pairwise disjointness of the registered
  half-open cells locally.
- No “near a prescribed point/open set” variant was added.  The paper chooses
  an arbitrary point off the grid faces and the reconciled `containingCell`
  field has no prescribed-location clause.
- The first direct `lake env lean` run reported a missing
  `GridObservations.olean`; building `Bindings.GridLemmas` first generated the
  dependency, after which direct checking was silent.
