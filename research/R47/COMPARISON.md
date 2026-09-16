# R47 reconciled specification — manuscript, drafts, and rulings

This comparison merges the independent Draft A (lane 240) and Draft B (lane
241) readings of Theorem 4.7, `thm:Rgrid`, against the lead's binding
reconciliation.  Line references are to `paper/sections/04-whole-space.tex`.

## Paper clause → Lean field, provenance, and ruling

| Paper clause | Reconciled Lean field(s) | Draft A provenance | Draft B provenance | Binding ruling |
|---|---|---|---|---|
| `:297-299`: under the regular-reference hypotheses of Theorem 4.2, first fix a finite grid family, then choose the inserted solutions | `RGridAPI.choose` with raw quantifier order `ν, 0<ν, a, a∈initialClassR, g, MemForceR g, T, 0<T, δ, 0<δ, reference, n, grids`, followed by `Nonempty (RGridFamily …)` | Stored a prepackaged `InsertionFamilyAPI` in an instance-level `RGridAPI ν P ι grids`; content was about a given family. | Universally quantified the raw reference data and `Fin n → Grid`, then returned one family witness. | Adopt B's existence shape and concrete `Fin n` indexing.  One witness is selected after the entire grid family; it is not selected separately for each grid. |
| `:298` together with Theorem 4.2 `:32`: one sufficiently-small-scale force/solution family | `ε₀`, `eps_pos`, `force`, `solution`, `force_mem` | These were projections/consequences of the stored `InsertionFamilyAPI`. | These were explicit fields of `RGridFamily`. | Adopt B's explicit raw fields.  `solution` is a full `ClassicalSolutionR ν a (force ε) T`, and the total real-indexed family supports the right-hand limit at zero. |
| Theorem 4.2 `:36`, inherited through “under the … hypotheses” at `:298`: unchanged earlier history | `history` | Not restated; inherited inside `InsertionFamilyAPI`. | Explicit equality for `ε ∈ (0,ε₀]`, then `0 ≤ t ≤ T-2ε²`, then every `x`. | Keep B's explicit field, as in the R46 ruling, so the inherited clause is visible on the chosen raw family. |
| Theorem 4.2 `:38`, inherited at `:298`: smooth compact force difference | `forceDifference_compact` | Inherited inside `InsertionFamilyAPI`. | Explicit `MemForceCompact (force ε-g)`. | Keep B's explicit field. |
| `:298-302`: `A_hu_ε(t)=A_hv(t)` for every prescribed grid and `0≤t<T` | `velocity_observations` | `velocityObservations` used a local exact predicate, with grid before scale in that field. | Inlined registered `gridObservation` equality, ordered scale, grid, time. | Use B's field name and exact order `ε`, admissibility, `i`, `t ∈ Ico 0 T`.  Equality of the function-valued observation constrains every cell. |
| `:298-302`: `A_hg_ε(t)=A_hg(t)` on the same ranges | `force_observations` | `forceObservations` used the same local predicate. | Inlined the registered observation equality. | Use B's field name and exact order; no local observation predicate is registered or retained. |
| `:303`: `T^ν_{max,ℝ}(a,g_ε)=T` | `lifespan` | Explicit on the stored family. | Explicit on the raw force family. | Keep B's raw-data field, with exact equality to `ENNReal.ofReal T`. |
| `:303`, invoking `:221-223`: `‖u_ε-v‖_{E_T} → 0` | `energy_convergence` | Explicit `Tendsto` using `energyENorm`. | Same explicit `Tendsto` on `solution ε` and `reference`. | Keep B's field/body in the raw witness. |
| `:303`, invoking `:224-228`: simultaneous `L¹_tL²_x`, `L²_tH⁻¹_x`, and `L²_tḢ⁻¹_x` convergence of `g_ε-g` | `force_convergence` | Used the manuscript-literal `mixedLebesgueENorm 1 2`, then the inhomogeneous and homogeneous negative-order norms. | Used `forceSobolevENorm 1 0` for the first term, followed by the same other two terms. | The initial ruling selected B's order-zero Sobolev spelling; the lead's later addendum supersedes that spelling and directs use of literal `mixedLebesgueENorm 1 2`.  The other two summands and the single `Tendsto` conjunct are retained unchanged. |
| `:303-304`: one common ball contained in one cell of every grid | `center`, `radius`, `radius_pos`, `containingCell` | Used plain `Metric.ball … ⊆ grid.cell k`, matching the theorem sentence. | Strengthened this to closure contained in cell interior, following the proof at `:306`. | Use A's plain containment.  The proof's stronger convenience is not part of the public statement. |
| `:303-304`: velocity differences supported in the common ball | `velocity_support` | Explicit support field projected from the stored insertion family. | Explicit field on the raw solutions. | Use B's raw field for every admissible scale and `t ∈ [0,T)`. |
| `:303-304`: pressure difference supported there, except for an optional spatially constant gauge | `pressure_support` | Introduced local `PressureDifferenceSupportedInBallModuloGauge`. | Inlined `∃ c : ℝ → ℝ, ∀ t ∈ Ico 0 T, tsupport (…) ⊆ ball`. | Use B's inline formula; choose one time-dependent gauge per scale before quantifying over time.  No new registered predicate is introduced. |
| `:303-304`, with Theorem 4.2 `:38`: force differences supported in the common ball | `force_support` | Explicit full-spacetime projection into the ball. | Same explicit full-spacetime formulation. | Keep B's raw-data field, including the portion of the compact force difference after `T`. |

`RGridFamily` carries all conclusion fields, and `RGridAPI.choose` asserts their
simultaneous existence.  This is the pair of structures required by the lead's
explicit §3 decision; neither is inhabited or proved in this specification.

## Quantifier order and retained scope

The outer order is exactly:

1. `ν : ℝ`, then `0 < ν`;
2. `a : SpatialField`, then `a ∈ initialClassR`;
3. `g : SpaceTimeField`, then `MemForceR g`;
4. `T : ℝ`, then `0 < T`;
5. `δ : ℝ`, then `0 < δ`;
6. `reference : ClassicalSolutionR ν a g (T+δ)`;
7. `n : ℕ`, then `grids : Fin n → Grid`;
8. one `RGridFamily` witness.

Inside each observation field the order is admissible scale `ε`, grid index
`i`, then `t ∈ [0,T)`.  The function equality returned by `gridObservation`
means every cell of that grid.  The containing-cell index depends only on the
grid.  The pressure gauge depends on the scale and time, but not on space, and
one gauge function must work for every presingular time at that scale.

The explicit `reference` is retained; a redundant `RegularThrough` conjunct is
not added.  The history, full classical solutions, force compactness, exact
lifespan, both limits, and all three support clauses are retained on the same
witness.  The closure/interior strengthening, local named predicates from A,
point observations, pressure observations, and uniformity under arbitrary grid
refinement are not retained.

## Boundary with Proposition 4.6 density vocabulary

Theorem 4.7 at `:303` imports “the energy and force convergences” stated at
`:221-228`; it does not repeat the completed-space density assertions at
`:218-220`.  Thus `completedSobolevDensity` and
`completedHomogeneousDensity` are not `RGridFamily` fields.

The requested registered-vocabulary checks nevertheless appear in `Spec.lean`:

- for `q : ℝ≥0∞`, `(q = 1 ∨ q = 2)`, and
  `s < criticalOrder q.toReal`, Lean accepts by `rfl` that
  `CompletedDense q s S` is `CompletedDenseVia q s (IsSobolevPath s) S`;
- Lean accepts by `rfl` that `CompletedDenseHomogeneous 2 (-1) S` is
  `CompletedDenseVia 2 (-1) (IsHomogeneousPath (-1)) S`.

These checks confirm the registered abbreviations without adding either
density conjunct to R47.

## Assembly proved (lane 258)

`verification/Bindings/GridAssembly.lean` now supplies `rGridFamily_of_data`
and `rGrid_choose_of_realization`. The two structures are copied byte-for-byte
from `Spec.lean`, and the theorem's conclusion copies `RGridAPI.choose` token
for token. Every field belongs to the same witness, with a common ball chosen
by lane 247 before the correction is constructed.

Lane 233 fixes its own ball, so the assembly reuses its packet and reconstructs
its correction/scaling/insertion chain with the chosen center and radius and
the supplied reference itself. Lane 251/253 supplies both grid observations on
`[0,T)`. The R42 support/history/compactness fields, full-horizon solution and
exact lifespan suppliers close the remaining geometric and solution fields;
lane 249 supplies the energy limit. The pressure gauge is identically zero.
Forces and solutions at inadmissible scales use the fixed admissible scale
`ε₀`; this total extension preserves every admissible-scale clause and limit.

`Bindings/GridAssemblyNorms.lean` proves the literal mixed-norm limit directly
from the registered correction bound and packet mixed-norm convergence, joined
by the measurable-slice-path triangle inequality. No `H⁰ = L²` bridge or norm
renaming is assumed. R42 supplies the inhomogeneous `(2,-1)` limit. Lane 250's
homogeneous estimates and a proved compact-path triangle inequality supply the
third limit. The packet and correction powers are `1/2` and `3/2`.

The **single remaining input** is lane 250's exact
`NSFormalization.Section4.I03.CompactHomogeneousRealization`: time strong
measurability of the explicit D01 compact homogeneous path. It occurs only in
the homogeneous force convergence chain. **Lane 255** is assigned to close
this input. This assembly does not assert its unconditional proof.

## Order-zero bridge status

The general identity `mixedLebesgueENorm 1 2 f = forceSobolevENorm 1 0 f`
is still not supplied by this lane. The earlier failed `rfl` probe correctly
identified distinct path carriers. This is no longer an R47 assembly blocker:
the manuscript-literal mixed norm in the unchanged spec is proved to converge
directly. No owner ruling or additional named assumption is needed for R47.

Axiom audits and zero-data examples for both empty and nonempty grid families
are in `axioms_assembly.lean`; proof decisions and failed routes are recorded
in `ATTEMPTS_ASSEMBLY.md`.
