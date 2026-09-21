# R47 independent specification, draft B

## Paper clauses and Lean fields

All line references below are to `paper/sections/04-whole-space.tex`.

| Paper clause | Lean field |
| --- | --- |
| Regular-reference hypotheses, finite grid family (298; 32) | `RGridAPI.choose` |
| A single chosen family (298; 43) | `RGridFamily.force`, `solution`, `ε₀`, `eps_pos`, `force_mem` |
| Velocity averages equal (300–301) | `velocity_observations` |
| Force averages equal (300–301) | `force_observations` |
| Exact maximal lifespan (303) | `lifespan` |
| Energy convergence (303 → 221–223) | `energy_convergence` |
| Force convergences (303 → 224–228) | `force_convergence` |
| One ball in one cell of every grid (303; 306) | `center`, `radius`, `radius_pos`, `containingCell` |
| Velocity localization (303) | `velocity_support` |
| Pressure localization modulo optional constant gauge (303) | `pressure_support` |
| Force localization (303; 38) | `force_support` |
| Earlier history and compact smooth force difference inherited from insertion (36, 38) | `history`, `forceDifference_compact` |

`RGridFamily` has the individual conclusion fields; `RGridAPI.choose` packages their simultaneous existence. Neither structure has an inhabitant or proof in this draft.

## Choices

* Quantifiers: viscosity and positive viscosity; initial datum and membership; reference force and membership; positive target time; positive extension margin; actual reference solution; number of grids and the grid family; **then** one output family containing its ball and scale threshold. Within each observation clause: admissible ε, prescribed grid, presingular time, and (through function equality) every cell index. The containing cell depends on the grid, but not on ε or time. Empty finite families are allowed.
* Raw data is used instead of quantifying over an arbitrary `InsertionFamilyAPI`. The latter would select the ball/family before the grids, or impose packet/correction/scaling machinery as an additional hypothesis. The raw witness expresses the existential choice after the grids, with `ClassicalSolutionR` recording actual PDE solutions and their initial data. It does not prescribe the internal packet formulas or repeat all quantitative conclusions of Theorem 4.2. The explicitly referenced R47 convergences and lifespan concern exactly the same `force` and `solution` fields.
* `Data.Grid`, `Grid.cell`, `cellAverage`, and `gridObservation` are already registered. There are **no absent observation notions needing local definitions or registration**. “Identical observations” is ordinary equality of the registered sequence-valued map; no uninterpreted predicate is introduced.
* `Fin n → Grid` represents any finite family, including repeats, while each grid still has infinitely many cells indexed by `Fin 3 → ℤ`. Registered grids allow arbitrary offsets and positive per-axis widths, with half-open cells.
* A family is total in ε for the norms' right-hand limits. Outside `(0, ε₀]`, the solution family can be extended by any one admissible member; this does not add a mathematical existence requirement. No assertions about observation or support outside that scale range are made.
* A positive reference extension margin with a solution on `[0,T+δ)` is the witness form of registered `RegularThrough ν a g T`, and follows the registered R42 convention. It retains the actual velocity and pressure to be compared, unlike a bare proposition asserting regularity.
* Norms take values in `ℝ≥0∞`. `forceSobolevENorm 1 0` denotes the registered order-zero realization of `L¹_t L²_x`; the other two terms are `L²_t H⁻¹_x` and `L²_t Ḣ⁻¹_x`. The sum converges to zero as printed in Proposition 4.6. No claim is made that the background force belongs to the homogeneous space.

## Ambiguities and their resolution

1. **Identical means averages, not point values.** Equality holds coordinatewise for every cell in each prescribed grid, including cells other than the containing cell. It does not assert equality of restrictions of the velocity or force to the containing cell. There is no pressure-observation conclusion.
2. **Time endpoints.** Both observations hold for every `0 ≤ t < T`, including the initial velocity and force observations. There is no equality at the singular time T. Force support is global in time, inherited from Theorem 4.2; velocity and pressure localization only concern their classical domain `[0,T)`.
3. **Which family?** A single family is chosen after the entire finite list of grids. It simultaneously has the observation identities, exact lifespan, and all four convergence terms. This is not a theorem about every previously chosen insertion, nor about one family working for arbitrary refinements. The general density conclusion of Proposition 4.6 is not a convergence assertion and is not repeated.
4. **Ball containment.** The theorem text says “contained”; `containingCell` uses closure contained in the interior, as the permitted proof explicitly chooses at line 306. This is a harmless stronger witness selection, recorded rather than hidden.
5. **Pressure gauge.** The gauge is spatially constant and may depend on ε and t. A single function of t is chosen for each ε before quantifying over t. The zero gauge recovers the compact representative used in the proof. Smoothness of the pressure fields is already in `ClassicalSolutionR`; no observation of pressure is asserted.
6. **Regular through T+δ.** The prose at line 32 says “regular through T+δ”. The registered family uses a solution on `[0,T+δ)`. Since the positive margin is auxiliary and can be shrunk, this is the existential-margin reading, not a claim of endpoint regularity at the displayed horizon for a fixed margin. This convention should be retained or explicitly reconciled during comparison.

Only the authorized manuscript and registered vocabulary were used. No other R47 draft, statement collection, comparison, implementation, or collaboration brief was consulted.
