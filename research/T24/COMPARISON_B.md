# T24 draft B: paper clause → Lean field map

The draft keeps the T10 periodic physical-field representation and consumes
the copied T14 `PacketImportAPI` and T15 `PlacementData`/`ScalingAPI`.  `Type`
is used for the affine and finite-region APIs because the paper fixes
geometric/numerical data and carries selected fields; the conservative API is
`Prop` because it only states a universal implication and chooses no witness.

## Clause table

| Paper clause | Draft B field/definition | Section 4 counterpart | Choice or ambiguity |
|---|---|---|---|
| `prop:affine`, `03-torus.tex:668–671`: fixed packet, `ν`, terminal time, cylinder `B₀×(τ₀,τ₁)` | `AffineVariationAPI.viscosity_pos`, `.terminal_pos`, `.base_force_mem`, `.base_unbounded`, `.ballCenter`, `.ballRadius`, `.ballRadius_pos`, `.τ₀`, `.τ₁`, `.time_window`; `affineCylinder`, `AffineAdmissible` | No direct contract. `R45.force_classes.regularReference` has a fixed reference and simultaneous solution/force conclusions, but not local affine variations. | The periodic vocabulary uses `τ₁<T`; the paper's displayed affine proposition is normalized to `τ₁<1`. This is the rescaled terminal-time form.
| `eq:affine`, `:674–676`: `Ũ=U+b`, `Ṕ=P`, and the six-term force expansion | `affineVelocity`, `affinePressure`, `crossAdvection`, `affineForce`; `AffineVariationAPI.family` pins the selected `ClassicalSolutionT` to these exact fields | None. | The force is written with the registered `temporalDerivative`, `spatialLaplacian`, and cross transport, so no informal PDE residual remains.
| `b∈C_c^∞(Q)`, `div b=0`, `:672–675` | `AffineAdmissible` (global smoothness, compact support, exact cylinder support, pointwise divergence-free condition) | No direct counterpart. | `HasCompactSupport` is retained in addition to support inclusion to prevent a support predicate from silently totalizing an unbounded field.
| zero initial data, finite energy/dissipation, same late singularity, `:677` | `AffineVariationAPI.family`: `S.velocity (0,x)=0`, `energyENormT<⊤`, `energyGradientT<⊤`, `SpeedUnboundedAt`, and late agreement for `τ₁≤t<T` | `R47.grid_observations.GridFamilyAPI.history`, `.lifespan`, `.energy_convergence` have analogous pinned-history/solution obligations. | The solution class itself supplies regularity, incompressibility, periodicity, pressure gauge, and the PDE equation.
| infinite-dimensional distinct family, `:687–691` | `AffineVariationAPI.infinite_dimensional` gives a linearly independent countable family; `.distinct` gives injectivity of `b↦U+b` | No direct counterpart; `R47.grid_observations` is finite-grid, not infinite-dimensional. | Linear independence is stated on the concrete field space, not as an abstract “infinite-dimensional” proposition.
| non-isolation under `b↦λb`, `:692–696` | `affineCkSeminorm`; `AffineVariationAPI.nonisolated` gives `C^m` seminorm convergence for both velocity and force differences on every compact support set | `R47.GridFamilyAPI.energy_convergence`/`.force_convergence` are norm convergence, but not smooth-seminorm convergence. | The compact `C^m` seminorm is made concrete with iterated Fréchet derivatives and a totalized `sSup`; the API's `Tendsto` fields are the non-vacuity guard.
| `prop:multiple`, `:697–700`: finite disjoint interior balls, fixed `ν,T` | `MultipleRegionsAPI.ν`, `.ν_pos`, `.T`, `.T_pos`, `.N`, `.N_pos`, `.regionCenter`, `.regionRadius`, `.regionRadius_pos`, `.region_interior`, `.regions_disjoint` | `R47.grid_observations.GridObservationsAPI.choose` quantifies over finite `Fin n` families; `GridFamilyAPI.containingCell` is its common-support/separation analogue. | This draft selects the torus branch and makes “interior” explicit by containment in `interior fundamentalCube`; the bounded-domain/no-slip branch needs a separate domain carrier.
| `:701–706`: choose `x_j`, `ε_j`, `x_j+ε_jK_*⊂B_j`, `ε_j²<T` | `placement`, `.placement_time`, `.placement_center_mem`, `.scaling`, `ε`, `.ε_pos`, `.ε_admissible`, `.ε_time`, `.scaled_carrier_in_region` | `R47.GridFamilyAPI.center`, `.radius`, `.eps_pos`, `.velocity_support`, `.force_support` carry the same “one fixed support geometry” role. | Each region gets its own T15 placement/scaling record, while the imported packet is shared. This preserves the exact T15 binding for every rescaled field.
| `u=ΣU_j`, `p=ΣP_j`, `f=ΣF_j`, `:710–716` | `finiteVelocitySum`, `finitePressureSum`, `finiteForceSum`; `component`, `.component_pin`, `.assembled_velocity`, `.assembled_pressure`, `.assembled_force`, `.solution`, `.solution_pin`, `.force_mem` | `R47.GridFamilyAPI.solution`, `.force`, `.force_mem`, `.lifespan` are structurally similar selected-family fields. | Component fields are pinned to explicit T15 periodized fields, not merely existential solutions for the same force.
| simultaneous singularity in each `B_j`, `:712–722` | `component_velocity_support`, `.component_force_support`, `.region_agreement`, `.region_blowup` | `R47.GridFamilyAPI.velocity_support` and `.force_support` are the closest support counterparts; `R47` has observations rather than regional blow-up. | `region_blowup` expands the ballwise `limsup` into pointwise witnesses `t,x` with `T-δ<t`.
| finite energy/dissipation and displayed `M²Σ ε_j`, `D²Σ ε_j`, `:717–720` | `energy_finite`, `dissipation_finite`, `energy_bound`, `dissipation_bound`, using `packet.energyBound` and `packet.dissipationBound` | `R47.GridFamilyAPI.energy_convergence` is an energy norm limit, not the finite-sum square bounds. | Bounds are stated in the registered `ℝ≥0∞` energy terms, with explicit squares and finite sums; no unguarded real integral is introduced.
| `prop:conservative`, `:723–726`: `f=-∇φ`, globally defined periodic scalar | `PeriodicPotentialT`, `conservativeForceT`; `ConservativeForcingAPI.zero_from_rest` | No direct Section 4 counterpart. `R45.force_classes` only classifies compact/rapid forces. | The torus branch is represented. The force-class premise is explicit, so the statement cannot use a non-periodic/non-integrable totalized gradient.
| zero initial data implies `u≡0`, `:727–740` | `ConservativeForcingAPI.zero_from_rest` quantifies `ν>0`, `T>0`, smooth periodic `φ`, `conservativeForceT φ∈forceClassT`, and every `ClassicalSolutionT ν 0 … T`, concluding `S.velocity=0` | None. | The bounded-domain/no-slip sentence is recorded as an implementation gap rather than silently conflated with torus periodicity. The pressure-gauge exclusion of affine potentials is enforced by `IsPeriodicOn univ φ`.

## Needs-a-lemma / implementation list

- Prove the T15 support-transfer lemmas needed to discharge `component_velocity_support` and `component_force_support`, including the single-copy periodization clauses.
- Prove the affine PDE expansion and support/smoothness closure: `AffineAdmissible` implies the displayed `affineForce` is in `forceClassT`, and the selected affine fields form the pinned `ClassicalSolutionT`.
- Prove compact-support vanishing outside `Q`, late agreement, and the `C^m` seminorm bounds used by `nonisolated`; in particular, supply bounded derivatives of the base solution on the cylinder.
- Prove pairwise support separation kills every cross transport in the finite sum and yields `solution_pin`, `region_agreement`, and the two square energy bounds.
- Prove the conservative energy identity on the periodic torus and the integration-by-parts cancellation `∫∇φ·u=0`; then derive `zero_from_rest` in the registered solution class.
- If the bounded-domain branches are required, add a domain/no-slip carrier and its restriction/zero-extension norms rather than reusing the torus fields.

## Candidate implementation locations

`formalization/NSFormalization/Paper1/ConservativeForce.lean` and
`PeriodicNonpositiveForce.lean` are the natural conservative-force references;
the T15 periodization/scaling definitions are the source for all rescaled
component fields.  Section 4's `R47.GridFamilyAPI` is the closest existing
finite-family support/force/lifespan shape, while `R45.ForceClassesAPI` is the
closest force-class and regular-reference shape.
