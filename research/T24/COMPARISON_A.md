# T24 Draft A comparison

| Paper clause | Lean field |
|---|---|
| `affine:668-672` cylinder and endpoint inequalities | `AffineVariationAPI.cylinder`, `.cylinder_hypotheses` |
| `affine:673-680` compact divergence-free perturbation and definitions of `Ũ,P̃,F̃` | `.perturbation_class`, `.divergence_free`, `.velocity_definition`, `.pressure_definition`, `.force_definition` |
| `affine:681-686` support away from endpoints, equation, initial data | `.support_away_endpoints`, `.equation_and_divergence`, `.zero_initial_data` |
| `affine:687-696` bounds, late singularity, infinite dimensionality and non-isolation | `.finite_energy_dissipation`, `.same_late_singularity`, `.infinite_dimensional`, `.nonisolated_scaling` |
| `multiple:697-704` finite disjoint interior regions, ν>0 and T>0 | `MultipleRegionsAPI.region_count`, `.positive_viscosity`, `.positive_terminal_time`, `.disjoint_interior_regions` |
| `multiple:705-710` separated scaled supports and common terminal time | `.separation_hypothesis`, `.scale_choice`, `.scaled_support_containment` |
| `multiple:711-716` summed solution, smoothness and rest data | `.simultaneous_solution`, `.smooth_before_terminal_time`, `.zero_initial_data` |
| `multiple:713-722` limsup in every region, energy/dissipation, boundary/gauge clauses | `.singularity_each_region`, `.finite_energy`, `.finite_dissipation`, `.no_slip_boundary`, `.pressure_gauge` |
| `conservative:723-728` periodic/bounded domain and exact potential class | `ConservativeForcingAPI.domain_choice`, `.globally_defined_periodic_potential`, `.conservative_force`, `.no_slip_boundary` |
| `conservative:729-735` smooth rest solution, incompressibility and zero pairing | `.smooth_solution_from_rest`, `.incompressibility`, `.force_velocity_pairing_zero` |
| `conservative:736-740` energy argument, nonnegativity, zero conclusion and exclusion of affine potentials | `.energy_identity`, `.nonnegative_terms`, `.identically_zero`, `.no_breakdown`, `.affine_potential_excluded` |

All fields are propositions because these APIs specify existence/properties; numerical constants are represented by hypotheses in the proposition fields. The current draft uses the registered T10/T14/T15 vocabulary and elaborates successfully. The field-level propositions intentionally remain independent interfaces pending implementation lemmas.

## Ambiguities and lemma needs

* The paper switches between torus and bounded-domain realizations; a shared domain-indexed solution class is needed to turn the proposition fields into concrete terms.
* A lemma is needed that disjoint support implies vanishing cross-advection, and another that finite sums preserve the registered force class and energy bounds.
* The affine non-isolation statement is a seminorm convergence lemma for the quadratic force correction.
* Conservative forcing requires the periodic integration-by-parts/no-slip pairing lemma and uniqueness of the zero-energy solution.

## Implementation candidates

`PacketImportAPI` and `ScalingAPI` in T14/T15 provide the localized packet and rescaling data. Existing Section 4 force-class and grid-observation contracts can supply concrete force-membership and observation shapes when these T24 leaves are implemented.
