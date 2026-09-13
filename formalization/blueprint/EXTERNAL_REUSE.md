# External reuse and remaining adapters

Inspected on 13 September 2026. This record reports source and theorem-type
inspection, not a new Lean build. The local source archive contains later
changes than some of its historical handoffs; current file contents control.

## Upstream identity and reproducibility

| Source | Snapshot | Integration |
|---|---|---|
| OpenAI, `NavierStokesAndEuler` | Existing local source snapshot; the prior reference index attributes revision `8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`. The source copy has no `.git`, so commit equivalence is not independently established; per-file hashes identify the actual imported source. | `vendor/NavierStokesAndEuler`, Lean 4.34.0-rc2; the local Lake requirement and lockfile path both resolve here. |
| HeliCorgi, `ns-mns2-flowmap-bridge` | Git revision `de518485776d1d8de60f0c51151121df71e3ab6d`, fetched and read in this task. The spelling is HeliCorgi, not HeliCori. | `vendor/HeliCorgi`, Lean/mathlib 4.32.1; a separate source-only Lake project. |

The source manifests preserve both dependency lockfiles and licenses. The
HeliCorgi repository currently presents its results primarily as Lean source
and documentation; no separately identified HeliCorgi research-paper PDF is
represented as copied. The two original density manuscripts have both their
TeX and PDF in `paper/originals/local`. The OpenAI paper was already present in
`reference/` and was compared with the old local reference copy.

## Reuse matrix

Paths below are relative to the repository root. Declaration anchors were
read in the source snapshot; the summary does not inherit a README's build claim.

| Need | Existing source / declaration | Remaining manuscript obligation |
|---|---|---|
| Compact singular input | `formalization/NSFormalization/Source/ViscosityPacket.lean`, `selected_packet_every_viscosity`; OpenAI `NavierStokes/R3ActualCandidate.lean` and `R3CompactCandidate.lean` | Match the full merged Theorem 1.1, pressure/support and time conventions. Reuse the construction. |
| Concrete R3 heat, smoothing, Leray and convection | HeliCorgi `Formal/R3EndpointSafeProjectedDuhamel.lean`, `r3EndpointSafeProjectedDuhamelContract`, using `R3StokesH3Evolution`, `R3ProjectedSobolevConvection` | Coordinate/normalization and version transport; not a missing operator library. Its displayed equation has initial evolution minus the nonlinear Duhamel integral, without an external force term. |
| Local existence | HeliCorgi `Formal/R3EndpointSafeProjectedLocalExistence.lean`, `r3EndpointSafeProjected_exists_localMildSolution`; local `Source/OrdinaryForcedLocal.lean`, `exists_local` | HeliCorgi gives unforced H3 Bessel-coordinate mild solutions; the local OpenAI-based theorem has a fixed finite-order cylinder witness and ordinary L2 path. Connect forcing, real physical fields, common all-order interval and time regularity. Neither displayed conclusion alone is Proposition 2.1. |
| Restart and uniqueness | HeliCorgi `EndpointSafeTwoSpaceRestart`, `EndpointSafeTwoSpaceUniqueness`, `EndpointSafeTwoSpaceConcatenation`, `R3MildContinuation`; local `Source/OrdinaryViscousUniqueness.lean`, `velocity_unique` | Reuse unrestricted mild uniqueness and concatenation. Adapt shifted nonautonomous forcing, then identify the chosen maximal classical trajectory. |
| Continuation | HeliCorgi `Formal/R3MildContinuation.lean`, `r3EndpointSafeProjected_exists_extension_of_bounded`, `r3EndpointSafeProjected_blowup_dichotomy` | The source extends a bounded mild trajectory by an explicit positive time. The manuscript requires squared-H2 time integrability to imply higher-order bounds and restart for the forced classical field. These are different input criteria. |
| Physical PDE semantics | HeliCorgi `Formal/R3NavierStokesEquation.lean`, `r3EndpointSafeProjectedMild_navierStokes`; `Formal/R3SchwartzInitialData.lean`, `r3AdmissibleSchwartzDatum_navierStokes` | The capstone is unforced, spatially distributional and at interior times with a strong L2 time derivative. Extend to the actual forced classical H-infinity field and all manuscript initial data; do not assume H3 implies C-infinity. |
| Pressure gradient | HeliCorgi `Formal/R3HelmholtzPressure.lean`, `r3HelmholtzPressure_gradient` | For arbitrary L2 source F the gradient is `-(I-P)F`. Substitute convection minus forcing to match `(I-P)(f-convection)`, then transport normalization and required regularity. This generic pressure theorem is already reusable for nonzero forcing at the distributional level. |
| Tame products | Local `Paper3/CompleteTameProduct`, `SobolevPhysicalProduct`, `AngularTameProduct`; OpenAI Young convolution | Reuse complete physical multiplication and exact low-order H2 factors. Finish vector/tensor energy application, not another scalar product theory. |
| Critical embeddings | Local `Source/FractionalRealization.lean`, `realization_toDistribution`, `realization_norm_le_datum`; `Paper1/SchwartzCriticalEmbedding.lean`, `criticalFieldLp_norm_le_weighted`; OpenAI `NavierStokes/R3/SmoothSobolevL6.lean` | Actual distributional/Lp identifications are present. Match the full homogeneous completion, angular real-vector norms and derivative consequences for the fields used in critical PDE energy identities. A claim that the entire Riesz Fourier bridge is absent is stale. |
| Compact correction and insertion | Local `Paper1/RadialPotential`, `LocalCutoff`, `CorrectionForceProfile`; `Source/LocalApproximatingInsertion`, `exists_local_approximating_insertion`; `Source/InsertionBreakdown`, `insertion_lifespan_eq` | The source lifespan uses `SmoothLifespan.Flow`, not the manuscript's chosen maximal H-infinity solution. Reuse actual insertion; discharge the class bridge and preserve one common family. |
| Completed force density | Local `Paper3/AngularRealVectorBochner.lean`, `exists_angular_real_vector_positive_physical_approx` | Real angular Euclidean-vector positive-time physical Bochner approximation is already present. Identify the exact manuscript completion and finish the homogeneous H-minus-one variant and singular-force assembly. |
| Grid observations | Local `Paper3/ActualGridObservations.lean`, `actual_force_cell_averages_eq`, `actual_finite_grid_velocity_force_observations` | Force means are derived from the actual PDE. Attach them to the same manuscript insertion and convergence family; no need to rebuild the grid library. |

## External mathematical inputs in the revised appendices

Appendix A now cites Tao's published forced local theory rather than asking the
article to rebuild every local analytic foundation. Theorem 5.4(ii)-(iv) and
its proof on printed pages 52-53 supply the relevant whole-space starting
point; the proof explicitly allows smooth Sobolev data beyond the Schwartz
class. The local saved PDF and the
[publisher PDF](https://msp.org/apde/2013/6-1/apde-v6-n1-p02-s.pdf) were consulted.
Viscosity, pressure recovery, time smoothness and the stated continuation
criterion remain explicit application steps. Section 4 needs no mean reduction.

Appendix B uses Tao's homogeneous Sobolev inequality (Appendix A, (A.11)) and
retains the realization and normalization arguments. Taylor's compact-manifold
embedding is for the later periodic branch. Existing formal Riesz/embedding
components are reusable evidence, not mandatory proof-development subprojects.
Fujita-Kato is historical background in this merged version; HZZ weak
nonuniqueness, Clay's problem statement and numerical error estimates do not
supply the Section 4 classical forced local theorem.

Primary code sources:
[OpenAI](https://github.com/openai/NavierStokesAndEuler) and
[pinned HeliCorgi source](https://github.com/HeliCorgi/ns-mns2-flowmap-bridge/tree/de518485776d1d8de60f0c51151121df71e3ab6d).
Further source provenance remains in [reference/README.md](../../reference/README.md).

## Current audit findings

The static scan ignores nested comments and strings, follows copied-module
imports, and reports explicit admission/axiom tokens. It does not inspect
compiled theorem dependencies or Mathlib's kernel axioms.

1. The legacy umbrella imports `Paper1/BoundaryCorollary.lean`, with a genuine
   `sorry` in `exists_interior_noSlip_insertion` at line 90. Its hypotheses also
   require a nonempty set in R3 to be both open and compact, and the displayed
   fields are not adequately linked to the existential bounded flow. This is
   not the merged interior-ball corollary. Preserve the file as source history;
   exclude it from a future Section 4 certification root.
2. `Citations/WholeSpaceForcedLocalInterface.lean` and related modules contain
   schematic type/Prop fields and explicit axioms. They are not concrete
   formalizations of cited PDE theorems. None is imported by the copied umbrella.
3. Comparator challenge placeholders are preserved in the upstream source
   package, but should not be interpreted as proved manuscript inputs.
4. Old source counts and historical all-green claims do not apply to the new
   snapshot without a fresh build and theorem audit. No clean full-paper
   certification is claimed here.

The plan checker succeeds when packaging and the graph are consistent; it
reports inherited admissions rather than silently deleting or proving them.
This separation is necessary to honor the instruction not to write Lean code.
