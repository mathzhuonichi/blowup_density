# Formal proof closure of the article statements

Closed requires a Lean kernel-checked proof of the complete article statement,
with every auxiliary result formally proved and instantiated. No unproved
analytic theorem, existence supplier, admission or extra axiom may be left to
the caller. The article's quantified objects and stated hypotheses remain:
for example, positive viscosity or a given smooth reference solution are
conditions of a theorem, not unproved auxiliary inputs. The permitted logical
axioms are `propext`, `Classical.choice` and `Quot.sound`.

This review checks declaration types, the definitions of their statement
records, and the actual construction of their analytic inputs. It complements
[the kernel audit](AXIOM_AUDIT.json): axiom collection alone cannot distinguish
an assumed analytic theorem from an ordinary hypothesis.

## Remaining scope

There are no Partial article entries. All 27 mapped statements are supplied by
kernel-checked declarations with their analytic and construction inputs
instantiated. Scope qualifications that remain outside the mapped statements
are recorded in the guide and registry descriptions.

## The 27 Closed entries

The proof locations are linked in [RESULT_MAP.md](RESULT_MAP.md). The table
below records why a helper record is not being accepted as an unproved input.

| Article entry | Final proof and treatment of inputs |
|---|---|
| Theorem 1.1 | `Source.source_breakdown` selects the proved time-one candidate at the prescribed positive viscosity and applies `candidate_excludes_global_solution` to that very candidate and force. The helper derives finite-slab reference bounds from smoothness and compact support, applies proved positive-viscosity uniqueness, and contradicts blowup using continuity of a hypothetical global solution on the compact carrier through time one. No comparison theorem or estimate remains a caller input. |
| Proposition 2.1 | `localTheoryV2` and `torusLocalTheory` supply existence, uniqueness, maximality and the integral continuation routes. `continuationV3_holds` and `torusLocalTheoryV2_holds` add fixed-force H¹-uniform restart and endpoint continuation on both domains. Their suppliers prove the enstrophy differential inequality, uniform ODE barrier, endpoint H² integrability and the maximal-lifespan contradiction before applying the established H⁷/H³ continuation routes; no quantitative local-existence input remains a caller hypothesis. |
| Lemma 2.2 | `packetImportFamily.select` supplies the actual packet and both energy identities; `selected_packet_every_viscosity` and `exists_packet_quiet` supply the early-zero interval. The candidate properties are proved, not assumed existence. |
| Theorem 3.1 | `mainStatement_holds` takes no density or critical-regularity record from the caller; `closedMainTheoremAPI` uses the constructed `periodicDensityAPI` and `criticalRegularityT`. |
| Lemma 3.2 | `localizationAPI` is a closed inhabitant of the six-field localization record. Its norm identities, estimate and endpoints are proved in its definition. |
| Proposition 3.3 | `scalingStatement_holds` proves scaling for the specified packet and geometric placement. All packet conditions, including energy and extension properties, are supplied by the compiled packet-import construction; no scaling estimate is a premise. |
| Lemma 3.4 | `localPotential` constructs the cutoffs, threshold and potential from the lemma's regularity, divergence and geometric hypotheses. No potential or cutoff theorem is an input. |
| Lemma 3.5 | `correctionStatementArticle_holds` derives slab smoothness, periodicity and divergence from the classical reference after zero extension. `article_force_identification` transfers the force and all displayed bounds to the original velocity; packet support is a registered packet projection. No correction or estimate supplier is an input. |
| Theorem 3.6 | `T19.periodicInsertion_from_data` constructs placement, scaling and correction from the registered packet and the reference solution for every prescribed positive-radius ball with closure in the cube interior. Only the article's hypotheses remain. Zero-extension equality transfers history, divergence and energy to the given reference; lattice separation reduces the support to a single shrinking ball in the chart. The V2 binding retains all four clauses and the negative-order limit. |
| Proposition 3.7 | `periodicDensityStatement_holds` uses the constructed `periodicDensityAPI`; `T19.insertion` closes the reference-solution branch. Density needs some localization ball, not every prescribed ball. |
| Proposition 3.8 | `criticalRegularityStatement_holds` supplies the constructed `criticalRegularityT`. Its continuation argument uses the proved H3 restart and does not depend on the stronger H1-uniform statement. |
| Corollary 3.9 | `nonDensityStatement_unconditional` uses `closedNonDensityAPI`, whose critical-regularity supplier is constructed. |
| Corollary 3.10 | `mixedRegionStatement_holds` uses `mixedRegionAPI` and the constructed fixed-ball insertion. No gluing record is supplied by the caller. |
| Corollary 3.11 | `strongClosureStatement_holds` uses `strongClosureAPI`, with the inserted families and energy convergence supplied internally. |
| Proposition 3.12 | `projectionStatement_holds` obtains both clauses from the constructed `projectionAPI`. |
| Remark 3.13 | `T18.packetForce_ne_zero` derives nonzero forcing from packet energy and blowup. Single-copy scaling and the correction record's order-zero profile bound prove `forceAmplitude_lower`; `forceAmplitude_diverges` applies to every canonical record without additional premises. The binding discharges all raw packet clauses from the registered packet, and `T19.forceAmplitude_diverges` instantiates the constructed fixed-ball family. |
| Corollary 3.14 | `boundaryInsertion_from_data` takes only domain, ball, time, datum, force and reference-solution hypotheses. It instantiates `packetImportFamily.select`, `domainPlacementData`, `Contract.placeFrom` and the proved bounded-domain norm record before applying the insertion theorem. No packet, norm, correction or boundary-identity supplier is a caller argument. |
| Proposition 3.15 | `affineVariationPacket` is instantiated at the compiled selected packet. Remaining arguments are the stated affine vector and positive radius/time parameters. |
| Proposition 3.16 | `multipleRegionsStatementV2_holds` conjoins the torus theorem and the bounded-domain no-slip theorem. The latter constructs all thirty fields from raw packet projections, prescribed box-or-regular-level domain geometry, and disjoint interior balls. Concrete components supply every support, scaling, blow-up and norm hypothesis; no solution or analytic supplier is a caller premise. The registered packet gives a unit-box witness at viscosity and terminal time one. |
| Proposition 3.17 | `conservativeForcing` proves the periodic potential-force branch. `conservativeForcingOmega` proves the bounded box-or-regular-level-domain branch from the constructed boundary integration-by-parts identity and no-slip uniqueness. `conservativeForcingStatementV2_holds` registers both branches without an extra boundary identity or solution supplier. |
| Theorem 4.1 | `mainThresholds` is a closed record. Its density branch invokes `insertionLifespanV2_of_data`; its converse invokes the proved critical estimates. |
| Theorem 4.2 | `wholeSpaceInsertion_holds` selects one proved building block before the reference and region. It constructs an interior ball in every prescribed nonempty open set, keeps the given velocity and pressure definitionally, and proves every displayed clause for one family. The time margin is halved, so the original reference supplies strict continuation without an additional hypothesis. |
| Proposition 4.3 | `universal_of_memForceR` takes only viscosity, datum/force-class and smallness hypotheses. Maximal existence and fixed-force H7 continuation are supplied by compiled theorems. |
| Proposition 4.4 | `R44.main` takes only positive viscosity/horizon, force membership and the stated smallness bound. `rcritical2_endpoint_unconditional` supplies the conclusion. |
| Corollary 4.5 | `forceClasses` is a closed four-field record for the compact and rapid-decay classes, including the proved Schwartz-datum specialization. |
| Proposition 4.6 | `completedDensity` explicitly supplies `compactHomogeneousRealization` to both helpers that require it; the realization theorem is not left as an assumption. |
| Theorem 4.7 | `gridObservations_choose` supplies `compactHomogeneousRealization` and constructs the family. A given reference solution and the finite grids are part of the article's hypotheses. |

The H¹-uniform restart clauses of Proposition 2.1 and the prescribed-ball
clause of Theorem 3.6 are proved rather than assumed by downstream statements.
Theorem 4.2 covers every prescribed nonempty open set, and Theorem 4.7
additionally constructs a ball adapted to the given grids.

## Theorem 1.1 source and downstream use

The article restates Theorem 1.1 on page 1 of the saved OpenAI paper, including
same-force global nonexistence; no extra conclusion or hypothesis was added.
The upstream `ComparatorR3Theorem.lean` is byte-identical to the saved archive
at revision `8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538` and proves the
comparator formulation. The local `Source.source_breakdown` now proves the
complete `NavierStokesR3.ProblemStatement.breakdownStatement` with the locally
selected candidate, retaining singular time one and the same force throughout.
The earlier Partial label reflected a missing connection, now formally proved.

The two downstream construction routes still consume only the proved candidate
fields: periodic gluing uses `Bindings.packet`, `packetImportFamily.select`
and `Section3.T19.insertion`; whole-space gluing uses
`Bindings.insertionFromData_packet`. Their exact lifespan conclusions use
proved uniqueness and blowup. `PacketAPI` contains no assumed global
nonexistence field. The new full theorem strengthens the public coverage
without changing those downstream constructions or their hypotheses.

`Tests.Packet.checkedPacketBreakdown` checks the exact full statement and its
transitive axioms, alongside the existing construction check. The guide's
kernel audit also includes `Source.source_breakdown`. The Linux acceptance run
checks this declaration together with all 36 registered interfaces; the full
source snapshot and collected axiom sets are recorded in `AXIOM_AUDIT.json`.

## Verification

The Linux build checks the final boundary theorem with its concrete suppliers
in one import environment. An unused duplicate declaration in `Bindings.Scaling`
was removed so the packet and scaling modules can be imported together.
The article axiom audit checks every guide declaration transitively; the source
snapshot hash is checked against the local tree by `make check`.
The statement-level observations above are a source review, not an automated
proof that informal prose and Lean expressions have identical semantics.

The R42 acceptance declaration now checks `wholeSpaceInsertionStatement`, the
full raw-data prescribed-region statement. In particular the building block is
chosen before the reference and region, all conclusions share one family, and
there is no externally supplied correction or scaling record. Validation and
current source hashes are recorded in `AXIOM_AUDIT.json` and the generated graph.
