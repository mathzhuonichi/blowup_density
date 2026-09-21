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

- **Theorem 3.6.** `T18.periodicInsertionStatement_holds` quantifies over
  scaling and correction records. `T19.insertion` formally constructs those
  inputs from admissible data and a reference solution, but fixes its placement
  and correction radius. This closes the case needed for density; it does not
  by itself close the article's quantification over an arbitrary prescribed
  coordinate ball.

The other Partial entries are Proposition 2.1, Lemma 3.5, and
Propositions 3.16 and 3.17. Their precise limits remain in the guide.

## The 22 Closed entries

The proof locations are linked in [RESULT_MAP.md](RESULT_MAP.md). The table
below records why a helper record is not being accepted as an unproved input.

| Article entry | Final proof and treatment of inputs |
|---|---|
| Theorem 1.1 | `Source.source_breakdown` selects the proved time-one candidate at the prescribed positive viscosity and applies `candidate_excludes_global_solution` to that very candidate and force. The helper derives finite-slab reference bounds from smoothness and compact support, applies proved positive-viscosity uniqueness, and contradicts blowup using continuity of a hypothetical global solution on the compact carrier through time one. No comparison theorem or estimate remains a caller input. |
| Lemma 2.2 | `packetImportFamily.select` supplies the actual packet and both energy identities; `selected_packet_every_viscosity` and `exists_packet_quiet` supply the early-zero interval. The candidate properties are proved, not assumed existence. |
| Theorem 3.1 | `mainStatement_holds` takes no density or critical-regularity record from the caller; `closedMainTheoremAPI` uses the constructed `periodicDensityAPI` and `criticalRegularityT`. |
| Lemma 3.2 | `localizationAPI` is a closed inhabitant of the six-field localization record. Its norm identities, estimate and endpoints are proved in its definition. |
| Proposition 3.3 | `scalingStatement_holds` proves scaling for the specified packet and geometric placement. All packet conditions, including energy and extension properties, are supplied by the compiled packet-import construction; no scaling estimate is a premise. |
| Lemma 3.4 | `localPotential` constructs the cutoffs, threshold and potential from the lemma's regularity, divergence and geometric hypotheses. No potential or cutoff theorem is an input. |
| Proposition 3.7 | `periodicDensityStatement_holds` uses the constructed `periodicDensityAPI`; `T19.insertion` closes the reference-solution branch. Density needs some localization ball, not every prescribed ball. |
| Proposition 3.8 | `criticalRegularityStatement_holds` supplies the constructed `criticalRegularityT`. Its continuation argument uses proved H3 restart, not the missing H1-uniform statement. |
| Corollary 3.9 | `nonDensityStatement_unconditional` uses `closedNonDensityAPI`, whose critical-regularity supplier is constructed. |
| Corollary 3.10 | `mixedRegionStatement_holds` uses `mixedRegionAPI` and the constructed fixed-ball insertion. No gluing record is supplied by the caller. |
| Corollary 3.11 | `strongClosureStatement_holds` uses `strongClosureAPI`, with the inserted families and energy convergence supplied internally. |
| Proposition 3.12 | `projectionStatement_holds` obtains both clauses from the constructed `projectionAPI`. |
| Remark 3.13 | `T18.packetForce_ne_zero` derives nonzero forcing from packet energy and blowup. Single-copy scaling and the correction record’s order-zero profile bound prove `forceAmplitude_lower`; `forceAmplitude_diverges` and `forceAmplitude_real_diverges` apply to every canonical record without additional premises. The binding discharges all raw packet clauses from the registered packet, and `T19.forceAmplitude_diverges` instantiates the constructed fixed-ball family. |
| Corollary 3.14 | `boundaryInsertion_from_data` takes only domain, ball, time, datum, force and reference-solution hypotheses. It instantiates `packetImportFamily.select`, `domainPlacementData`, `Contract.placeFrom` and the proved bounded-domain norm record before applying the insertion theorem. No packet, norm, correction or boundary-identity supplier is a caller argument. |
| Proposition 3.15 | `affineVariationPacket` is instantiated at the compiled selected packet. Remaining arguments are the stated affine vector and positive radius/time parameters. |
| Theorem 4.1 | `mainThresholds` is a closed record. Its density branch invokes `insertionLifespanV2_of_data`; its converse invokes the proved critical estimates. |
| Theorem 4.2 | `wholeSpaceInsertion_holds` selects one proved building block before the reference and region. It constructs an interior ball in every prescribed nonempty open set, keeps the given velocity and pressure definitionally, and proves every displayed clause for one family. The time margin is halved, so the original reference supplies strict continuation without an additional hypothesis. |
| Proposition 4.3 | `universal_of_memForceR` takes only viscosity, datum/force-class and smallness hypotheses. Maximal existence and fixed-force H7 continuation are supplied by compiled theorems. |
| Proposition 4.4 | `R44.main` takes only positive viscosity/horizon, force membership and the stated smallness bound. `rcritical2_endpoint_unconditional` supplies the conclusion. |
| Corollary 4.5 | `forceClasses` is a closed four-field record for the compact and rapid-decay classes, including the proved Schwartz-datum specialization. |
| Proposition 4.6 | `completedDensity` explicitly supplies `compactHomogeneousRealization` to both helpers that require it; the realization theorem is not left as an assumption. |
| Theorem 4.7 | `gridObservations_choose` supplies `compactHomogeneousRealization` and constructs the family. A given reference solution and the finite grids are part of the article's hypotheses. |

Thus the missing H1-uniform restart clause of Proposition 2.1 and the
prescribed-ball clause of Theorem 3.6 are not assumed by the Closed downstream
statements. Those statements use the fully formalized high-order restart and
constructed insertion cases, respectively. Theorem 4.2 now covers every prescribed
nonempty open set, and Theorem 4.7 additionally constructs a ball adapted to the
given grids.

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
checks this declaration together with all 30 registered interfaces; the full
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
