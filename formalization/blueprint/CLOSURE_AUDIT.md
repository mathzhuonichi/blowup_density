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

## Closure status

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
| Proposition 2.1 | `localForceTheory` proves local existence with full Sobolev regularity and pressure recovery, maximal existence, uniqueness and actual integral continuation without global time-integrability or temporal support assumptions. `SmoothForceR` uses smooth Sobolev paths on the future half-line. `SmoothForceT` uses restriction from smooth periodic representatives on every finite closed future slab, imposing no condition on the original field at negative times. Whole-space continuation uses a cutoff equal to one on `[0,S+1]`; periodic continuation uses finite-window force bounds and uniform H3 restart. The separate H1 restart contracts remain statements for the density force classes. |
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
| Proposition 3.16 | `multipleRegionsStatementV2_holds` conjoins the torus theorem and the bounded-domain no-slip theorem. The latter constructs all thirty fields from raw packet projections, an arbitrary prescribed nonempty bounded open domain, and disjoint interior balls. Concrete components supply every support, scaling, blow-up and norm hypothesis; no solution or analytic supplier is a caller premise. The registered packet gives a unit-box witness at viscosity and terminal time one. |
| Proposition 3.17 | `conservativeForcing` proves the periodic potential-force branch. `conservativeForcingOmega` proves the arbitrary nonempty bounded open domain branch using the proved open-set integration-by-parts identity and the difference-energy identity against rest. The potential is smooth only near the closed spatial slab during the lifespan, without a global smoothness assumption. `conservativeForcingStatementV2_holds` registers both branches without an extra boundary identity or solution supplier. |
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
checks this declaration together with all 37 registered interfaces; the full
source snapshot and collected axiom sets are recorded in `AXIOM_AUDIT.json`.

## Verification

The Linux build checks the final boundary theorem with its concrete suppliers
in one import environment. An unused duplicate declaration in `Bindings.Scaling`
was removed so the packet and scaling modules can be imported together.
The article axiom audit checks every guide declaration transitively; the source
snapshot hash is checked against the local tree by
`python3 experiments/check_formalization_plan.py --check`.
The statement-level observations above are a source review, not an automated
proof that informal prose and Lean expressions have identical semantics.

The R42 acceptance declaration now checks `wholeSpaceInsertionStatement`, the
full raw-data prescribed-region statement. In particular the building block is
chosen before the reference and region, all conclusions share one family, and
there is no externally supplied correction or scaling record. Validation and
current source hashes are recorded in `AXIOM_AUDIT.json` and the generated graph.

## Scope generalization after PR #475 (21 September 2026)

The changes were developed from merge commit
`ce68392c4e224e80a04b12305f6d8ee482f5d9b0`, with unrelated worktree changes
preserved. Proposition 3.16 now accepts every nonempty bounded open domain.
Proposition 3.17 uses the same domain class and potentials smooth on a
neighborhood of `[0,T) × closure Ω`. Their independent V2 specifications and
bindings were generalized together; the integration identity is the proved
`ibp_of_isOpen_isBounded`, without a boundary-shape premise.

Proposition 2.1 has the new independent V3 interface
`Contracts/V3/LocalForceTheory.lean`, implemented by
`Bindings.LocalForceTheory.localForceTheory`. Its nine fields retain full
local Sobolev regularity, pressure recovery, maximal development, uniqueness
and actual continuation of the original velocity. Periodic pressure agreement
and whole-space pressure-gauge uniqueness are explicit. The force predicates
are stated in the contract: smooth future Sobolev paths on the whole space,
and finite closed-slab smooth periodic representatives on the torus. The
regression examples admit permanent forcing and periodic forces with arbitrary
negative-time behavior. The density force classes and their global norms
retain their original definitions.

The pinned Linux build passed all 37 registered acceptance declarations
(11,053 build jobs). A fresh audit checked 77 declarations across all 27
article entries, with no forbidden axioms or source admission tokens. The
local and Linux trees have the same 2,300-file source fingerprint:
`8c192a60db92a48dfda1d38db3931f4ab0a2913f94196b3ce92e08bbc415085c`.
All four mutation checks passed: an implementation refactor was accepted,
and an admitted proof, an extra axiom and an unsupported hypothesis removal
were rejected for the expected reasons. The updated six-page guide was rebuilt
and every page was visually checked.

Reproduce the checks with the pinned toolchain in Linux:

```sh
lake -d verification build
python3 experiments/audit_article_axioms.py --build --workers 1 --output-dir /tmp/article-audit
python3 experiments/test_contract_mutations.py --skip-build
python3 experiments/check_formalization_plan.py --check
python3 experiments/check_contracts.py --summary
python3 experiments/test_contract_policy.py
```

Run these commands from the repository root in Linux with the pinned
toolchain available on `PATH`.

## Consolidated publication snapshot (22 September 2026)

The article and guide PDFs now live with their sources under `paper/`.
All PDF links, the guide's external article labels and the document checker
use that location. The original manuscripts, citation corpus, upstream
source copies and licenses remain available for provenance checks.

Before compressing the publication history, the complete local history,
uncommitted source snapshot and all 477 remote branch tips were backed up
outside the repository; the remote mirror passed `git fsck --full`.
The CI module selector now checks all committed modules when an initial push
or history rewrite makes its base commit unavailable.

Validation of this snapshot passed a Linux build explicitly selecting all
2,289 Lean modules (11,053 jobs), all 13 architecture-policy regression tests,
the source-fingerprint check and the reader-document checks. Both PDFs were
rebuilt without final LaTeX warnings, and the affected layouts were inspected.
The Lean source fingerprint and kernel-audit evidence above are unchanged.
For memory-constrained Linux environments, use `LEAN_NUM_THREADS=1`.
