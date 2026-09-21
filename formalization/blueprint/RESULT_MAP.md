# Current article-to-code correspondence

Closed requires a Lean kernel-checked proof of the complete article statement,
with every auxiliary result formally proved and instantiated. Only the article
hypotheses and standard logical axioms remain. Partial means only part is formally
proved. A downstream result can be Closed if it uses only fully formalized cases.
See [the input-closure audit](CLOSURE_AUDIT.md) and [the axiom audit](DEPENDENCY_GRAPH.md).

| Article statement | Label | Coverage | Code locations |
|---|---|---|---|
| Theorem 1.1 | `thm:packet` | Closed | [`source_breakdown`](../../formalization/NSFormalization/Source/PacketBreakdown.lean#L76) |
| Proposition 2.1 | `prop:local` | Partial | [`localTheoryV2`](../../verification/Bindings/LocalTheoryV2.lean#L93); [`velocity_unique`](../../formalization/NSFormalization/Section4/A02/Uniqueness.lean#L120); [`exists_maximal_of_localSolution`](../../formalization/NSFormalization/Section4/A02/Maximal.lean#L157); [`extendsBeyond_of_memForceR'`](../../formalization/NSFormalization/Section4/A04/ShiftedExtension.lean#L247); [`torusLocalTheory`](../../verification/Bindings/TorusLocalTheory.lean#L483) |
| Lemma 2.2 | `lem:packetenergy` | Closed | [`energy_le_work_of_packet`](../../formalization/NSFormalization/Section3/T14/PacketEnergy.lean#L160); [`work_eq_square_of_packet`](../../formalization/NSFormalization/Section3/T14/PacketEnergy.lean#L106); [`exists_packet_quiet`](../../formalization/NSFormalization/Section4/I01/Quiet.lean#L53) |
| Theorem 3.1 | `thm:main` | Closed | [`mainStatement_holds`](../../formalization/NSFormalization/Section3/T21/MainAssembly.lean#L84) |
| Lemma 3.2 | `lem:localization` | Closed | [`localizationAPI`](../../formalization/NSFormalization/Section3/T13/Assembly.lean#L330) |
| Proposition 3.3 | `prop:scaling` | Closed | [`scalingStatement_holds`](../../formalization/NSFormalization/Section3/T15/Assembly.lean#L130) |
| Lemma 3.4 | `lem:potential` | Closed | [`localPotential`](../../formalization/NSFormalization/Section3/T16/Assembly.lean#L483) |
| Lemma 3.5 | `lem:correction` | Partial | [`correctionStatementAmended_holds`](../../formalization/NSFormalization/Section3/T17/Assembly.lean#L107) |
| Theorem 3.6 | `thm:insertion` | Partial | [`periodicInsertionStatement_holds`](../../formalization/NSFormalization/Section3/T18/Assembly.lean#L238); [`insertion`](../../formalization/NSFormalization/Section3/T19/Threading.lean#L126) |
| Proposition 3.7 | `prop:density` | Closed | [`periodicDensityStatement_holds`](../../formalization/NSFormalization/Section3/T19/Assembly.lean#L43) |
| Proposition 3.8 | `prop:critical` | Closed | [`criticalRegularityStatement_holds`](../../formalization/NSFormalization/Section3/T20/Assembly.lean#L53) |
| Corollary 3.9 | `cor:nondensity` | Closed | [`nonDensityStatement_unconditional`](../../formalization/NSFormalization/Section3/T21/MainAssembly.lean#L80) |
| Corollary 3.10 | `cor:mixed` | Closed | [`mixedRegionStatement_holds`](../../formalization/NSFormalization/Section3/T19/Assembly.lean#L47) |
| Corollary 3.11 | `cor:closure` | Closed | [`strongClosureStatement_holds`](../../formalization/NSFormalization/Section3/T19/Assembly.lean#L51) |
| Proposition 3.12 | `prop:projection` | Closed | [`projectionStatement_holds`](../../formalization/NSFormalization/Section3/T19/Assembly.lean#L55) |
| Remark 3.13 | `rem:peaks` | Partial | [`scalingStatement_holds`](../../formalization/NSFormalization/Section3/T15/Assembly.lean#L130); [`correctionStatementAmended_holds`](../../formalization/NSFormalization/Section3/T17/Assembly.lean#L107) |
| Corollary 3.14 | `cor:boundary` | Closed | [`boundaryInsertion_from_data`](../../verification/Bindings/BoundaryInsertionV2.lean#L27); [`boundedDomainNorm`](../../formalization/NSFormalization/Section3/T22/Assembly.lean#L25) |
| Proposition 3.15 | `prop:affine` | Closed | [`affineVariationPacket`](../../verification/Bindings/AffineVariation.lean#L109) |
| Proposition 3.16 | `prop:multiple` | Partial | [`multipleRegionsStatement_holds`](../../formalization/NSFormalization/Section3/T24/MultipleAssembly.lean#L51) |
| Proposition 3.17 | `prop:conservative` | Partial | [`conservativeForcing`](../../formalization/NSFormalization/Section3/T24/ConservativeAssembly.lean#L45) |
| Theorem 4.1 | `thm:Rmain` | Closed | [`mainThresholds`](../../verification/Bindings/MainThresholds.lean#L85); [`breakdownDenseR_of_subcritical`](../../verification/Bindings/DensityFromInsertion.lean#L30); [`mainThresholds_nonDensity`](../../verification/Bindings/MainThresholds.lean#L34) |
| Theorem 4.2 | `thm:Rinsert` | Closed | [`wholeSpaceInsertion_holds`](../../verification/Bindings/InsertionFromData.lean#L150) |
| Proposition 4.3 | `prop:Rcritical1` | Closed | [`universal_of_memForceR`](../../formalization/NSFormalization/Section4/R43/Universal.lean#L193) |
| Proposition 4.4 | `prop:Rcritical2` | Closed | [`main`](../../formalization/NSFormalization/Section4/R44/Prop44.lean#L24) |
| Corollary 4.5 | `cor:Rclasses` | Closed | [`forceClasses`](../../verification/Bindings/ForceClasses.lean#L46) |
| Proposition 4.6 | `prop:Renergy` | Closed | [`completedDensity`](../../verification/Bindings/CompletedDensity.lean#L14) |
| Theorem 4.7 | `thm:Rgrid` | Closed | [`gridObservations_choose`](../../verification/Bindings/GridObservations.lean#L47) |
