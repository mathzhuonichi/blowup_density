# T23 proof split — interior no-slip insertion (`cor:boundary`)

Planning lane 449, 2026-09-19. Completed planning inventory, persisted first as a skeleton and then refined in section commits. No proof or registration is asserted by this document.

Model legend: **codex-sol = bookkeeping/transport; codex-astra = analytic core**. Sizes: S = focused transport; M = several dependent lemmas; L = new analytic theorem or substantial construction.

## 0. Ground rules and supplier audit

This is a plan, not a proof certificate. `Spec` below means `research/T23/Spec.lean`; `S3`, `S4`, `P1`, `C1`, `C2`, `B` abbreviate `formalization/NSFormalization/Section3`, `formalization/NSFormalization/Section4`, `formalization/NSFormalization/Paper1`, `verification/Contracts/V1`, `verification/Contracts/V2`, `verification/Bindings`. All citations use the checked-out snapshot. Paper text was read with `sed -n '600,667p' paper/sections/03-torus.tex`: norms at 603–629, statement at 632–651, local construction at 654–655, negative tail at 659–660, fixed support and uniqueness at 661–664.

**Peeling rule.** An analytic obligation becomes its own named theorem and probe before any constructor uses it. A failed route is split at its exact residual; neither a conclusion-shaped hypothesis nor an arbitrary `Prop` field closes a unit. S = focused transport; M = one known argument with supporting lemmas; L = substantial analytic development. Every new domain theorem must retain the actual reference, ball, packet, correction, and scale range. No proofs or edits to existing Lean modules in lane 449.

**Consume versus thread.** Registered IDs are `I02.correction`, `I02.correction_v2`, `I03.scaling` (`verification/contracts.json:27,38,71`) and `T04.bounded_domain_norm` (`:478`). Whole-space records are consumed, not new external assumptions of the corollary. Internally thread the *chosen matching* correction and scaling records: `C1/Scaling.lean:480` returns `A.correction = C`, which must be retained. Registration is conditional on supplier hypotheses: `C1/Correction.lean:542` needs globally smooth, globally divergence-free reference fields and their equation on the whole spatial slab. A `ClassicalSolutionOmega` supplies those only on Ω (`Spec:555,565,569`). A random inhabited correction does not match the given reference. U2 must close this gap locally or by a proved solenoidal extension; do not silently convert domain solutions to whole-space solutions.

T22's copied record (`Spec:278`) is historical. At proof/registration time use `C1/BoundedDomainNorm.lean:74,109` and the inhabited `B/BoundedDomainNorm.lean:81,88`; its canonical implementation is `S3/T22/Assembly.lean:25`. The `norms` parameter may be kept in a compatibility wrapper but must be the registered type, with an explicit three-field adapter for the copied type. Definition bridges and record conversions already have a model in `B/BoundedDomainNorm.lean:23–67`. No new analytic T22 supplier remains to prove.

Thread the given domain reference, free center/ball and packet raw fields. Follow the raw-field convention of `S3/T18/Insertion.lean:37` and `research/T18/REPORT_422.md:5`: packet velocity, pressure, force, carrier, energyBound, dissipationBound; proof-side code cannot import contracts. Define one canonical domain solution record and one domain insertion bundle. Domain/contract copies require fieldwise maps and round trips; equality of two inductive structures is not an `rfl` definition bridge. T18's bundle itself cannot be used: it requires torus `PlacementData`, `ClassicalSolutionT`, and torus correction/scaling.

**Exact T18 transfer boundary.** Direct generic helper reuse is available for `S3/T18/Momentum.lean:24` (`contDiff_two_of_smooth`). The full-space slice helpers at `:30,37,45` apply only to genuinely full-space smooth summands; domain versions require local open-neighborhood arguments. No theorem taking `InsertionData` transfers directly to a domain reference. Re-prove U1 formulas/thresholds from the same elementary argument (`Insertion.lean:79–128`); U2 force closure by intersecting slab neighborhoods and unioning time supports (`ForceClass.lean:23,47,53`); U3 kinematics (`Kinematics.lean:20,29,71,77`); U4 divergence (`Divergence.lean:26,43`); U5 cross terms (`CrossTransport.lean:46,82,90`); U6 residual algebra (`Momentum.lean:82,110`). Their proof patterns and underlying whole-space algebra transfer, not their torus theorem types. Pressure-mean lemmas `Momentum.lean:59,67` and `Lifespan.lean:48,101` need Ω-integrals, volume factors and new smoothness proofs. U8 lifespan (`Lifespan.lean:273,300,338`) supplies a proof pattern only: replace periodic compact-cube boundedness with compact closure Ω, and T11 uniqueness with U7. T11 `velocity_unique` (`S3/T11/Uniqueness.lean:27`) takes `ClassicalSolutionT`; `Assembly.lean:184,374` is torus local/H³ theory, not a domain solver.

**Snapshot and safe imports.** The checked-out T18 theorem modules are U1–U6 and U8, as the cited declarations verify. U7 and U9–U11 are upstream lanes 435/443/445 per the task brief, not claimed landed here; U12 is an integration gate. `P1/BoundaryCorollaryCorrected.lean:19` is a useful geometric proof, but its line 1 imports `BoundaryCorollary`; `BoundaryReferenceRestriction.lean:1` does too, and `BoundaryCorollary.lean:90` contains `sorry`. Do not import these candidates under the house rule. Recreate their short geometry in a clean module. `corrected_interior_noSlip_insertion` (`:45`) merely projects an assumed contract; it is not the missing construction. `P1/LocalizationBoundary.lean:189` is periodic interpolation, not the T22 zero-extension theorem; use registered T22 instead.

**Statement gate G0 (new audit finding).** As written, `boundaryInsertionStatement` (`Spec:1037–1050`) universally quantifies raw `D : CutoffData` with no compatibility or positivity hypothesis. `CutoffData` has seven data fields only (`:135,140,146,152,158,164,170`). Choose `D.ε₀ = 0`: API fields `eps_pos` (`:728`) and `eps_le_cutoff` (`:734`) imply `0 < ε₀ ≤ 0`. Thus for any admissible other inputs there can be no API witness. Registered suppliers cannot fix a universally prescribed bad D. U9 must obtain an owner-approved statement repair, preferably existentially choosing D from the local construction and retaining its identities, as reconciliation §3 intends. Adding only `0 < D.ε₀` is insufficient: an arbitrary correction can violate divergence, support and cancellation. Keep the current Spec untouched and report this obstruction explicitly.

## 1. Units and exhaustive field ownership

All targets below refer to exact current Spec field types; G0 means the final quantified theorem cannot yet be proved. Suggested new modules live under `S3/T23/`; names are proposed, not claims of existing files.

### U-CAN — canonical vocabulary (lane 480, 2026-09-19)

**Status: complete, kernel checked.** `Section3/T23/Boundary.lean` is the public
entry point for the 48-field raw `BoundaryInsertionAPI`, literal
`boundaryInsertionStatement`, and G0's existential `boundaryInsertionStatement'`.
These are interfaces/definitions, not a construction or registration of T23.
The literal zero-cutoff instance is refuted by `boundaryInsertionAPI_zero_cutoff`.
The earlier G0 location gap is closed; U2's analytic matching obligations remain.

Canonical ownership (all T23 names below are in `NSFormalization.Section3.T23`):

| Consumers | Canonical names / defining module |
|---|---|
| U3–U6, U8, U9 | `DomainPlacementData u p f K`, `domainPlacementData`, `interiorBall_in_domain` — `Placement` (16 fields) |
| U3–U6, U8, U9 | `CutoffData`, `localCorrectionData`, `LocalCorrectionCore`, `correctionForce` — `LocalCorrection` (one seven-field cutoff record); the supplier bridge remains `LocalCorrectionBridge` |
| U3, U4, U8, U9 | `ClassicalSolutionOmega`, `SmoothOnClosedSlab`, `IsBoxDomain`, `IsRegularLevelDomain`, `IsBoundedBoxOrSmoothDomain`, `initialClassOmega`, `MemForceOmega`, `forceClassOmega` — `DomainSolution`; imported through `NoSlipUniqueness` |
| U3–U6, U8, U9 | `BoundaryInsertionAPI ν u p f K M E place Ω norms a g r δ D reference` — `Boundary`; preserve its 48 fields and order |
| U3, U8 | `domainMaximalLifespan`, `IsMaximalDomainSolution`, `domainPressureMean`, `domainNormalizePressure` — `Boundary` |
| U5, U6 | `domainEnergyEssSup`, `domainEnergyGradient`, `domainEnergyENorm`, `domainForceSobolevENorm`, `zeroExtForceSobolevENorm` — `Boundary`; use `NSFormalization.Section3.T22.BoundedDomainNormAPI` and its existing norm vocabulary from `T22.Domain` |
| U4, U5, U8 | `prescribed_closedBall_compact`, `exists_inner_closedBall`, `prescribed_closedBall_disjoint_frontier` — `Geometry`; frontier separation explicitly requires `IsOpen Ω` |
| U2, U9 | `WholeSpaceCorrectionAPI ν u K` — `WholeSpaceCorrection`, the full 73-field raw adapter for registered I02; both fieldwise directions checked in the boundary probe |
| U9 | `boundaryInsertionStatement'` — `Boundary`; choose matching `C` and `D` existentially with all seven cutoff identities, positive radius and both ball inclusions. The unprimed definition preserves the literal false-instance-bearing wording only. |

No existing Lean module needed a deduplication edit: this checkout already has
one T23 cutoff record and one domain family (478's continuation moved the latter
to `DomainSolution`). Do not introduce a new copy in subsequent units.
The raw packet order is velocity, pressure, force, carrier, energy bound,
dissipation bound; no packet validity or analytic supplier is fabricated here.
The probe embeds the untouched Spec and checks bidirectional field conversions,
round trips, the exact literal/repaired binders, and the repaired existential's
full supplier/cutoff matching. Registration policy and the remaining analytic
units in §4 are unchanged.

### U1 — cube-free placement and interior geometry (M, codex-sol)

**Status (lane 476, 2026-09-19): complete.** `Section3/T23/Placement.lean`
constructs all 16 raw-field `DomainPlacementData` fields for every prescribed
positive-radius interior ball and proves `interiorBall_in_domain`; the
translated `(5,5,5)` probe exercises every field and confirms that the domain
need not contain the origin.  Axiom audit: exactly
`[propext, Classical.choice, Quot.sound]` for every introduced declaration.

Target all **16** `DomainPlacementData` fields: `T:378`, `time_pos:382`, `chartCenter:386`, `chartRadius:390`, `chartRadius_pos:394`, `x₀:398`, `x₀_mem:402`, `Kstar:407`, `Kstar_compact:412`, `carrier_subset:417`, `force_projection_subset:423`, `ε₀:429`, `eps_pos:433`, `eps_le_one:437`, `eps_time:443`, `eps_space:449`; API `interiorBall_in_domain:720`. Dependencies: packet compact support, prescribed positive T and prescribed closed ball inside Ω; no T18 assembly dependency.

Construct Kstar as the union of packet carrier and the spatial image of compact force support (verified route `B/CorrectionV2.lean:537`, `isCompact_carrierStar`). Choose a finite radius R bounding Kstar and positive margin `chartRadius - dist x₀ chartCenter`. Choose one positive threshold below 1, a strict time bound, and margin/(R+1), with a factor 1/2 to retain strict inequalities at the closed upper endpoint. Prove affine-image containment. This works for any given interior ball and any x₀ in it, including Ω=(1,2)³; no origin or cube condition. Also prove closed-ball compactness, separation from frontier Ω, and existence of a smaller ball around x₀. The geometry proof at `P1/BoundaryCorollaryCorrected.lean:19` is a template only (unsafe import noted above). A concrete translated-ball placement probe must satisfy eps_time, not just list the fields.

### U2 — local correction supplier and compatibility (L, codex-astra)

**Lane 481 U2b status (2026-09-19): matching and correction estimates closed.**
`MatchingSupplier.lean` proves local correction/force transport, both exact U2
cross transports, the seven-field supplier cutoff, and the domain-reference
locality bridge. `CorrectionEstimates.lean` proves energy restriction, local
energy/mixed estimates, and the positive Sobolev-force estimate. The extended
`T23-U2b-matching-supplier_closes.lean` probe actually constructs registered
I02 V2/I03 records from the local reference, retaining `A.correction = C` and
`D.ε₀ = C.ε₀ = A.ε₀`, with all three estimates and both cross terms at that D.
Its literal supplier-cutoff variant additionally retains all seven G0 cutoff
identities. Record construction remains in the contract-facing research layer
because implementation modules cannot import Contracts/Bindings; U9 can move
that checked bridge to its binding. No full BoundaryInsertionAPI assembly,
V1 amendment, U6 path-to-slice comparison, or G1 completion is claimed.
See `REPORT_481.md` for the inner-radius convention and exact gate results.

**Lane 477 status (2026-09-19): partial, kernel checked.** Exact G0 zero-cutoff
API instance refuted and existential repair defined in the research probe;
canonical `StatementRepair` contains only the raw obstruction pending domain
API vocabulary. One actual `D` now has local potential/curl, global smooth
divergence-free correction, cancellation, Ico cross transports, compact smooth
force and uniform correction/force jet bounds. Fixed solenoidal spatial/window
extensions and global correction/force agreement are proved. Remaining: consume
and retain matching I02/I03 records and close energy/mixed/Sobolev norm fields
at this `D`; no full supplier or U9 registration is claimed. See
`REPORT_477.md`, `ATTEMPTS_U2.md`, and `SPEC_ISSUES.md` G0 addendum.


Targets the seven cutoff data fields `Spec:135–170` and their construction identities; API `crossTransport_background_advects_packet:879`, `crossTransport_packet_advects_background:888`. Dependencies: U1; statement repair G0 for end-to-end assembly. Produce one positive cutoff threshold and one D with its actual smoothness, curl/divergence, cancellation, support and force estimates, tied to the given reference and x₀. These are named proved lemmas, not placeholder fields.

I02 gives `correction_support:359`, `correction_support_ball:364`, `correction_cancels_germ:385`, `force_support:433`, `force_support_ball:444`, `force_formula:415` in `C1/Correction.lean`. But `reference_divergence_free:230` is global. Preferred bridge to investigate: take the radial potential in a slightly larger interior ball, multiply it by a fixed compact cutoff equal to one near the construction ball, and take curl to obtain a globally smooth solenoidal reference extension agreeing there. Extend pressure smoothly with a cutoff and define its exterior force by the residual; it agrees with g where needed. Prove agreement of potential/correction/force jets on their supports, including the time window through T, before consuming I02/I03. `B/CorrectionV2.lean:87–100` still requires the global hypotheses; it does not supply this bridge. Its prescribed-K version (`C2/Correction.lean:136,155`) can cover Kstar, or separately shrink the packet-force range using U1. If extension transport is longer, peel the local versions of the I02 analytic lemmas; do not claim the registered record itself has weaker hypotheses.

Cancellation gives both cross terms by the open-neighborhood argument of `S3/T18/CrossTransport.lean:46`; use the un-periodized packet. I02 cancellation is on Ioo, while targets use Ico: handle t=0 by the packet's inactive past and derivative of the zero slice. Prove global cross identities despite reference smoothness only near Ω: away from packet/correction support the relevant fields are locally zero, so no exterior regularity assumption is needed.

### U3 — triple, kinematics, momentum and solution record (L, codex-astra)

**Lane 482 status (2026-09-19): complete with the authorized supplier/U4 threading.**
`PressureNormalization.lean`, `Triple.lean`, and `Solution.lean` prove the 18
triple fields, pressure normalization analysis, and the ten-field domain solution
constructor / API `solution`. Theorems retain the same raw placement, correction
and reference; U2's existing `LocalCorrectionCore`, same-scale packet facts and
U4 no-slip are explicit parameters. The threshold also retains independent I03
and geometry bounds. Original-Spec field probe and all gates pass; 42 production
declarations have exactly the standard three axioms. See `REPORT_482.md`.

API targets **18 fields**: `ε₀:726`, `eps_pos:728`, `eps_le_scaling:731`, `eps_le_cutoff:734`; `velocity:738`, `pressure:740`, `force:742`; `velocity_formula:749`, `pressure_formula:757`, `force_formula:764`; `force_mem:773`, `forceDifference_mem:777`; `velocity_smooth:784`, `pressure_smooth:789`, `initial:794`, `incompressible:798`, `momentum:806`, `history:812`. Dependencies: U1/U2, with U4 no-slip used only for the bundled solution below.

Set `u=v+w+scaledPacket`, `p=domainNormalizePressure Ω (π+scaledPressure)`, `f=g+correctionForce+scaledForce`, for **all** ε and spacetime points as the formulas require. Choose threshold below placement, cutoff, consumed I03 and the extra geometric bounds; do not use the simple T18 min unless all other bounds have already been built into those inputs. Use I03 `scaledEquation:223`, `scaledDivergenceFree:231` (`C1/Scaling.lean`) restricted to Ω. Sum derivatives locally; use U2 cross terms and spatial constancy of the pressure shift for the exact residual. Intersect open neighborhoods for smooth sums, and union compact positive time supports for force classes. Quiet history is global, including its closed endpoint, by I02 `correction_vanishes_before:369` and packet zero past.

Peel pressure normalization separately (M, codex-astra, within U3): finite positive volume of nonempty bounded open Ω; integrability of pressure slices; smooth dependence of the Ω-integral on time using local compact slabs in the open-neighborhood extension; zero integral after dividing by `(volume Ω).toReal`. The torus Haar calculation `S3/T18/Lifespan.lean:48` does not eliminate that volume factor. Target the exact neighborhood convention (`Spec:459`), not just smoothness within the closed set.

Own all **10** `ClassicalSolutionOmega` fields: `velocity:545`, `pressure:548`, `horizon_pos:551`, `velocity_smooth:555`, `pressure_smooth:557`, `initial:561`, `divergence:565`, `momentum:569`, `no_slip:574` (from U4), `pressure_gauge:578`. Package API `solution:840` after U4. No periodicity or torus Sobolev-path fields are imported. The target record differs from both whole-space and torus records; only a fieldwise domain constructor is valid.

### U4 — localized differences and boundary retention (M, codex-sol)

API targets **8 fields**: `collar_agreement:823`, `noSlip_preserved:831`, `velocityDifference_divFree:897`, `diffSupportRadius:903`, `diffSupportRadius_pos:906`, `velocityDifference_support:912`, `diffSupport_in_chart:919`, `forceDifference_spatialSupport:930`. Dependencies: U1/U2 and U3 formulas/divergence (not its solution packaging).

**Status (lane 483, 2026-09-19): complete conditionally.**
`Section3/T23/Differences.lean` proves all eight fields over the explicit U3
velocity/force formulas, smoothness and incompressibility hypotheses.  It uses
lane 477's actual `LocalCorrectionCore` support and correction-force support,
the raw I03 `carrier_subset` clause, and the raw packet force support.  The
chosen `ρ = max R_cutoff R_packet + 1` is strictly larger than both radii; the
positive common threshold is shrunk so `ball x₀ (ερ) ⊆ B` at its closed upper
endpoint.  Force support holds for every real time, and the literal zero
extension of each force-difference slice has `tsupport ⊆ closure B`.  Final U9
assembly must instantiate the threaded U3 hypotheses and select this shrunk
threshold; no parallel-lane module is imported.

Take ρ strictly larger than the cutoff and packet carrier radii, bound tsupport of the sum by the union, and shrink ε so `ball x₀ (ερ) ⊆ B`. Use I02 support fields cited in U2 and the scaled carrier from I03 `carrier_subset:190`; this is a single un-periodized ball. Force support also needs the force projection in Kstar, not merely P.carrier. Establish the all-real-time support assertion, especially after T, via I02 `force_support:433` plus scaled force support. With K=closure B, prove `tsupport (zeroExtension Ω (fε(t)-g(t))) ⊆ K` by closedness of K; the API only states pointwise nonvanishing support, so this conversion is a separate lemma. Outside B both perturbations vanish; frontier Ω misses B, giving no-slip from reference.no_slip. For a literally open boundary neighborhood use `(closure B)ᶜ`; the API's Bᶜ equality is stronger and suffices. Divergence of the difference follows locally in Ω.

### U5 — registered T22 domain/zero-extension comparison (M, codex-sol)

**Status (lane 484, 2026-09-19): complete.**
`Section3/T23/DomainComparison.lean:domain_zeroExt_comparison` applies the
canonical T22 three-field API to the actual force difference with the fixed
compact set `closure B`, chooses `C` before time and `ε`, and integrates both
extended-norm inequalities over `Ioi 0` without finiteness assumptions.  It
threads exactly U3's `forceDifference_mem` and U4's all-time pointwise support;
the order-zero slice identity and all five copied T23 norm-definition bridges
are checked separately.  The closure probe also gives explicit fieldwise
adapters from both the historical `Spec.lean` copy and the registered T22
contract copy to the canonical proof-side record.

API target `domain_zeroExt_comparison:983`; supporting targets domain norm definitions `Spec:615,622,629,640,648` and copied norm API `:289,304,324` transport. Dependencies: U3 force smoothness, U4 fixed support, registered T22. No new proof of cutoffMultiplier is requested.

Apply `C1/BoundedDomainNorm.lean:109` with the **difference** zε(t), Ω and fixed K=closure B. Choose C once for each s, before t and ε; integrate its two inequalities over Ioi 0. Use ENNReal lintegral monotonicity and constant multiplication, keeping possible infinite norms valid. The implementation route is `S3/T22/ZeroExtensionComparison.lean:28`. Apply `orderZero` (`C1/BoundedDomainNorm.lean:74`, `S3/T22/OrderZero.lean:219`) to the smooth difference slice for its physical restricted L² interpretation; handle gradient components for energy separately, since T22's field is vector-valued. Prove zero extension equals the globally supported force difference, not the reference or full force. This is no bounded zero-extension theorem for arbitrary H^s(Ω) data.

### U6 — closeness rates, path-norm bridge and convergence (L, codex-astra)

**Status (lane 485, 2026-09-19): complete with the authorized threaded U2b/U3/U4/U5 hypotheses.** `NormBridge.lean` and `Rates.lean` prove all eight field components; the probe consumes registered I03 scaling on the identical correction, and all 18 production declarations have exactly the standard three axioms. Both modules/probe, `make check`, `lake test`, and mutation gates pass. U9 must discharge the explicit matching, support, regularity, and comparison premises; no boundary API inhabitant or G0/G1 resolution is asserted. See `REPORT_485.md`.

API targets **8 fields**: `energyConst:938`, `energyConst_nonneg:940`, `energyRate:947`, `forceDiffSobolevConst:956`, `forceDiffSobolevConst_pos:961`, `forceDifference_sobolev_bound:969`, `forceDifference_negativeSobolev_tendsto:995`, `forceDifference_convergence:1003`. Dependencies: U2 matching scaling/correction, U3/U4, U5.

Energy: restriction of the L² measure decreases each velocity/gradient norm; pass through essSup, lintegral and the positive square root. Consume `C1/Scaling.lean:284` perturbationEnergyBound and preserve exactly `(P.energyBound+P.dissipationBound) ε^(1/2)+C ε^(3/2)`. `P1/LocalizationBoundary.lean:64,91` supplies real integral comparisons as a possible template; the actual target is ENNReal, so explicitly bridge or prove measure monotonicity directly.

Force: q=1 in `C1/Scaling.lean:319,335` gives packet and correction rates; ε≤1 and s≥0 absorb their order-zero terms, choose a strictly positive common C_s, then use U5's left comparison. **Peel the norm bridge first:** the supplier `C1/Data.lean:225` is an infimum over measurable datum paths, whereas `Spec:640,648` integrates per-slice norms. Prove `∫⁻ sobolevENorm s (f(t,·)) ≤ forceSobolevENorm 1 s f` by bounding against each admissible path and taking the infimum (empty-path case is top); equality is not definitional or required. Derive sum estimates on realized slices/paths with honest finite-norm witnesses.

For every s<0, prove the inhomogeneous weight contraction from order 0, giving `sobolevENorm s E₀z ≤ sobolevENorm 0 E₀z = ‖E₀z‖₂`; integrate and use the s=0 rate. I03 negative scaling only covers -3/2<s<0 (`:359,371`), so it cannot supply this all-negative tail. CutoffMultiplier alone is not the order monotonicity theorem. Finally squeeze along 𝓝[>]0 using eventual membership in (0,ε₀], positive exponents, and continuity of ofReal; keep definitions for ε outside that interval arbitrary but fixed by U3 formulas.

### U7 — domain no-slip velocity uniqueness (L, codex-astra)

**Lane 478 continuation status (2026-09-19): box U7 closed.**
`noSlip_uniqueness_box` proves the original velocity conclusion on `IsBoxDomain Ω`;
`ibp_box`, the domain difference-energy identity, convection estimate and Grönwall
are proved. `noSlip_uniqueness_of_ibp` proves the full conclusion under the explicit
scalar boundary identity `IBP Ω`. The sole smooth-branch analytic residual is
`IsOpen Ω → Bornology.IsBounded Ω → IsRegularLevelDomain Ω → IBP Ω`; see
`SPEC_ISSUES.md` G1 and `REPORT_478b.md`. Unrestricted `noSlip_uniqueness` remains
unclaimed; V1 box-only registration is a lead decision.

API target `noSlip_uniqueness:1015–1021`. Dependencies: canonical domain record and geometry; independent of packet/correction and T18 U12. Exact new theorem target (same local names as Spec):

```lean
∀ (ν : ℝ), 0 < ν → ∀ (Ω : Set Space), IsBoundedBoxOrSmoothDomain Ω →
  ∀ (a' : SpatialField), a' ∈ initialClassOmega Ω →
  ∀ (f : SpaceTimeField), f ∈ forceClassOmega Ω →
  ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionOmega ν Ω a' f T₁)
    (u₂ : ClassicalSolutionOmega ν Ω a' f T₂),
  ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x ∈ Ω,
    u₁.velocity (t, x) = u₂.velocity (t, x)
```

No verified domain uniqueness supplier was found; the searches are recorded in §2. T11 `velocity_unique` (`S3/T11/Uniqueness.lean:27`) is only a periodic analogue. Prove difference energy on [0,S] strictly inside both horizons: finite integrals and differentiability from compact slab smoothness; integration by parts for box and smooth-level domains; pressure and boundary terms vanish by no-slip and divergence; transport skew cancellation; bound the remaining term by a uniform spatial derivative bound of u₂ times ‖u₁-u₂‖₂². Grönwall from zero initial difference gives zero energy; continuity on open Ω upgrades a.e. equality to pointwise equality. Peel box/smooth integration-by-parts infrastructure before the energy argument; no boundary uniqueness axiom, pressure equality, H¹ restart assumption or free energy-identity premise is allowed.

### U8 — interior blow-up and lifespan exactly T (L, codex-astra)

**Lane 486: four fields kernel checked over the authorized U3/U4 family hypotheses.** `InteriorBlowup.lean` proves witnesses in the prescribed ball and Ω, pointwise blow-up and the local-continuity essential-supremum limsup. `Lifespan.lean` proves lifespan exactly T and maximality by compact closure bounds and U7; box specializations discharge IBP, while the smooth branch retains the explicit G1 `IBP Ω` premise. No new solution/placement/insertion record or U9 assembly is asserted. Probe and complete 15-declaration three-axiom audit pass; see `REPORT_486.md`.

API targets **4 fields**: `lifespan:847`, `maximal:857`, `blowup:863`, `blowup_limsup:868`. Dependencies: U2 cancellation, U3 solution, U4, U7. `solution:840` belongs to U3.

First strengthen the internal blow-up witness to include `x ∈ Ω` (indeed in the packet ball): I03 `scaledBlowup:239` and support/cancellation place every positive-level witness there; u equals the packet on its support. This implies the API's whole-space `SpeedUnboundedAt`, but the latter alone is insufficient for domain lifespan. For essential-supremum blow-up, continuity on a neighborhood of the witness inside Ω yields a positive-measure ball with large speed. `S4/R42/BlowupEssSup.lean:100` assumes global slice continuity, which the domain reference does not have outside Ω; adapt its `:63` local positive-measure argument, do not apply it blindly.

The exact lifespan theorem is, for each admissible ε, `domainMaximalLifespan ν Ω a (force ε) = ENNReal.ofReal place.T`. Lower bound follows directly from the full-horizon U3 solution and the supremum definition (`Spec:584`). For the upper bound, any solution on S>T agrees with the inserted velocity in Ω by U7 and is bounded on compact `[0,T] × closure Ω` by its smoothness. This contradicts the **interior** blow-up witness. The verified torus pattern is `S3/T18/Lifespan.lean:249,273,300`; replace the periodic cube reduction with closure Ω. No general domain existence/continuation theorem, H² embedding or H¹ restart is needed for this argument. For `maximal` (`Spec:601`), restrict the same total fields to any positive shorter horizon and retain their literal global field equalities, using lifespan=T. No uniqueness of pressure is needed.

### U9 — assembly, statement repair, contract/bindings/tests (M, codex-sol)

**Lane 487b: complete; `T04.boundary_insertion` registered (55 total).** G2 is closed by the weaker operational window core, proved at the literal U2b supplier cutoff; original U2/U4 theorem statements remain valid. The 48-field `boundaryInsertionAPI` is assembled, and the binding discharges every supplier clause. Box existence is unconditional; the smooth-domain branch has explicit `IBP Ω`. The full unit-box/nonzero-packet/zero-reference probe at T=1 and guarded audits pass. See `REPORT_487b.md` and `ATTEMPTS_U9.md`; G0/G1 V1 scope wording remains owner-pending.


Own the remaining **4** API fields `domain:701`, `delta_pos:705`, `reference_force_mem:710`, `initial_mem:714`, and the final `boundaryInsertionStatement:1037–1050`. Dependencies: U1–U8, T18 U12 integration convention, G0 and owner choices in §4. Field count: U1=1, U2=2, U3=19 including solution, U4=8, U5=1, U6=8, U7=1, U8=4, U9=4: **48**. The separate 16 placement and 10 solution fields are all assigned above; the 7 cutoff data and 3 T22 fields are also accounted for.

Assemble only after each exact field theorem is closed. Preserve the current Spec field inventory in compatibility documentation, but **do not claim its universal arbitrary-D statement proved**. Owner-approved corrected quantification must actually select a compatible cutoff and matching internal whole-space records. Register domain vocabulary separately or with T23 according to owner decision; consume registered T22 instead of copying its definitions again. Bind raw packet fields and all copied definitions by rfl bridges where valid; build domain/contract record conversions and round trips explicitly. Final tests: literal field types and quantifier order, translated interior ball, positive common threshold, chosen-family identity, normalized pressure and no-slip, all-t force support, uniform comparison constant, interior blow-up, lifespan equality, negative orders below -3/2, plus transitive axiom checks restricted to propext/Classical.choice/Quot.sound. Run repository contract/import and mutation gates when Lean is implemented. U9 is bookkeeping only after these gates; unproved analysis is sent back to its owning L unit.

## 2. Dependency ledger and negative-search evidence

| Consumer | Supplier / exact route | Residual and owner |
|---|---|---|
| U1 placement | `B/CorrectionV2.lean:537` compact carrier enlargement | Free-center geometry and strict threshold: U1 |
| U2 correction | `C1/Correction.lean:542`, `C2/Correction.lean:155`; actual constructor `B/CorrectionV2.lean:87` | Domain-to-local/whole-space bridge, matching D: U2; G0 repair: owner |
| U3 packet equation | `C1/Scaling.lean:480` retains given C; fields `:223,231` | Local restriction and normalized pressure: U3 |
| U4 support | `C1/Correction.lean:359,433,444`, `C2/Correction.lean:136` | Kstar force projection and all-time support; no V1 carrier-only shortcut |
| U5 comparison | `C1/BoundedDomainNorm.lean:74,109`; `B/BoundedDomainNorm.lean:81` | Fixed K then C before ε,t; integration: U5 |
| U6 rates | `C1/Scaling.lean:284,319,335`; `C1/Data.lean:225` | Measurable-path to slice-integral inequality; all-negative-order contraction |
| U7 uniqueness | `S3/T11/Uniqueness.lean:27` is periodic only | New Ω integration-by-parts / difference-energy theorem |
| U8 lifespan | `S3/T18/Lifespan.lean:273,300,338` is a template | U7 plus interior blow-up and compact closure Ω |
| U9 registration | T18 canonical raw bundle `S3/T18/Insertion.lean:37`; T22 conversion `B/BoundedDomainNorm.lean:54–67` | T18 U12, G0, domain record registration and owner policy |

Dependency order is U1 → U2 → U3 formulas/regularity → U4 → U3 solution; U3/U4 → U5 → U6; U7 can run independently on domain vocabulary; U3 solution/U4/U7 → U8; all → U9. The apparent U3/U4 cycle disappears by packaging solution last. U6 is not needed for uniqueness or lifespan except force-class membership, already owned by U3.

Searches actually run (paths relative to repository root):

```sh
grep -rnEi 'no.?slip|domain.*unique|unique.*domain|boundary.*unique|unique.*boundary' formalization/NSFormalization/Section4 formalization/NSFormalization/Paper1 vendor --include='*.lean'
grep -rnE '^(theorem|lemma|def).*([Nn]o[Ss]lip.*[Uu]niqu|[Uu]niqu.*[Nn]o[Ss]lip|[Dd]omain[Vv]elocity[Uu]nique|[Dd]omainMaximalLifespan)' formalization/NSFormalization/Section4 formalization/NSFormalization/Paper1 vendor --include='*.lean'
grep -rnE 'ClassicalSolutionOmega|BoundaryInsertionAPI' verification/Contracts formalization/NSFormalization --include='*.lean'
```

The first broad search found boundary-support bookkeeping (`P1/BoundaryReferenceRestriction.lean:40,76,126`), the conditional corrected corollary (`P1/BoundaryCorollaryCorrected.lean:28,45`), periodic lifespan (`vendor/NavierStokesAndEuler/NavierStokes/MaximalLifespan.lean:86,89`) and unrelated UniqueDiffOn/boundary-coordinate/Euler hits. None supplies classical Navier–Stokes no-slip uniqueness on this Ω structure. The second and third searches returned **no output** (grep exit 1). This is a scoped search result, not a claim that no differently named lemma could exist. No bounded-domain uniqueness or canonical/registered T23 record was located in the searched tree. U7 is therefore budgeted L, not marked reusable. No claim is made that in-flight branches have landed.

Registration and declarations were independently checked with `grep -nE 'I02|I03|bounded_domain_norm' verification/contracts.json`, `grep -rnE '^(theorem|lemma|def|structure|noncomputable def)'` on the cited supplier directories, and `sed -n` on the cited declarations. The older reconciliation's “T22 unregistered” and “LocalizationBoundary:189 zero-extension core” descriptions are superseded by the checked sources above.

## 3. Waves and start conditions

| Wave | Startable work | Exit condition |
|---|---|---|
| 0 — now | U1 geometry; U2 supplier/local-extension audit; U7 domain record and integration-by-parts development; U5 generic fixed-K integration and U6 path-norm bridge | Named lemmas with exact hypotheses; G0 counterexample delivered to owner |
| 1 — after local supplier | U2 cancellation and cutoff estimates; U3 formulas, local smoothness, force classes, gauge and residual; U4 support/collar | One compatible family and positive common threshold; all-time force support |
| 2 — after family facts | U3 solution packaging, U5 instantiated comparison, U6 rates/convergence; U8 after U7 | Every mathematical field closed, including interior blow-up and lifespan=T |
| 3 — gated assembly | U9 contract, bindings, field/type probes and mutation tests | T18 U12 canonical integration reviewed, all owner decisions resolved, no G0 false quantifier remains |

T18 U12 is an integration/registration gate requested for this lane, not a mathematical prerequisite for constructing an un-periodized domain packet. Its in-flight U7/U9–U11 may furnish patterns, but no planned Ω theorem depends on an unverified upstream proof. Independent analytic work should not wait for them. Conversely, T18 U12 cannot resolve the missing domain uniqueness or arbitrary-D quantifier by itself. Conditional local theorem development can start while G0 is pending; the final unconditional statement and registry entry cannot.

## 4. Risks and owner decisions blocking registration

1. **Arbitrary D makes the current statement unsatisfiable for admissible data with D.ε₀=0.** This is stronger than a missing proof. The reconciliation §3 says to identify the cutoff with the consumed correction, but Spec:1037 quantifies it independently. Owner must approve changed quantification/compatibility before U9; U2 constructs the concrete compatible choice. Raw r is also unconstrained by the statement, so it cannot be silently treated as a positive construction radius. Use a positive inner radius derived in U1 and explicitly pin any retained r.
2. **“Any interior ball” must remain literal.** Reconciliation's rejected A forces the origin into Ω; rejected B confines placement to the unit cube. Neither is repaired by picking a convenient domain. Keep free x₀, prescribed B with closure B⊆Ω, and prove a nonvacuous translated example. Cube-free placement is already the approved reconciliation direction (§0/§3), not a reason to reopen it; any registration reformulation must retain it.
3. **Owner's domain data policy remains open.** T22 registration is resolved (`verification/contracts.json:478`); registration of `ClassicalSolutionOmega` and the canonical domain data location remains a decision. No conversion from `ClassicalSolutionT` or `ClassicalSolutionR` to a no-slip solution is automatic. Contract/local copies of the domain record need fieldwise conversions and round trips; definition-level rfl bridges do not identify different structures. No new contract import whitelist is silently assumed.
4. **Whole-space correction is conditional.** I02/I03 consumption is the binding direction, but global hypotheses are not inherited from Ω. U2 must prove a local extension/transport result or the appropriate local analytic lemmas. This cannot be postponed into U9 or replaced with the fact that a correction exists for some other background. Preserve I03's same-C equality, packet identity, time, center, correction family, and force formula through every conversion.
5. **Domain-shape and gauge choices need owner disposition.** Reconciliation §3 adopts the regular-level smooth-domain encoding plus boxes/nonempty and normalized pressure; §4 questions 3 and 5 leave policy approval open. Verify these choices when registering. Velocity-only uniqueness is sufficient; do not strengthen it to pressure equality, especially without connectedness. Normalization must prove smooth time dependence and finite positive volume. The current reference horizon is Ico(T+δ), not the paper's closed endpoint; δ>0 leaves a neighborhood of T for the construction, but the registration fidelity note must preserve this distinction.
6. **No-slip uniqueness is new analysis.** Search evidence is §2; periodic and whole-space uniqueness do not apply to domain records. Box corners and smooth-level domains require actual boundary integration-by-parts arguments. The explicit-solution supremum proof avoids demanding an entire domain local-existence/continuation API; it still needs U7 and an interior blow-up witness.
7. **Norm and support traps.** Do not substitute joint path infima for T23's per-slice norm, pretend their equality is rfl, or use negative I03 rates below their -3/2 endpoint. Keep the fixed compact K valid after T and C chosen before ε. Support of the difference, not full gε, permits zero extension. Compact support must control derivative supports used in force and gradient energy estimates.
8. **Total fields outside Ω are unconstrained.** The Spec's formulas/history/cross terms are global, while reference smoothness and uniqueness are local. Locality plus perturbation support must prove the global algebraic assertions. Global `SpeedUnboundedAt` alone is inadequate for lifespan; prove interior witnesses. Global continuity required by the existing essSup lemma is not available: use a positive-measure neighborhood inside Ω.
9. **Unsafe candidate imports and stale supplier descriptions.** Both proposed boundary helper modules import the sorry-bearing `BoundaryCorollary.lean`; their useful elementary geometry should be implemented cleanly. The corrected conditional contract is not an inhabitant. T22's registered theorem, not periodic interpolation in LocalizationBoundary, supplies zero-extension comparison.

Registration stop conditions are concrete: G0 statement repair; proved local correction matching; closed U7/U8 and all other field lemmas; owner disposition of domain record placement, smooth-domain encoding and gauge/scope; and T18 U12 integration review. None is replaced by placeholder fields. This lane leaves existing specifications and modules unchanged so these decisions remain reviewable.
