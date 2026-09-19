# T23 proof split — interior no-slip insertion (`cor:boundary`)

Planning lane 449. Incremental draft: supplier evidence and exact field ownership are refined in subsequent commits. No proof or registration is asserted by this document.

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

### U1 — cube-free placement and interior geometry (M, codex-sol)

Target all **16** `DomainPlacementData` fields: `T:378`, `time_pos:382`, `chartCenter:386`, `chartRadius:390`, `chartRadius_pos:394`, `x₀:398`, `x₀_mem:402`, `Kstar:407`, `Kstar_compact:412`, `carrier_subset:417`, `force_projection_subset:423`, `ε₀:429`, `eps_pos:433`, `eps_le_one:437`, `eps_time:443`, `eps_space:449`; API `interiorBall_in_domain:720`. Dependencies: packet compact support, prescribed positive T and prescribed closed ball inside Ω; no T18 assembly dependency.

Construct Kstar as the union of packet carrier and the spatial image of compact force support (verified route `B/CorrectionV2.lean:537`, `isCompact_carrierStar`). Choose a finite radius R bounding Kstar and positive margin `chartRadius - dist x₀ chartCenter`. Choose one positive threshold below 1, a strict time bound, and margin/(R+1), with a factor 1/2 to retain strict inequalities at the closed upper endpoint. Prove affine-image containment. This works for any given interior ball and any x₀ in it, including Ω=(1,2)³; no origin or cube condition. Also prove closed-ball compactness, separation from frontier Ω, and existence of a smaller ball around x₀. The geometry proof at `P1/BoundaryCorollaryCorrected.lean:19` is a template only (unsafe import noted above). A concrete translated-ball placement probe must satisfy eps_time, not just list the fields.

### U2 — local correction supplier and compatibility (L, codex-astra)

Targets the seven cutoff data fields `Spec:135–170` and their construction identities; API `crossTransport_background_advects_packet:879`, `crossTransport_packet_advects_background:888`. Dependencies: U1; statement repair G0 for end-to-end assembly. Produce one positive cutoff threshold and one D with its actual smoothness, curl/divergence, cancellation, support and force estimates, tied to the given reference and x₀. These are named proved lemmas, not placeholder fields.

I02 gives `correction_support:359`, `correction_support_ball:364`, `correction_cancels_germ:385`, `force_support:433`, `force_support_ball:444`, `force_formula:415` in `C1/Correction.lean`. But `reference_divergence_free:230` is global. Preferred bridge to investigate: take the radial potential in a slightly larger interior ball, multiply it by a fixed compact cutoff equal to one near the construction ball, and take curl to obtain a globally smooth solenoidal reference extension agreeing there. Extend pressure smoothly with a cutoff and define its exterior force by the residual; it agrees with g where needed. Prove agreement of potential/correction/force jets on their supports, including the time window through T, before consuming I02/I03. `B/CorrectionV2.lean:87–100` still requires the global hypotheses; it does not supply this bridge. Its prescribed-K version (`C2/Correction.lean:136,155`) can cover Kstar, or separately shrink the packet-force range using U1. If extension transport is longer, peel the local versions of the I02 analytic lemmas; do not claim the registered record itself has weaker hypotheses.

Cancellation gives both cross terms by the open-neighborhood argument of `S3/T18/CrossTransport.lean:46`; use the un-periodized packet. I02 cancellation is on Ioo, while targets use Ico: handle t=0 by the packet's inactive past and derivative of the zero slice. Prove global cross identities despite reference smoothness only near Ω: away from packet/correction support the relevant fields are locally zero, so no exterior regularity assumption is needed.

### U3 — triple, kinematics, momentum and solution record (L, codex-astra)

API targets **18 fields**: `ε₀:726`, `eps_pos:728`, `eps_le_scaling:731`, `eps_le_cutoff:734`; `velocity:738`, `pressure:740`, `force:742`; formulas `:749,757,764`; `force_mem:773`, `forceDifference_mem:777`; `velocity_smooth:784`, `pressure_smooth:789`, `initial:794`, `incompressible:798`, `momentum:806`, `history:812`. Dependencies: U1/U2, with U4 no-slip used only for the bundled solution below.

Set `u=v+w+scaledPacket`, `p=domainNormalizePressure Ω (π+scaledPressure)`, `f=g+correctionForce+scaledForce`, for **all** ε and spacetime points as the formulas require. Choose threshold below placement, cutoff, consumed I03 and the extra geometric bounds; do not use the simple T18 min unless all other bounds have already been built into those inputs. Use I03 `scaledEquation:223`, `scaledDivergenceFree:231` (`C1/Scaling.lean`) restricted to Ω. Sum derivatives locally; use U2 cross terms and spatial constancy of the pressure shift for the exact residual. Intersect open neighborhoods for smooth sums, and union compact positive time supports for force classes. Quiet history is global, including its closed endpoint, by I02 `correction_vanishes_before:369` and packet zero past.

Peel pressure normalization separately (M, codex-astra, within U3): finite positive volume of nonempty bounded open Ω; integrability of pressure slices; smooth dependence of the Ω-integral on time using local compact slabs in the open-neighborhood extension; zero integral after dividing by `(volume Ω).toReal`. The torus Haar calculation `S3/T18/Lifespan.lean:48` does not eliminate that volume factor. Target the exact neighborhood convention (`Spec:459`), not just smoothness within the closed set.

Own all **10** `ClassicalSolutionOmega` fields: `velocity:545`, `pressure:548`, `horizon_pos:551`, `velocity_smooth:555`, `pressure_smooth:557`, `initial:561`, `divergence:565`, `momentum:569`, `no_slip:574` (from U4), `pressure_gauge:578`. Package API `solution:840` after U4. No periodicity or torus Sobolev-path fields are imported. The target record differs from both whole-space and torus records; only a fieldwise domain constructor is valid.

### U4 — localized differences and boundary retention (M, codex-sol)

API targets **8 fields**: `collar_agreement:823`, `noSlip_preserved:831`, `velocityDifference_divFree:897`, `diffSupportRadius:903`, `diffSupportRadius_pos:906`, `velocityDifference_support:912`, `diffSupport_in_chart:919`, `forceDifference_spatialSupport:930`. Dependencies: U1/U2 and U3 formulas/divergence (not its solution packaging).

Take ρ strictly larger than the cutoff and packet carrier radii, bound tsupport of the sum by the union, and shrink ε so `ball x₀ (ερ) ⊆ B`. Use I02 support fields cited in U2 and the scaled carrier from I03 `carrier_subset:190`; this is a single un-periodized ball. Force support also needs the force projection in Kstar, not merely P.carrier. Establish the all-real-time support assertion, especially after T, via I02 `force_support:433` plus scaled force support. With K=closure B, prove `tsupport (zeroExtension Ω (fε(t)-g(t))) ⊆ K` by closedness of K; the API only states pointwise nonvanishing support, so this conversion is a separate lemma. Outside B both perturbations vanish; frontier Ω misses B, giving no-slip from reference.no_slip. For a literally open boundary neighborhood use `(closure B)ᶜ`; the API's Bᶜ equality is stronger and suffices. Divergence of the difference follows locally in Ω.

### U5 — registered T22 domain/zero-extension comparison (M, codex-sol)

API target `domain_zeroExt_comparison:983`; supporting targets domain norm definitions `Spec:615,622,629,640,648` and copied norm API `:289,304,324` transport. Dependencies: U3 force smoothness, U4 fixed support, registered T22. No new proof of cutoffMultiplier is requested.

Apply `C1/BoundedDomainNorm.lean:109` with the **difference** zε(t), Ω and fixed K=closure B. Choose C once for each s, before t and ε; integrate its two inequalities over Ioi 0. Use ENNReal lintegral monotonicity and constant multiplication, keeping possible infinite norms valid. The implementation route is `S3/T22/ZeroExtensionComparison.lean:28`. Apply `orderZero` (`C1/BoundedDomainNorm.lean:74`, `S3/T22/OrderZero.lean:219`) to the smooth difference slice for its physical restricted L² interpretation; handle gradient components for energy separately, since T22's field is vector-valued. Prove zero extension equals the globally supported force difference, not the reference or full force. This is no bounded zero-extension theorem for arbitrary H^s(Ω) data.

### U6 — closeness rates, path-norm bridge and convergence (L, codex-astra)

API targets **8 fields**: `energyConst:938`, `energyConst_nonneg:940`, `energyRate:947`, `forceDiffSobolevConst:956`, `forceDiffSobolevConst_pos:961`, `forceDifference_sobolev_bound:969`, `forceDifference_negativeSobolev_tendsto:995`, `forceDifference_convergence:1003`. Dependencies: U2 matching scaling/correction, U3/U4, U5.

Energy: restriction of the L² measure decreases each velocity/gradient norm; pass through essSup, lintegral and the positive square root. Consume `C1/Scaling.lean:284` perturbationEnergyBound and preserve exactly `(P.energyBound+P.dissipationBound) ε^(1/2)+C ε^(3/2)`. `P1/LocalizationBoundary.lean:64,91` supplies real integral comparisons as a possible template; the actual target is ENNReal, so explicitly bridge or prove measure monotonicity directly.

Force: q=1 in `C1/Scaling.lean:319,335` gives packet and correction rates; ε≤1 and s≥0 absorb their order-zero terms, choose a strictly positive common C_s, then use U5's left comparison. **Peel the norm bridge first:** the supplier `C1/Data.lean:225` is an infimum over measurable datum paths, whereas `Spec:640,648` integrates per-slice norms. Prove `∫⁻ sobolevENorm s (f(t,·)) ≤ forceSobolevENorm 1 s f` by bounding against each admissible path and taking the infimum (empty-path case is top); equality is not definitional or required. Derive sum estimates on realized slices/paths with honest finite-norm witnesses.

For every s<0, prove the inhomogeneous weight contraction from order 0, giving `sobolevENorm s E₀z ≤ sobolevENorm 0 E₀z = ‖E₀z‖₂`; integrate and use the s=0 rate. I03 negative scaling only covers -3/2<s<0 (`:359,371`), so it cannot supply this all-negative tail. CutoffMultiplier alone is not the order monotonicity theorem. Finally squeeze along 𝓝[>]0 using eventual membership in (0,ε₀], positive exponents, and continuity of ofReal; keep definitions for ε outside that interval arbitrary but fixed by U3 formulas.

### U7 — domain no-slip velocity uniqueness (L, codex-astra)

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

API targets **4 fields**: `lifespan:847`, `maximal:857`, `blowup:863`, `blowup_limsup:868`. Dependencies: U2 cancellation, U3 solution, U4, U7. `solution:840` belongs to U3.

First strengthen the internal blow-up witness to include `x ∈ Ω` (indeed in the packet ball): I03 `scaledBlowup:239` and support/cancellation place every positive-level witness there; u equals the packet on its support. This implies the API's whole-space `SpeedUnboundedAt`, but the latter alone is insufficient for domain lifespan. For essential-supremum blow-up, continuity on a neighborhood of the witness inside Ω yields a positive-measure ball with large speed. `S4/R42/BlowupEssSup.lean:100` assumes global slice continuity, which the domain reference does not have outside Ω; adapt its `:63` local positive-measure argument, do not apply it blindly.

The exact lifespan theorem is, for each admissible ε, `domainMaximalLifespan ν Ω a (force ε) = ENNReal.ofReal place.T`. Lower bound follows directly from the full-horizon U3 solution and the supremum definition (`Spec:584`). For the upper bound, any solution on S>T agrees with the inserted velocity in Ω by U7 and is bounded on compact `[0,T] × closure Ω` by its smoothness. This contradicts the **interior** blow-up witness. The verified torus pattern is `S3/T18/Lifespan.lean:249,273,300`; replace the periodic cube reduction with closure Ω. No general domain existence/continuation theorem, H² embedding or H¹ restart is needed for this argument. For `maximal` (`Spec:601`), restrict the same total fields to any positive shorter horizon and retain their literal global field equalities, using lifespan=T. No uniqueness of pressure is needed.

### U9 — assembly, statement repair, contract/bindings/tests (M, codex-sol)

Own the remaining **4** API fields `domain:701`, `delta_pos:705`, `reference_force_mem:710`, `initial_mem:714`, and the final `boundaryInsertionStatement:1037–1050`. Dependencies: U1–U8, T18 U12 integration convention, G0 and owner choices in §4. Field count: U1=1, U2=2, U3=19 including solution, U4=8, U5=1, U6=8, U7=1, U8=4, U9=4: **48**. The separate 16 placement and 10 solution fields are all assigned above; the 7 cutoff data and 3 T22 fields are also accounted for.

Assemble only after each exact field theorem is closed. Preserve the current Spec field inventory in compatibility documentation, but **do not claim its universal arbitrary-D statement proved**. Owner-approved corrected quantification must actually select a compatible cutoff and matching internal whole-space records. Register domain vocabulary separately or with T23 according to owner decision; consume registered T22 instead of copying its definitions again. Bind raw packet fields and all copied definitions by rfl bridges where valid; build domain/contract record conversions and round trips explicitly. Final tests: literal field types and quantifier order, translated interior ball, positive common threshold, chosen-family identity, normalized pressure and no-slip, all-t force support, uniform comparison constant, interior blow-up, lifespan equality, negative orders below -3/2, plus transitive axiom checks restricted to propext/Classical.choice/Quot.sound. Run repository contract/import and mutation gates when Lean is implemented. U9 is bookkeeping only after these gates; unproved analysis is sent back to its owning L unit.

## 2. Dependency ledger

U1/U2 → U3/U4 → U5/U6; U3/U4/U7 → U8; all units → U9. Registered suppliers must be instantiated with matching data; registration alone is not a compatibility proof.

## 3. Waves

Start geometry and supplier audits now. Domain analytic units can proceed independently of torus assembly. Final canonical reuse and registration wait for T18 U12 and unresolved owner decisions.

## 4. Risks

Reject origin-centered support for arbitrary domains and torus placement outside the unit cube. Audit arbitrary cutoff parameters, pressure normalization, domain uniqueness, and whole-space/domain solution conversions before claiming assembly is routine.
