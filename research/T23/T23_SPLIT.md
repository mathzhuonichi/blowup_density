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

## 1. Units (initial targets)

| Unit | Target | Size / model |
|---|---|---|
| U1 | Cube-free `DomainPlacementData`: all 16 fields, interior ball and small-scale geometry | M / codex-sol |
| U2 | Whole-space correction compatibility and `CutoffData` identification for a domain reference | L / codex-astra |
| U3 | Un-periodized inserted triple, pressure normalization, all 10 `ClassicalSolutionOmega` fields | L / codex-astra |
| U4 | Support localization, fixed compact force support, collar agreement and no-slip retention | M / codex-sol |
| U5 | T22 comparison on the force difference and domain order-zero transport | M / codex-sol |
| U6 | Domain energy/force closeness rates and negative-order tail | L / codex-astra |
| U7 | Domain velocity uniqueness by difference energy, with exact hypotheses | L / codex-astra |
| U8 | Interior blow-up, lifespan exactly T and maximal record | L / codex-astra |
| U9 | Complete 48-field API, quantified statement, contracts/bindings/tests; gate on T18 U12 and owner decisions | M / codex-sol |

Exact field partition and checked source routes follow in the next revision.

## 2. Dependency ledger

U1/U2 → U3/U4 → U5/U6; U3/U4/U7 → U8; all units → U9. Registered suppliers must be instantiated with matching data; registration alone is not a compatibility proof.

## 3. Waves

Start geometry and supplier audits now. Domain analytic units can proceed independently of torus assembly. Final canonical reuse and registration wait for T18 U12 and unresolved owner decisions.

## 4. Risks

Reject origin-centered support for arbitrary domains and torus placement outside the unit cube. Audit arbitrary cutoff parameters, pressure normalization, domain uniqueness, and whole-space/domain solution conversions before claiming assembly is routine.
