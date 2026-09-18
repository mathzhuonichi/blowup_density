# T16 `lem:potential` — reconciled comparison

This comparison merges blind Draft A (lane 271) and blind Draft B (lane 272)
under the binding rulings in the lead's
`research/T16/RECONCILIATION.md`.  The current paper file places the lemma
and proof at `paper/sections/03-torus.tex:176-216`; the lane brief's
`:21-60` range is an older excerpt offset.

`Spec.lean` uses B's `CutoffData`, B's `LocalPotentialAPI` field names and
order, B's packet name `U`, and B's main quantifier order.  It uses A's more
precise citations and explanatory support distinctions.  Every data/API field
has an explicit non-vacuity paragraph.

## T10 vocabulary and standalone import strategy

Research files are checked as standalone Lean files and cannot be imported as
modules.  The spec therefore starts with the same imports as T10
(`Contracts.V1.Data` and
`Mathlib.Analysis.Fourier.AddCircleMulti`), adds the registered
`Contracts.V1.Correction` definitions needed by T16, and copies only the
following declarations in their original `BlowupDensity.T10.Draft`
namespace:

- `PeriodicFrequency`, verbatim from `research/T10/Spec.lean:46-48`;
- `IsPeriodicOn`, verbatim from `research/T10/Spec.lean:66-70`.

The required provenance banner appears immediately before those copies.
`SpaceTimeField` is referenced directly from the same registered
`Contracts.V1.Data` vocabulary used by T10.  T16 has no Sobolev, homogeneous,
mean, Fourier, or norm clause, so copying any other T10 definition would add
unused specification surface.  Once `T01.torus_data` is registered, the two
copies should be replaced by an import.

## Paper clause → Lean field, provenance, and ruling

| Paper clause | Reconciled Lean spelling | Draft A | Draft B | Ruling |
|---|---|---|---|---|
| Witnesses are fixed before “sufficiently small `ε`” (`03-torus.tex:167-188,212`) | `CutoffData` with `θ, η, plateau, θRadius, ε₀, potential, correction` | All witnesses were parameters to a Prop structure and existentially bound outside it | Type-valued `CutoffData` projected by a Prop-valued API | Keep B's data record and its field order, so downstream statements can project the actual witnesses. |
| Reference and packet field vocabulary | `v U : SpaceTimeField`; `IsPeriodicOn univ v` | Own `VelocityField` and upstream `UnitSpatialPeriodsOn`; packet named `localizedVelocity` | Own `VelocityField` and provisional `IsPeriodic`; packet named `U` | Use T10's `SpaceTimeField`/`IsPeriodicOn`, and B's packet name `U`. |
| Coordinate ball and compact `K_*` (`:101-105,164-177`) | Main premises `0 < r`, `r < 1/2`, `IsCompact K`, local smoothness and local zero divergence | Arbitrary fundamental-cube origin and closed-ball inclusion | Injective unit-torus chart encoded by `r < 1/2` | Keep B's quantifiers and premises. |
| Source packet support (`:101-120,214`) | `∀ t ∈ Ioo 0 1, tsupport (fun x => U (t,x)) ⊆ K` and `periodicScaledPacket` | Assumed support of an already localized family at every scale | Assumed compact source-time support, then used registered `scaledPacket` and periodization | Keep B; T14 later supplies this premise for the paper's packet. |
| Smooth compact spatial Urysohn cutoff (`:167-174,181`) | `theta_smooth`, `theta_compactSupport` | Same two names | Same two names | Shared field names; use A's detailed citations. |
| Spatial cutoff takes values in `[0,1]` (`:171-172`) | `theta_range` | Split into `theta_nonneg` and `theta_le_one` | One `Icc 0 1` membership | Keep B's single range field. |
| `θ=1` on an open neighborhood of `K_*` (`:168-172,181`) | `plateau_open`, `prescribed_subset_plateau`, `theta_one` | Same mathematical clauses | Same field names, aligned with I02 V2 | Keep B's fields and order; cite A's full Urysohn paragraph. |
| Fixed compact support radius (`:168-172,181,212`) | `theta_radius_pos`, `theta_support` | Same two names | Same two names | Shared; strict positivity prevents a degenerate size witness. |
| Smooth compact temporal cutoff (`:173-174,182`) | `eta_smooth`, `eta_compactSupport` | Same two names | Same two names | Shared; cite A's direct-construction paragraph. |
| Temporal range `[0,1]` (`:171-174`) | `eta_range` | Split into `eta_nonneg` and `eta_le_one` | One `Icc 0 1` membership | Keep B's single range field. |
| `η=1` on `[-1,1]`, supported in `(-2,2)` (`:182,188-189,214-215`) | `eta_one`, `eta_support` | Same names | Same names | Shared fields, with A's proof-line citations. |
| “For sufficiently small `ε`” (`:188,212`) | `eps_pos` and all scale-dependent fields quantify `ε ∈ Ioc 0 D.ε₀` | Same interval convention | Same interval convention | Shared; one threshold controls every conclusion. |
| `2ε² < min(T,δ)` and spatial containment (`:103-105,212`) | `eps_time`, `eps_space` | Same field names | Same field names | Shared, with `D.θRadius` used in the spatial inequality. |
| Local smooth radial potential (`:177-181`) | `potential_smooth` on `(0,T+δ) × ball x₀ r` | Same local domain | Same local domain | Shared. |
| Display `eq:potential` (`:178-180`) | `potential_formula` | Restricted formula to the local slab and ball | Formula quantified for all `t,x` | Keep B's field shape and name, as required by reconciliation; the curl conclusion remains local. |
| `curl A=v` (`:181,196-210`) | `potential_curl` on the local slab and ball | Same conclusion | Same conclusion | Shared, using A's exact proof citation. |
| Display `eq:cutoff` (`:183-188`) | `correction_formula` using registered `scaledTemporalCutoff`, `scaledSpatialCutoff`, and `curl` | Formula on the chart, with global extension in later fields | Same chart formula | Keep B's binders and field name; Euclidean operators are reused from the registered I02 contract. |
| Global smoothness of the zero-extended periodic field (`:188,212`) | `correction_smooth` | Same field name | Same field name | Shared. |
| Unit spatial periodicity (`:188,212`) | `correction_periodic : IsPeriodicOn univ ...` | Upstream `UnitSpatialPeriodsOn` | Provisional lattice predicate `IsPeriodic` | Replace both draft-local spellings by T10's `IsPeriodicOn`. |
| Divergence-free correction (`:188,212`) | `correction_divergence_free` | Same field name | Same field name | Shared; use the registered physical divergence. |
| Temporal support in `(T-2ε²,T+2ε²)` (`:188-189,212`) | `correction_support` | Combined time and periodic spatial support in one field | Temporal support field, spatial support separated | Keep B's split and field order. |
| Spatial support in the coordinate ball on the torus (`:188,212`) | `correction_support_ball` with `periodicSet (Metric.ball x₀ r)` | Stronger combined inclusion using the scaled cutoff radius | Fixed coordinate-ball periodic lift | Keep B's named field.  The stronger scaled-radius inclusion remains a possible proof theorem. |
| `eq:bgzero` on the active interval (`:190-193,214-215`) | `correction_cancels` on `Ico (T-ε²) T` | Open neighborhood of the support of the already-scaled packet | Open neighborhood of `periodicScaledPacket U x₀ T ε` | Keep B's packet object and field name, with A's exact citations and open-neighborhood explanation. |
| Exact theorem packaging | `localPotentialStatement` | `localDivergenceFreeCutoffStatement` with seven existential witnesses | `localPotentialStatement` with `∃ D : CutoffData` | Keep B.  The theorem asserts no T17 derivative, energy, or force bound. |

There is no universal numerical constant in T16.  The only real size data are
`θRadius` and `ε₀`, and both have strict positivity fields.  A nonzero
periodic physical lift cannot have compact support in all of `R³`, so the
specification deliberately separates compact support of the unscaled cutoffs
from periodic support of the global correction.

## Proof dependencies

The reconciliation's §4 sends this specification next to a medium proof lane
and directs it to reuse the Section 4 I02 construction, in particular
`NSFormalization.Paper1.CorrectionProfile.physicalCorrection` and the
`CorrectionVectorNorms` layer.  The exact proof obligations are:

1. **Local radial potential.**  Reuse
   `RadialPotential.centeredPotential_eq_integral`,
   `centeredPotential_contDiff`, and `curl_centeredPotential`.  A local
   extension/localization lemma is still needed because T16 assumes
   `ContDiffOn` and zero divergence only on the coordinate ball, whereas the
   existing theorems take a globally smooth slice.
2. **Cutoff construction with range.**  Refine
   `Paper1.exists_spatial_cutoff` and
   `Paper1.exists_temporal_cutoff` to export the pointwise `Icc 0 1`
   range, choose a radius containing the compact `K`, and retain the open
   plateau.  The existing bump construction supplies the smoothness, compact
   support, plateau, and support inclusions.
3. **One small-scale threshold.**  From `T>0`, `δ>0`, `r>0`, and
   `D.θRadius>0`, choose `D.ε₀>0` so that both strict inequalities
   `2*ε^2 < min T δ` and `ε*D.θRadius < r` hold for every
   `ε ∈ Ioc 0 D.ε₀`.
4. **Euclidean correction.**  Reuse
   `CorrectionProfile.physicalCorrection`,
   `physicalCorrection_rescale`, `physicalCorrection_eq_profile`,
   `CorrectionForceNorms.physicalCorrection_smooth` (provided by the
   `CorrectionVectorNorms` module), and the local
   `localCorrection_divergence`/support lemmas to establish the chart
   formula, smoothness, divergence, and time/spatial support before
   periodization.  T17, not T16, consumes the derivative/norm estimates.
5. **Smooth periodic gluing.**  Prove that the compact chart correction,
   whose support stays strictly inside the ball, extends by zero across the
   chart boundary and its integer translates form a locally finite smooth
   `SpaceTimeField`.  Derive `correction_periodic`,
   `correction_support`, and `correction_support_ball`.
6. **Packet support bridge.**  From the source support premise for `U` and
   the registered `scaledPacket`/zero-past definition, prove the support
   inclusion for `periodicScaledPacket U x₀ T ε`.  This bridge belongs with
   T14's packet registration, even though T16 consumes it for cancellation.
7. **Plateau cancellation.**  On `Ico (T-ε²) T`, use `eta_one`; on the
   scaled open plateau use `theta_one` and local constancy, then combine
   `potential_curl` with the chart formula to show
   `D.correction ε=-v` on an open neighborhood of the packet support.

### Exact T10 lemmas needed

T16 stays entirely in T10's physical representation and does not mention
`PeriodicSobolev`, `IsPeriodicDatum`, Fourier coefficients, means, Leray,
pressure, or norms.  Consequently items 2–17 of
`research/T10/COMPARISON.md`'s “Needs a lemma” list are not prerequisites for
this theorem (in particular, item 9's physical/coefficient divergence bridge
is unnecessary because T16 states divergence physically).

The periodic gluing proof needs two elementary physical-layer lemmas that
should be delivered with T10's quotient/physical bridge, refining item 1 of
that list:

```lean
-- Coordinate generators imply invariance under every integer translate.
IsPeriodicOn I z →
  ∀ t ∈ I, ∀ x, ∀ k : PeriodicFrequency,
    z (t, x + latticeVector k) = z (t, x)

-- The lifted support set is invariant under every coordinate unit shift.
∀ x, x ∈ periodicSet S ↔ x + coordinateVector i ∈ periodicSet S
```

The first is the exact compatibility needed between T10's coordinate-generator
`IsPeriodicOn` and T16's all-lattice `periodicSet`; the second can be stated
as pointwise membership equivalence if set addition is inconvenient.  The
`torusLift`/Haar/Fourier portions of T10 item 1 are not needed for a direct
physical-lift proof, but will be needed if the registration binding transports
the result through the quotient torus.

## Open questions for the owner

1. The binding ruling selects B's globally quantified
   `potential_formula : ∀ t x, ...`, while the hypotheses and
   `potential_smooth`/`potential_curl` are local.  The global formula is
   satisfiable because it defines a total field, but A's local formula is the
   exact hypothesis-strength match.  Confirm the eventual V1 contract should
   preserve B's stronger formula.
2. B encodes an injective coordinate chart as `r < 1/2`; A allowed an
   arbitrary ball whose closed ball lies in a chosen fundamental cube.
   Confirm the fixed-radius encoding is the desired registered interface.
3. B's `correction_support_ball` records the fixed ball of radius `r`;
   A recorded the sharper scaled radius `ε * θRadius`.  Should the sharper
   inclusion be an additional theorem in the binding/proof layer, without
   changing this reconciled contract?
4. `periodicScaledPacket` is written as a total `tsum`, as in B.  Its
   intended local-finiteness semantics depend on T14's compact packet support;
   outside those hypotheses Lean's totalized sum can carry junk behavior.
   Should T14 register a locally-finite periodization operator or a support
   theorem strong enough to hide this totalization from later contracts?
5. When `T01.torus_data` is registered, should T16 import that contract
   directly and delete the two copied declarations in the same version, or
   should the replacement wait for the T16 registration lane so its drift
   bridge can be added atomically?

## Status (lane 347, 2026-09-18)

Proof lane 347 (Opus) delivered the canonical module
`formalization/NSFormalization/Section3/T16/LocalPotential.lean` and the probe
`research/T16/probes/api_on_canonical.lean`:

* **Reconciliation confirmed faithful.**  The 4 helper `def`s equal the Spec's
  copies by `rfl`, and `CutoffData`/`LocalPotentialAPI` convert fieldwise both
  ways, so every `Contracts.V1` operator in the Spec is definitionally the
  canonical `NavierStokes`/`Paper1`/`Source` notion.  `specStatement_of_module`
  shows the module's general theorem would close the Spec's statement.
* **Proved (general):** `exists_originCutoff` (+`[0,1]` range),
  `exists_timeCutoff`, `exists_threshold`; `potential_formula` is definitional.
* **Proved (v = 0):** the full `LocalPotentialAPI` (`localPotential_zero`), used
  as the non-vacuity `v=0,U=0,K={0}` instance.
* **Open (documented, `ATTEMPTS.md`/`SPEC_ISSUES.md`):** `potential_smooth`,
  `potential_curl` for general `v` (need a spatial-truncation lemma — the I02
  lemmas require `v` on `I ×ˢ univ`, not `I ×ˢ ball x₀ r`), and the entire
  periodic correction block (the lattice lift and its smoothness / periodicity /
  support / divergence / cancellation).

Answer to reconciliation open question 1 recorded in `SPEC_ISSUES.md` §1: B's
globally-quantified `potential_formula` is satisfiable definitionally, but the
*local* smoothness/curl hypotheses block direct I02 reuse.

## Status (lane 351, 2026-09-18) — Gap 1 closed for the potential

Proof lane 351 (Opus) delivered
`formalization/NSFormalization/Section3/T16/BallPotential.lean` and the probe
`research/T16/probes/ball_potential_closes.lean`, closing **Gap 1** (the radial
potential on the chart ball) for general local `v`:

* **`potential_smooth` (general `v`): PROVED** —
  `timePotential_contDiffOn_ball hI hv`. Route: at each `z ∈ I ×ˢ ball x₀ r`,
  truncate `v` by a `ContDiffBump` cutoff `χ` that is `1` on a plateau ball
  containing the radial segment and supported in `ball x₀ r`, apply
  `I02.timePotential_contDiffOn` to the globally-time-smooth `χ·v`, and transfer
  by the slicewise `timePotential_congr_segment`.
* **`potential_curl` (general `v`): PROVED** —
  `spatialCurl_timePotential_on_ball hv hdiv ht hx`. Route (ATTEMPTS §Gap1 option
  b): `I02.spatialCurl_timePotential_on` is genuinely global (its `hdiv` is
  universally quantified through `RadialPotential.curl_centeredPotential`), but
  `curl_potential` only consumes divergence at the segment points `r·x`,
  `r∈[0,1]`; so the new `curl_potential_of_segment` /
  `curl_centeredPotential_of_segment` weaken `hdiv` to `Set.Icc 0 1`, and `χ·v`
  (divergence-free on the plateau ball, `∇χ=0` there) qualifies.
* **`potential_formula`: definitional** (`centeredPotential_eq_integral`).
* **Packaged:** `exists_potential_on_ball` gives the three fields verbatim for
  lane 353 to fill `D.potential := timePotential v x₀` by `exact` (probe
  `ball_potential_closes.lean` proves this against the canonical field types,
  plus a nonzero constant-field non-vacuity instance).
* **Still open (Gap 2):** the periodic correction block, unchanged.

All 8 new declarations print `[propext, Classical.choice, Quot.sound]`
(`research/T16/axioms_ball_potential.lean`).
## Lane 352 (T16 gap 2: lattice lift) — status

The entire periodic-correction block flagged "Open" above is now **closed** in
`formalization/NSFormalization/Section3/T16/LatticeLift.lean` (all decls print
`[propext, Classical.choice, Quot.sound]`):

* `latticeLift w = periodize w` by `rfl` (frequency `latticeVector = lattice`
  agrees definitionally), so OpenAI's `NavierStokes.PeriodicLocalization` is
  reused verbatim.  The seven `correction_*` fields are transported:
  `latticeLift_smooth`, `latticeLift_periodic`, `latticeLift_eq_of_ball`
  (`correction_formula`), `latticeLift_divergence_zero`,
  `latticeLift_timeSupport` (`correction_support`), `latticeLift_sliceSupport`
  (`correction_support_ball`), `latticeLift_cancels` (`correction_cancels`).
* Packaged as `correction_fields_of_chart`: the seven canonical field bodies for
  `fun ε => latticeLift (W ε)` from transportable chart hypotheses.  Probe
  `probes/lattice_lift_closes.lean` restates each field verbatim + a nonzero bump.
* Note: `LocalPotentialAPI` has **seven** `correction_*` fields (the brief's
  "eight" double-counts `support`/`support_ball`).

## Lane 358 (T16 assembly: `localPotential`) — status

`theorem localPotential : localPotentialStatement` is **closed** in
`formalization/NSFormalization/Section3/T16/Assembly.lean` — **all 26 fields of the
reconciled `LocalPotentialAPI` discharged** for general local `v` (no `v = 0`
restriction), every declaration `[propext, Classical.choice, Quot.sound]`:

* 16 cutoff/threshold fields ← lane 347 (`exists_originCutoff`/`exists_timeCutoff`/
  `exists_threshold`); 3 potential fields ← lane 351 (`potential := timePotential v x₀`);
  7 correction fields ← lane 352's fixed `correction_fields_of_chart`, with
  `correction := fun ε => latticeLift (physicalCorrection v x₀ T θ η ε)`.
* The chart hypotheses of `correction_fields_of_chart` are discharged by:
  `hWformula` = `rfl`; `hWcompact` = `physical_compact`; `hWtsupp` = `physical_support`;
  `hWsmooth`/`hWdiv` = new **local-reference** companions
  (`physicalCorrection_contDiff`/`physicalCorrection_divergence`, joint spacetime
  truncation of `(η_ε θ_ε)•A`); `hWcancel` = `physicalCorrection_cancels` on the
  scaled plateau `x₀+ε•O`, packet bound via the time-truncated packet +
  `latticeLift_sliceSupport_closed`.
* Probe `probes/assembly_closes.lean`: `localPotential` closes the canonical
  statement, the reconciled Spec's copy (through `T16Probe.specStatement_of_module`),
  and a nonzero constant divergence-free non-vacuity instance.  Axiom audit
  `axioms_assembly.lean` (11 decls).  Depends on merge of `erenup/352-T16-lattice-lift`
  (local cancellation interface).
