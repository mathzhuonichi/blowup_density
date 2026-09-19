# T17 (`lem:correction`, `paper/sections/03-torus.tex:218-286`) — reconciliation of drafts A (lane 294) and B (lane 295)

Drafts: `.claude/worktrees/294-SPEC-t17-draft-a/research/T17/DraftA.lean` (1028 lines), `.claude/worktrees/295-SPEC-t17-draft-b/research/T17/DraftB.lean` (993 lines). Both blind, both statement-only, both elaborate. Both were written **before `T01.torus_data` was registered and before T15 was reconciled** — that changes the copy policy and the geometry packaging (§2, §3). Upstream read: `Contracts/V1/TorusData.lean`, `research/T10|T13|T15|T16/Spec.lean`, `Contracts/V1/Correction.lean` + `Contracts/V2/Correction.lean` (`I02.correction`, `I02.correction_v2`).

## 0. Lead review

(left for the lead)

## 0. Lead review (2026-09-18 05:30Z)
Drafted by an Opus subagent from the two blind drafts (294/295); reviewed and **approved** by the lead. Two decisions the draft left open: (a) **yes**, `CorrectionAPI` takes T15's `place : PlacementData P` as a parameter (T15 designed `PlacementData` for exactly this sharing; definitional equality of `T, x₀, K_*, B, ε₀` with T15/T18 is worth the extra packet parameter); (b) `mixedLebesgueENormT` stays a T17-local definition copied verbatim (T13 copy policy) — no change to the registered `T01.torus_data` now; registration is decided when T18 consumes it. All other rulings binding as written (real constants with `ENNReal.ofReal`, B's manuscript cylinder, the `𝒜_ε` chart binding to T16, B's two profile identities, registered `alpha`, torus-lift support measurement with A's open ball, T16/T13 witnesses as fields, honest `MemForceSobolevT 1 s` guard on `eq:HHs`, A's arithmetic `force_exponent_identity` demoted to a drift `example`).

## 1. Agreement

Both build one **Type-valued** `CorrectionAPI` over T16's already constructed `D : CutoffData` + `LocalPotentialAPI` and T13's `LocalizationAPI`, with every uniform constant as data fixed **before** `ε` (`:242`), every scale clause quantified over one `ε ∈ Ioc 0 D.ε₀`, and no packet field used. Identical, and identical to the paper:

* `eq:H` (`:219-223`) as a `def correctionForce ν v D ε` over T16's `D.correction ε`: `∂ₜw − ν•Δw + Dw(v) + Dv(w) + advection w`, i.e. `(v·∇)w` third and `(w·∇)v` fourth, the registered `Contracts.V1` operator tokens, time-first `SpaceTime`. Byte-identical in the two drafts (and equal to V1 `force_formula`, whose two middle summands are written in the opposite, commutative order).
* Both halves of `eq:derivativebounds` (`:226-233`) byte-identical to V1's `correction_derivative_bound`/`force_derivative_bound`: `j` unit time directions appended to `m` spatial directions of norm ≤ 1, `≤ C_{j,m}·(ε⁻¹)^(2j+m)` resp. `C_m·(ε⁻¹)^(2+m)`; arbitrary unit directions subsume every coordinate `β` with `m = |β|`.
* `eq:wE` (`:234`) as `energyENormT T (D.correction ε) ≤ … ε^(3/2)` in T10's torus energy norm on `(0,T)`, guarded by slice-wise `MemLp … 2 periodicTorusMeasure` for `w_ε` and its full gradient.
* `eq:Hmixed` (`:235-237`) as an **inequality** at the exponent `−2+3/p+2/q = α(p,q)+1`, over `p q : ℝ≥0∞` so that both essential-supremum endpoints are the `toReal ⊤ = 0` case with no separate clause, in a new torus mixed norm `mixedLebesgueENormT` (⨅ over strongly measurable normalized-Haar `Lp`-paths, `forceTimeMeasure` on `(0,∞)`) — byte-identical in both drafts **and** to T15's `mixedLebesgueENormT`.
* `eq:HHs` (`:239-241`) only at `q = 1`, `0 ≤ s ≤ 1`, through T10's `forceSobolevENormT 1 s`, `≤ C_s(ε^{3/2} + ε^{3/2−s})`, with the T13 witness present.
* `force_smooth` + `force_support` for "`H_ε` smooth across `T`, extends by zero" (`:225`), `force_periodic` (forced by the (P) representation; not literal in the lemma but required by every torus norm), `O(ε³)` spatial volume and `4ε²` time length measured **on one torus copy** because a periodic lift has infinite Euclidean spatial support, `viscosity_pos`, `eps_le_one`.
* The fixed-cylinder proof input (`:245-273`) is elevated to fields in both, exactly as the T17 row of `SECTION3_PLAN.md` asks: `W_ε` and the bracketed force profile are smooth, supported in an `ε`-independent cylinder, with every fixed `iteratedFDeriv` order bounded uniformly in `ε` there, and the physical force equal to `ε⁻²·bracket` under the chart `z ↦ (T + ε²σ, x₀ + εz)` (σ-origin at `T`, **not** at `t_ε = T − ε²`).

Neither draft omits a display, neither invents a norm or exponent, and no field is `True`/`∃ x, True`. I re-derived every rate against `:275-285`: `‖w‖_{L^∞L²} ≤ Cε^{3/2}` and `‖∇w‖_{L²L²} ≤ Cε^{-1}·ε^{3/2}·ε` (`:277-279`); `ε^{-2}·(ε³)^{1/p}·(ε²)^{1/q} = ε^{-2+3/p+2/q}` (`p=q=∞` is the amplitude bound `ε^{-2}`, `p=q=1` is `ε³`, `p=2,q=1` is `ε^{3/2}`); and for `eq:HHs` the amplitude `ε^{-2}` times the homogeneous factor `ε^{-1/2-s}` times the `ε²` time integration gives `ε^{3/2-s}`, against `ε^{3/2}` for the `L²` part (`:283-284`). All match.

## 2. Rulings

| clause | A | B | ruling (one-line reason) |
|---|---|---|---|
| constants type | real data + `ENNReal.ofReal (C * ε^…)` | `ℝ≥0∞` data + `_finite` + `C * ENNReal.ofReal (ε^…)` | **A.** House style: registered `I02.correction` (`energyConst`/`mixedConst : ℝ`) and T15 (`sobolevConst : ℝ → ℝ`) both use real constants inside one `ofReal`; B's product form also admits the `⊤ * 0` reading. Keep A's `0 ≤ C` fields (they block an unsatisfiable negative constant, which `ofReal` would collapse to `0`). |
| profile-uniformity constants | `∀ k, ∃ C, …` inside a `Prop` predicate `UniformlySmoothOnFixedCylinder` | data fields `correctionProfileConst`/`forceProfileConst : ℕ → ℝ` | **B.** Type-valued record with constants as data is the house rule; A's `∃` hides the very witnesses `:245-260` says are `ε`-independent. |
| hypothesis packaging | one grouped field `profiles : UniformProfileHypotheses` (6 clauses, incl. uniformity of `V_ε` and `𝒜_ε`) | inline fields for `W_ε` and the bracket only | **B, inline.** Uniform smoothness of `V_ε`/`𝒜_ε` is proof-internal: it follows from T16's `potential_smooth` + `eps_space`/`eps_time` on the cylinder, so it becomes a §4 lemma, not an obligation on the record. |
| fixed cylinder | `tsupport D.η ×ˢ tsupport D.θ` | `Icc (-2) 2 ×ˢ closedBall 0 D.θRadius` | **B.** The manuscript's cylinder (`:284` names the endpoints `σ = ±2`), `ε`-independent by construction, and contains A's by T16 `eta_support`/`theta_support`. |
| `𝒜_ε` | `ε⁻¹ • D.potential (chart z)` | the literal display `∫₀¹ ρ • cross (v …) z` | **A.** Defining the profile through T16's stored `D.potential` makes drift impossible; B's display (`:250-253`) becomes a change-of-variables obligation (§4). |
| profile ↔ physical identity | only for the force (`force_rescaling`) | both `correction_profile_identity` and `force_profile_identity` | **B. A gap:** without the correction identity, A's `correction_derivative_bound` on `D.correction` is logically disconnected from its own profile hypotheses. |
| `O(ε³)` spatial volume | per slice: `∀ t, μ_{T³}(tsupport (torusLift (H(t,·))))` | `μ_{T³}(Prod.snd '' tsupport (torusSpaceTimeLift H))` | **B.** The paper says "*its* spatial support" (one spacetime set), which is also V1's `Prod.snd '' tsupport` shape; on the torus lift that support is compact, so the projection is measurable, not merely outer-measurable. |
| `O(ε²)` time length | Euclidean `Prod.fst '' tsupport H` (V1 byte-shape) | `Prod.fst '' tsupport (torusSpaceTimeLift H)` | **B**, for one consistent lift convention and the same compactness argument; A's Euclidean spelling is recovered by periodicity and stays available as a binding-level `theorem`. |
| force support set | `Ioo(T±2ε²) ×ˢ periodicSet (ball x₀ (ε·θRadius))` | same with `closedBall` | **A.** V1's `correction_support` uses the open ball and T16's `theta_support` delivers it; B's closed ball is strictly weaker. |
| `α(p,q)` | new `correctionForceExponent := -2+3/p+2/q` **plus a field** `force_exponent_identity : … = alpha p q + 1` | new `correctionAlpha`, a duplicate of registered `alpha` | **neither.** Use the registered `Contracts.V1.alpha` (T15's `alphaT` is `rfl`-equal to it) and write `ε ^ (alpha p q + 1)`. **A's `force_exponent_identity` is a trivially true field** — pure arithmetic in `p,q`, provable by `ring`, mentioning neither `H_ε` nor `ε`; it is a drift check, so it goes outside the structure as an `example`, exactly as T15 does for `alphaT`. |
| `p,q` quantifier | `[Fact (1 ≤ p)] [Fact (1 ≤ q)]` | same | **T15's spelling:** `∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q → …`. `Fact (1 ≤ q)` is not needed for any type and is awkward to supply inside a field; T18 must match T15's `packetMixedScaling`. The range `1 ≤ p,q ≤ ∞` is the paper's at `:133` (`eq:Hmixed` itself names none). |
| `s` range | `s ∈ Icc 0 1` | `0 ≤ s → s ≤ 1` | **B** (= T15 `packetSobolevBound`). |
| `eq:HHs` honesty | `force_sobolev_path : ∃ G, IsPeriodicSobolevPath ∧ AEStronglyMeasurable` | none | **A's, respelled as T15's `MemForceSobolevT 1 s`** (adds `MemLp`). Not load-bearing (`⨅` over an empty subtype is `⊤`, so a finite bound already forces an honest path) but it is the sibling's guard and hands T18 the witness. |
| `MemLp` guards | `correction_slice_memLp`, `correction_gradient_memLp`, `force_spatial_memLp` | identical | **both, keep.** Load-bearing for `eq:wE` only: `energyENormT` is an `essSup`/`∫⁻` of `eLpNorm`, a *lower* integral that a non-measurable slice can make junk-small. For the two `⨅`-norms they are hygiene. |
| T16 / T13 witnesses | Prop **parameters** `_potential`, `_localization` | same | **fields** `potential`, `localization`, per the T15 ruling ("`I03` carries its upstream record as a field; a `Prop` parameter is decoration"). Both are proof-irrelevant either way. |
| geometry | ad-hoc parameters `_radiusPos`, `_chart : closure (ball x₀ r) ⊆ interior fundamentalCube`, `_referencePeriodic` | none at all | **A's content, repackaged as T15's `PlacementData`** (§3). B has no chart hypothesis, so its `force_sobolev_bound` cannot reach T13's `localization`, whose constant is quantified after a ball with `closure ⊆ interior fundamentalCube`. |
| `ε₀` | `eps_le_one : D.ε₀ ≤ 1` | same | **replace by `eps_le_placement : D.ε₀ ≤ place.ε₀`**; `≤ 1` then comes from `place.eps_le_one`, and T15's and T17's conclusions hold on one common scale interval. |
| chart map | `z ↦ (T + ε²z.1, x₀ + ε•z.2)` inlined | same, inlined | **keep the drafts' map, as one named helper** `correctionChartPoint`. Do **not** reuse T15's `scaledSourcePoint`: it is based at `t_ε = T − ε²`, the correction chart at `T` (σ ∈ `[-1,0)` on the active interval), a genuine shift of one. T16's `scaledTemporalCutoff … T ε` already uses the `T` origin. |
| mixed-norm vocabulary | re-declared under `T17.DraftA` | re-declared under `T17.DraftB` | **neither: copy T15's.** `IsPeriodicLebesgueSlicePath`/`mixedLebesgueENormT` are byte-identical in all three; a third copy under a `T17` namespace would make T18's identification non-syntactic. |

Nothing else in either draft is false or vacuous. A's per-slice volume field is true (just weaker than the paper's clause), B's `closedBall` support is true (just weaker than A's).

## 3. Decisions

**Base draft: B** (inline Type-valued fields, data profile constants, the manuscript cylinder, both profile identities, torus-lift support measures, V1 field order). **Take from A**: real constants + `ENNReal.ofReal`, `𝒜_ε` defined through `D.potential`, the open-ball force support, the `eq:HHs` path guard, and the chart/periodicity hypotheses — the last **re-expressed through T15's `PlacementData`**. **Drop**: A's `force_exponent_identity` (→ `example … := by ring`), A's `V_ε`/`𝒜_ε` uniformity fields (→ §4 lemma), both drafts' private `correctionAlpha`/`correctionForceExponent`.

Signature: `structure CorrectionAPI (ν : ℝ) {P : PacketAPI ν} (place : PlacementData P) (v : SpaceTimeField) (r δ : ℝ) (D : CutoffData) : Type`, with `T := place.T`, `x₀ := place.x₀`, `K := place.Kstar`, chart ball `(place.chartCenter, place.chartRadius)`. Reason: `research/T15/Spec.lean:560,915-921` says in so many words that the placement record exists "so T17 and T18 can consume definitionally the same `T,x₀,B,K_*,ε₀`". Cost — **open for the lead**: this drags a `PacketAPI ν` parameter into a lemma whose mathematics never uses the packet (T16 already carries `U` for the same reason). Fields, in order:

| field | informal statement | paper |
|---|---|---|
| `potential` | a T16 `LocalPotentialAPI v P.velocity place.Kstar place.x₀ r place.T δ D` witness | `:176-217` |
| `localization` | a T13 `LocalizationAPI` witness | `:22-98`, used `:284` |
| `viscosity_pos`, `radius_pos` | `0 < ν`, `0 < r` | `:219-223`, `:102-105` |
| `ball_in_chart` | `ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius` (with `place.chartBall_in_cube`, this is A's `_chart`) | `:102-105`, `:23` |
| `eps_le_placement` | `D.ε₀ ≤ place.ε₀` | `:103`, `:242` |
| `reference_periodic` | `IsPeriodicOn univ v` | `:2-4` (P) |
| `correction_profile_support` | `tsupport W_ε ⊆ Icc (-2) 2 ×ˢ closedBall 0 D.θRadius` | `:256-260` |
| `correctionProfileConst`, `_nonneg`, `correction_profile_uniform` | every `iteratedFDeriv` order of `W_ε` bounded on the cylinder, uniformly in `ε` | `:254-260` |
| `correction_profile_identity` | `w_ε(T+ε²σ, x₀+εz) = W_ε(z,σ)` | `:256-259` |
| `force_profile_support`, `forceProfileConst`, `_nonneg`, `force_profile_uniform` | the same three clauses for the bracketed force profile | `:262-273` |
| `force_profile_identity` | `H_ε(T+ε²σ, x₀+εz) = ε⁻² • bracket(z,σ)`, all three interior `ε` powers | `:264-272` |
| `force_smooth`, `force_periodic` | `H_ε` globally `C^∞` (so smooth across `T`) and unit-periodic | `:225` |
| `force_support` | `tsupport H_ε ⊆ Ioo(T−2ε², T+2ε²) ×ˢ periodicSet (ball x₀ (ε·D.θRadius))` | `:225`, `:188-189` |
| `spatialVolumeConst`, `_nonneg`, `force_spatial_volume` | torus volume of the spatial projection `≤ C ε³` | `:225` |
| `force_time_length` | length of the temporal projection `≤ 4ε²` | `:225` |
| `correctionDerivConst`, `_nonneg`, `correction_derivative_bound` | `|∂ₜʲ∂ₓᵝ w_ε| ≤ C_{β,j} ε^{−2j−|β|}` | `:226-229` |
| `forceDerivConst`, `_nonneg`, `force_derivative_bound` | `|∂ₓᵝ H_ε| ≤ C_β ε^{−2−|β|}` (`m = 0` is the amplitude bound) | `:229-232` |
| `correction_slice_memLp`, `correction_gradient_memLp` | honest Haar-`L²` slices for `w_ε` and `∇w_ε` | `01-introduction.tex:143-145` |
| `energyConst`, `_nonneg`, `correction_energy_bound` | `‖w_ε‖_{E_T} ≤ C ε^{3/2}` | `:234`, `:275-280` |
| `mixedConst`, `_nonneg`, `force_spatial_memLp`, `force_mixed_bound` | honest `L^p(T³)` slices for every `p`, and `‖H_ε‖_{L^q(0,∞;L^p(T³))} ≤ C_{p,q} ε^{α(p,q)+1}`, `1 ≤ p,q ≤ ∞` | `:235-238`, `:281-282` |
| `sobolevConst`, `sobolevConst_pos`, `forceSobolev_memLp`, `force_sobolev_bound` | `0 < C_s`; an honest `L¹(0,∞;H^s(T³))` datum path; `‖H_ε‖_{L¹_tH^s(T³)} ≤ C_s(ε^{3/2}+ε^{3/2−s})`, `0 ≤ s ≤ 1` | `:239-242`, `:284` |

Constants: real data fields with `0 ≤ ·`, except `sobolevConst` which takes T15's strict `0 < ·` on `[0,1]` (same node, same name, same consumer). Outside the structure, three drift `example`s: `-2 + 3/p.toReal + 2/q.toReal = alpha p q + 1` (`by ring`), and `rfl` checks of the copied `mixedLebesgueENormT`/`alpha` against their T15/V1 originals. **One addition beyond both drafts, shape only**: a `def correctionStatement : Prop` closing the record existentially with the data pinned (`Nonempty (CorrectionAPI ν place v r δ D)` under T16's hypotheses), matching `Contracts/V1/Correction.lean:542` `correctionStatement`, T16's `localPotentialStatement` and T15's `scalingStatement`. No new mathematical field is introduced; the paper demands none that both drafts missed.

**Vocabulary / copy policy** (both drafts predate the registration): `import Contracts.V1.TorusData` for the registered T10 half (`IsPeriodicOn`, `torusLift`, `periodicTorusMeasure`, `PeriodicSobolev`, `IsPeriodicDatum`, `periodicSobolevENorm`) and `Contracts.V1.Correction` for `curl`/`cross`/`scaledSpatialCutoff`/`scaledTemporalCutoff`/`alpha`/`PacketAPI`; then verbatim delimited copies, in their own namespaces, of (i) the still-unregistered T10 solution-class half `BlowupDensity.T10.Draft` (`IsPeriodicSobolevPath`, `forceSobolevENormT`, `energyEssSupT`/`energyGradientT`/`energyENormT`), (ii) `BlowupDensity.T13.Spec` (`fundamentalCube`, `SupportedInBall`, `latticeVector`, `periodize`, `LocalizationAPI` and the kernels it needs), (iii) `BlowupDensity.T16.Spec` (`latticeVector`, `periodicSet`, `CutoffData`, `LocalPotentialAPI`), (iv) `BlowupDensity.T15.Draft` (`IsPeriodicLebesgueSlicePath`, `mixedLebesgueENormT`, `MemForceSobolevT`, `PlacementData`). Every copy carries the `copied verbatim from research/<ID>/Spec.lean:<lines>` marker and must stay byte-identical, exactly as `research/T15/Spec.lean` does for T10/T13/T14.

## 4. Next

**Spec lane**: write `research/T17/Spec.lean` per §3, elaborate it (`cd verification && lake env lean ../research/T17/Spec.lean`), and merge the two comparisons into `research/T17/COMPARISON.md` keeping both paper-clause tables, both ambiguity lists and both candidate lists.

**"Needs a lemma" union (A 1-7 ∪ B 1-5, deduped)**: ① rescale T16's `correction_formula` on the chart and identify it with `W_ε` (`correction_profile_identity`), and identify `ε⁻¹•D.potential(chart)` with the display `∫₀¹ρ v(x₀+ερz)×z dρ` from `potential_formula`. ② affine chain rule for `force_profile_identity` with the exact `ε`, `ε²`, `ε⁻²` factors. ③ uniform derivative constants from joint smoothness of `(ε,z) ↦` profile on `[0,ε₀] × cylinder` — including the dropped `V_ε`/`𝒜_ε` step, which needs `eps_space`/`eps_time` to keep the chart inside `Ioo 0 (T+δ) ×ˢ ball x₀ r`. ④ transfer of the single central copy to `periodicSet`, periodicity of `correctionForce`, and the torus support volume/duration. ⑤ periodic energy scaling and the honest `L²` slice paths for `energyENormT`. ⑥ mixed-norm change of variables for all `1 ≤ p,q ≤ ∞` including both `∞` endpoints, plus the strongly measurable `Lp` path and the `|Q| = 1` Haar-vs-Lebesgue identification. ⑦ express each force slice as `periodize` of its compactly supported central copy, apply `LocalizationAPI.localization` for `0 < s < 1` and `endpoint_zero`/`endpoint_one` at `s = 0,1` with one `ε`-independent constant, integrate in time (`ε²`), and assemble the T10 datum path for `forceSobolev_memLp`. ⑧ `ball_in_chart` + `place.chartBall_in_cube` ⇒ T13's chart hypothesis; the `x₀ + εK_* ⊆ B` half is already `place.eps_space`.

**Implementation candidates** (union of both comparisons; none imported by the spec, none discharges a field alone): `Paper1/CorrectionProfile.lean` `profile_smooth`, `profile_support`, `profile_uniform_derivative_bound`, `profile_uniform_global_derivative_bound`, `physicalCorrection_rescale`, `physicalCorrection_eq_profile:223`, `physical_mixed_derivative_bound`; `Paper1/CorrectionForceProfile.lean` `forceProfile`, `forceProfile_eq_operators`, `forceProfile_smooth`, `forceProfile_support`, `physicalForce_eq_profile:185`, `forceProfile_uniform_derivative_bound`, `physicalForce_spatial_derivative_bound`; `Paper1/CorrectionEnergy.lean` `compact_energy_bound`, `physicalCorrection_uniform_energy`, `physicalCorrection_total_direction_energy`; `Paper1/CorrectionMixedNorms.lean` `physical_force_spatial_memLp`, `physical_force_mixed_bound:123`, `physical_force_mixed_memLp`; `Paper1/CorrectionPositiveNorms.lean` + `CorrectionVectorNorms.lean` (positive-order profile bounds, vector assembly); `Paper1/PeriodicCorrectionEndpointRates.lean:49` `correction_vector_whole_endpoint_rates` (whole-space `s = 0,1` rates, still needs the T13 single-copy adapter). Two files neither comparison listed but which sit on ⑦: `Paper1/CorrectionForceNorms.lean:78,100` `scalarProfile_uniform_homogeneous(_time)` (uniform homogeneous-norm bounds of the force profile) and `Paper1/PeriodicCorrectionEndpointInstantiation.lean:30` `eventually_correction_coordinate_periodized_endpoint_product` (the only existing *periodized* endpoint statement).

**Open for the lead / owner**: (a) whether `CorrectionAPI` should carry `place : PlacementData P` — definitional sharing with T15/T18 at the price of a `PacketAPI` parameter the lemma's mathematics does not use; (b) whether `mixedLebesgueENormT` should move into the T10 data contract (raised by draft B) rather than being copied by both T15 and T17 — a T01/T10 contract change, hence not a T17 decision.

## Lead amendment — completed G4, lane 453 continuation

The user's final block is implemented literally in the raw-field
`correctionStatementAmended`: positive viscosity/radius/margin, `r < 1/2`,
periodicity, global smoothness, divergence-free on the chart cylinder, raw
packet support on `(0,1)`, and the requested ball's inclusion in the placement
chart. The last clause repairs the accepted geometry counterexample; it is not
inferred from the API being constructed. Compactness and positive target time
come from placement. G1 is handled at statement level, and G3 by raw fields.

The unamended statement and every API field remain unchanged. The contract's
`Packet` namespace preserves the Spec's `CorrectionAPI` and unamended statement
byte-for-byte; the enclosing raw-field record gives the completed G4 block
without requiring an artificial `PacketAPI` for arbitrary raw fields. Fieldwise
conversions and round trips connect the two contract spellings and the canonical
record. Only the amended statement is registered. Cutoffs come from T16 with
threshold `min ε₁ place.ε₀`; every bound uses that same positive threshold.

### Lead amendment (2026-09-19 12:45Z, G4)

`correctionStatement` is registered with the hypothesis block of the registered `T02.local_potential` statement plus `0 < ν` and the global `ContDiff ℝ ∞ v` (G1 option (a) at the statement level; the `CorrectionAPI` field list is unchanged). See `SPEC_ISSUES.md` (G4). Owner-pending: whether the Spec text should be amended to carry these hypotheses explicitly (V1 wording).

> Addendum (2026-09-19 12:53Z): the amended hypothesis block also carries `ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius` and the raw packet support clause — see `SPEC_ISSUES.md` G4 addendum (lane 453 counterexample).
