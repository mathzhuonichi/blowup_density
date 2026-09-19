# T18 — proof-lane split (`thm:insertion`, exact local insertion on `T³`, `paper/sections/03-torus.tex:287-346`)

Lead-facing, 2026-09-18. Target = the reconciled `PeriodicInsertionAPI` (`research/T18/Spec.lean:1658-1967`,
**11 parameters / 45 fields**) + `periodicInsertionStatement` (`Spec.lean:1977`). Design =
`research/T18/RECONCILIATION.md` §3-§4 + `COMPARISON.md` "Proof dependencies". Twin = Section 4 R42
(`Contracts/V1/InsertionFamily.lean`, `Contracts/V2/InsertionLifespan.lean`, `Section4/R42/*`; splits
`research/R42/LIFESPAN_SPLIT.md`, `MAXIMAL_SPLIT.md` — **same proof skeleton**). House style =
`research/T11/T11_SPLIT.md`, `research/T17/T17_SPLIT.md`.
Size: **S** ≤ ~100 lines; **M** one self-contained lemma with a known proof; **L** a multi-file campaign.
Model: `codex-sol` = reuse/transport/algebra/bookkeeping; `Opus` = analytic core.

## 0. Ground rules

**Peeling rule.** Every unit ends in a `theorem` whose statement **is** a `PeriodicInsertionAPI` field of
`Spec.lean` verbatim, or a lemma directly consumed by one. A unit that cannot close its target from the tree
names **exactly one** input hypothesis (a `def … : Prop` in `Section3/T18/`, written out, non-tautological,
discharged by a later unit); no named input for hard analytic units.

**T18 has essentially no named inputs — everything ambient is threaded or registered+inhabited.** Unlike
T11/T15/T17, T18 is an *assembly* over three richer objects, so its proof obligations reduce to combining
given fields:
- **Threaded parameters** (given as structure hypotheses, `Spec.lean:1658-1665`): `scaling : ScalingAPI P place`
  (T15) and `correction : CorrectionAPI ν place reference.velocity r δ D` (T17, carrying `.potential :
  LocalPotentialAPI` = T16 and `.localization : LocalizationAPI` = T13), plus `P` (T14 energy-enhanced packet),
  `place`, `reference`, `a,g,r,δ,D`. The proof **uses their fields directly**; it does **not** re-prove or
  inhabit T13/T14/T15/T16/T17.
- **Registered + inhabited** (consumed by name, `Bindings/TorusLocalTheory.lean:355,387`): T11
  `torusLocalTheoryAPI` / `torusContinuationH3API`; the **H³-narrowed** continuation (see §H1/H3).
- **Proved local lemma** (consumed by name): T12 `boundedRepresentative` (`Section3/T12/FourierEmbeddings.lean:386`,
  `‖v‖_{L∞} ≤ Cinfty‖v‖_{H²}`, H²↪L∞); T16 lattice lift (`Section3/T16/LatticeLift.lean`).

**Blocking = non-vacuity, not provability (T15/T17 precedent).** Because `scaling`/`correction` are threaded,
every T18 field *theorem* is provable now from the structure hypotheses. A unit is marked **"gated on
<T15/T17 unit>"** when the specific `scaling.*` / `correction.*` bound field it consumes is the *output* of a
still-unfinished T15/T17 lane (T15 wave-1 only merged: `Section3/T15/{Bridges,ParsevalZero,HaarBridge}.lean`;
T17 U5-U12 pending, incl. the T13-gated Sobolev, `research/T17/T17_SPLIT.md`) — exactly the staging T15/T17
used for their T13-gated fields. Gated units are still lane-startable against the structure hypothesis; only
their end-to-end **non-vacuity / `Nonempty` closure** (U12) waits.

**Which fields need the H¹-ball restart vs the H³-narrowed API.** **None need `PeriodicRestartH1`.** The
lifespan-exactly-`T` unit (U8) consumes only the **H³-narrowed** `torusContinuationH3API`
(`higherOrderBound`, `extendsBeyond`, `lifespanInfiniteOfLocallyFinite` — the three ball-free manuscript
fields — and `restartBeyondH3`) plus `torusLocalTheoryAPI.{velocity_unique, solution, regularity}`. Per
`research/T11/H1_GAP.md` §3: the inserted datum `a` and force `g_ε` are explicit smooth periodic objects, so
every `H^m` norm (in particular the H³ ball) is finite/computable; the `≤T` half is the ball-free
`lifespanInfiniteOfLocallyFinite` fed by `higherOrderBound` at `m=3` against `blowup_limsup` (through H²↪L∞),
and the `≥T` half is local existence/uniqueness, which carry no ball. **No T18 field mentions
`periodicSobolevENorm 1`** (grep: the only tree hits are `research/T20/Spec.lean:402,437`). So U8 confirms the
H1_GAP "expected OK" verdict; `PeriodicRestartH1`/`PeriodicRestartBeyondH1` stay unconsumed.

**Lead note (2026-09-18 13:02Z) — canonical-module prerequisite.** `formalization/` cannot import `Contracts.V1.PacketAPI` (T17 issue G3), so the T18 canonical module cannot take `P : PacketImportAPI ν`, `place : PlacementData P`, `scaling : ScalingAPI P place`, `correction : CorrectionAPI …` in the Spec's spelling. Prerequisites, added as units: **T15 U-CAN** (lane 384): `Section3/T15/Scaling.lean` restating `PlacementData` and `ScalingAPI` over the raw packet fields (`u p f : VelocityField`, `carrier`, the `PacketAPI`/`PacketEnergyAPI` clauses used, as explicit hypotheses/fields) with a probe converting from the Spec's `PacketImportAPI`-based structures (probes may import `Contracts.*`); **T17 U-CAN** (first half of U12): `Section3/T17/Correction.lean` restating `CorrectionAPI` over the canonical T15/T16 records with the bare `(x₀, T)` spelling of lanes 370/373/375. T18 U1 starts after both land; the T18 canonical structure threads the canonical records, and the assembly/contract lane (U12) converts to the Spec's spelling in `verification/`.

## 1. Units

`v := reference.velocity`, `π := reference.pressure`, `w_ε := D.correction ε`, `H_ε := correctionForce ν v D ε`,
`U_ε := periodizedScaledVelocity P place.x₀ place.T ε`, `P_ε := periodizedScaledPressure …`,
`F_ε := periodizedScaledForce …`, `b_ε := correctedBackground v D.correction ε`.

- **U1 — inserted triple + the three `eq:insertion` formulas + threshold + trivial hypotheses.**
  New `Section3/T18/Insertion.lean`. Targets (verbatim): `velocity`/`pressure`/`force` (data, `Spec.lean:1700-1704`),
  `velocity_formula` (`:1710`), `pressure_formula` (`:1723`), `force_formula` (`:1732`), `ε₀` (`:1684`),
  `eps_pos` (`:1686`), `eps_le_scaling` (`:1691`), `eps_le_cutoff` (`:1696`), `delta_pos` (`:1671`),
  `reference_force_mem` (`:1675`), `initial_mem` (`:1679`). Route: `def velocity ε z := v z + w_ε z + U_ε z`,
  `pressure ε := normalizePressureT (fun z => π z + P_ε z)`, `force ε z := g z + H_ε z + F_ε z`; the three
  `*_formula` close by `rfl`. `ε₀ := min place.ε₀ D.ε₀`; `eps_pos` from `place.eps_pos`/`D.eps_pos`; the two
  `≤` by `min_le_left`/`min_le_right`. `delta_pos`/`reference_force_mem`/`initial_mem` are the statement's
  hypotheses `hδ`/`hg`/`ha`. **S, codex-sol.** No named input. Deps: —.
  **Status (lane 422, 2026-09-18): complete.** Canonical raw-field bundle, all eleven U1 fields, Spec-form
  conversion probe, and exact three-axiom audit pass; concrete end-to-end non-vacuity remains with the
  separately scoped T15 U15 and T17 assembly witnesses.

- **U2 — force class memberships.** New `Section3/T18/ForceClass.lean`. Targets `force_mem` (`Spec.lean:1741`),
  `forceDifference_mem` (`:1746`). Route: `g_ε - g = H_ε + F_ε`; `forceClassT` = `MemForceT` (smooth + unit-periodic +
  compact-in-`(0,∞)` support) is closed under `+`. `H_ε ∈ 𝓕` from `correction.force_smooth`/`force_periodic`/
  `force_support` (`Spec.lean:1445,1449,1453`); `F_ε ∈ 𝓕` from `scaling.force_mem` (`:632`, `MemForceT`); sum
  ⟹ `forceDifference_mem`; `+ g` (`reference_force_mem`) ⟹ `force_mem`. Mirrors R42
  `memForceR_insertedForce` / `forceDifference_compact` (`LIFESPAN_SPLIT.md` #3). **S-M, codex-sol.** No named
  input. Deps: U1 (threaded `scaling.force_mem` = T15 U7, `correction.force_*` = T17 U7).

  **Status (lane 426, 2026-09-18): complete.** Both force-class fields proved by compact time-support union; no missing threaded fact.
  Canonical theorems, Spec-form conversion probe, and exact three-axiom audit pass.

- **U3 — regularity, initial value, history, periodicity.** New `Section3/T18/Kinematics.lean`. Targets
  `velocity_smooth` (`Spec.lean:1753`), `pressure_smooth` (`:1758`), `initial` (`:1763`), `history` (`:1780`),
  `velocity_periodic` (`:1786`). Route: each is a summand fact. Smoothness on `Ico 0 T ×ˢ univ` from
  `reference.velocity_smooth`/`pressure_smooth` + `correction.correction_smooth`/`force_profile_smooth` +
  the periodized-packet smoothness inside `scaling.solution`; periodicity from `reference` periodicity +
  `correction.correction_periodic` + periodize periodicity (`latticeLift_periodic`); `initial` (`u_ε(0,·)=a`)
  and `history` (`u_ε=v` on `0≤t≤T-2ε²`) because `w_ε=0` (`correction.correction_support`, supp ⊆
  `Ioo(T-2ε²,T+2ε²)`) and `U_ε=0` before `t_ε=T-ε²` (packet zero-past, self-contained from the copied
  `scaledSourcePoint`/`zeroPastField`), and `T-2ε²<t_ε`. Mirror R42 assembly (`Section4/R42/Assembly.lean`).
  **M, codex-sol.** No named input. Deps: U1.

  **Status (lane 426, 2026-09-18): complete.** All five kinematic fields proved, including normalized pressure smoothness and the closed quiet-history endpoint.
  Canonical theorems, Spec-form conversion probe, and exact three-axiom audit pass.

- **U4 — incompressibility.** New `Section3/T18/Divergence.lean`. Targets `incompressible` (`Spec.lean:1767`),
  `velocityDifference_divFree` (`:1858`) — the second is `incompressible` minus `v`. Route:
  `div u_ε = div v + div w_ε + div U_ε = 0` on `Ico 0 T`: `div v = 0` from `reference.divergence`; `div w_ε = 0`
  from `correction.correction_divergence_free` (`Spec.lean:1070`, it is a spatial curl); `div U_ε = 0` from
  `scaling.solution`'s `.divergence` (periodized packet). **S-M, codex-sol.** No named input. Deps: U1
  (threaded `scaling.solution` = T15 U11).

  **Status (lane 426, 2026-09-18): complete.** Both divergence fields proved on Ico 0 T, including time zero.
  Canonical theorems, Spec-form conversion probe, and exact three-axiom audit pass.

- **U5 — the two vanishing cross-transport terms.** New `Section3/T18/CrossTransport.lean`. Targets
  `crossTransport_background_advects_packet` (`Spec.lean:1838`, `(b_ε·∇)U_ε=0`),
  `crossTransport_packet_advects_background` (`:1848`, `(U_ε·∇)b_ε=0`), both on `Ico 0 T` as
  `spatialDerivative … = 0`. Route (`eq:bgzero`, `:322-328`): pointwise case split on `x`. On a neighborhood
  `O ⊇ supp U_ε(t,·)`, `b_ε(t,x)=0` **with all derivatives** by `correction.potential.correction_cancels`
  (`Spec.lean:1094`, for `t ∈ Ico (T-ε²) T`) — so `(b_ε·∇)U_ε` (direction `b_ε=0`) and `(U_ε·∇)b_ε`
  (`∇b_ε=0`) both vanish; off `O`, `x ∉ supp U_ε` so `U_ε` and `∇U_ε` vanish. For `t < T-ε²`, `U_ε(t,·)=0`
  (packet zero-past). Reuse T16 `latticeLift_cancels` (`Section3/T16/LatticeLift.lean:365`) and the
  directional-Fréchet locality of `spatialDerivative`. **M, Opus.** No named input. Deps: U1
  (`correction.potential` = T16, DONE; the periodized-packet-before-start is self-contained).

  **Status (lane 433, 2026-09-18): complete.** Both cross-transport fields proved on `Ico 0 T`, with the
  case split at exactly `t_ε = T - ε²`: before it the periodized packet *slice* is the constant zero field
  (`packet_slice_zero`, sharper than lane 426's pointwise `packet_quiet`), from it on
  `correction.potential.correction_cancels` supplies the open removal set and the Section 4 lemma
  `Source.cross_advection_eq_zero` closes both terms. The T16 `periodicScaledPacket` and the T15
  `periodizedScaledVelocity` spellings are `rfl`-equal (`periodicScaledPacket_eq`), so no transport is
  needed. Canonical theorems, Spec-form conversion probe, and exact three-axiom audit pass.

- **U6 — the exact momentum equation (`eq:insertion` exactness).** New `Section3/T18/Momentum.lean`. Target
  `momentum` (`Spec.lean:1774`, `navierStokesResidual ν (velocity ε) (pressure ε) t x = force ε (t,x)` on
  `Ioo 0 T`). Route (`:315-328`): the corrected background `b_ε=v+w_ε` satisfies
  `∂_t b_ε+(b_ε·∇)b_ε-νΔb_ε+∇π = g+H_ε` (from `reference.momentum` + the *definition* of `H_ε` =
  `correctionForce` as that residual); adding the periodized-packet equation `NS(U_ε,P_ε)=F_ε`
  (`scaling.solution`'s `.momentum`) reconstructs `NS(u_ε,p_ε)` up to the two cross terms, which are `0` by
  **U5**; pressure via `pressure_formula` (mean-zero normalization is a spatially constant shift, `∇` unchanged).
  Mirror R42 `Section4/R42/Assembly.lean` momentum. **M-L, Opus.** No named input. Deps: U1, U5 (threaded
  `scaling.solution` = T15 U11).

  **Status (lane 433, 2026-09-18): complete.** `momentum` proved on `Ioo 0 T`. `Source.residual ν` is
  `rfl`-equal to the registered `navierStokesResidual ν`, so `Source.{residual_add, corrected_background}`
  apply directly; the two cross terms they produce are discharged by U5, the reference equation by
  `reference.momentum`, the packet equation by `scaling.solution`'s `momentum`, and both mean-zero gauges by
  one hypothesis-free lemma `pressureGradient_normalizePressureT` (`fderiv_sub_const`). Canonical theorems,
  Spec-form conversion probe, and exact three-axiom audit pass.

- **U7 — localization of the velocity difference (clause (iii)).** New `Section3/T18/Support.lean`. Targets
  `diffSupportRadius` (`Spec.lean:1863`), `diffSupportRadius_pos` (`:1865`), `velocityDifference_support`
  (`:1873`), `diffSupport_in_chart` (`:1880`). Route: `u_ε-v = w_ε+U_ε`, both unit-periodic; set
  `ρ := max D.θRadius R_K` (`R_K` = packet-carrier radius) so each spatial slice's `tsupport ⊆
  periodicSet (Metric.ball place.x₀ (ε·ρ))` (diameter `O(ε)`) via T16 `latticeLift_sliceSupport`
  (`LatticeLift.lean:275`) for `w_ε` and `scaling.velocity_singleCopy` + `place.eps_space` for `U_ε`;
  `diffSupport_in_chart` = `place.eps_space`/`chartBall_in_cube`. **A's single-ball form is FALSE** for a
  periodic difference (`RECONCILIATION.md` §"False clauses"); keep `periodicSet`. **M, codex-sol.** No named
  input. Deps: U1.

- **U8 — lifespan exactly `T`, maximality, blow-up (clause (i)).** New `Section3/T18/Lifespan.lean`. Targets
  `solution` (`Spec.lean:1796`), `maximal` (`:1806`), `lifespan` (`:1812`), `blowup` (`:1818`),
  `blowup_limsup` (`:1825`). Route (mirror `R42/LIFESPAN_SPLIT.md` + `MAXIMAL_SPLIT.md`):
  (a) `solution` = one full-horizon `ClassicalSolutionT ν a (force ε) place.T` from U3/U4/U6 + the Sobolev
  datum path (R42 residual 1a/1e-i: cutoff-in-time the compact-support difference, `contDiff_angularPath`,
  then `+` `reference.sobolev`) + `pressure_gradient`; regularity via T11 `regularity_of_classical`
  (`Section3/T11/ClassicalRegularity.lean`, every `ClassicalSolutionT` is regular).
  (b) `blowup`: on the active support `u_ε=U_ε` (because `b_ε=0` there, U5/`correction_cancels`), so
  `SpeedUnboundedAt` transfers from `scaling.unboundedSpeed` of `U_ε` (`:675`).
  (c) `blowup_limsup`: pointwise `SpeedUnboundedAt` + slice continuity (`velocity_smooth`) ⟹ ess-sup lower
  bound via `IsOpenPosMeasure`, then `limsup … = ⊤` (R42 `blowup_essSup`, `LIFESPAN_SPLIT.md` #2).
  (d) `lifespan` = `le_antisymm`: `≥T` from `solution` on every `S<T` + `torusLocalTheoryAPI.velocity_unique`
  (`Contracts/V1/TorusLocalTheory.lean:467`); `≤T` from `torusContinuationH3API.lifespanInfiniteOfLocallyFinite`
  (`:579`) + `higherOrderBound` (`:539`) at `m=3` against `blowup_limsup`, transferred L∞→H² by T12
  `boundedRepresentative` (`Section3/T12/FourierEmbeddings.lean:386`).
  (e) `maximal` = `IsMaximalPeriodicSolution` from `lifespan` + the shorter-horizon family + `velocity_unique`
  (mirror R42 `Bindings/InsertionLifespan.lean §9 isMaximalSolution_of_inserted`, `MAXIMAL_SPLIT.md`).
  **Uses the H³-narrowed API only — no `PeriodicRestartH1` (§H1/H3).** **L, Opus.** No named input. Deps:
  U1, U3, U4, U6 (threaded `scaling.solution`/`unboundedSpeed` = T15 U11/U6; registered T11+T12, DONE).

- **U9 — `eq:Eclose` (energy closeness).** New `Section3/T18/EnergyRate.lean`. Target `energyRate`
  (`Spec.lean:1892`, `‖u_ε-v‖_{E_T} ≤ (M+D)ε^{1/2}+Cε^{3/2}`). Route: `u_ε-v=w_ε+U_ε`; triangle inequality
  for `energyENormT place.T` (Minkowski on `essSup+lintegral`, no `MemLp` guard needed) ⟹
  `≤ ‖U_ε‖ + ‖w_ε‖`; `‖U_ε‖ = (M+D)ε^{1/2}` from `scaling.packetEnergyIdentity` (`:698`) +
  `packetDissipationIdentity` (`:709`), `M=P.energyBound`, `D=P.dissipationBound`; `‖w_ε‖ ≤ Cε^{3/2}` with
  `C=correction.energyConst` from `correction.correction_energy_bound` (`Spec.lean:1523`). **M, Opus.** Hard
  analytic (norm triangle), no named input. Deps: U1. **Gated on T15 U4 + T17 U9.**
  **Lane 443 status:** analytic triangle and all threaded bookkeeping are complete as
  `energyRate_separateConstants`.  The exact canonical field is blocked only by absent
  `0 ≤ energyBound` and `0 ≤ dissipationBound` fields; the Spec-form field closes in
  `probes/u9_u10_closes.lean` from `PacketImportAPI.energy_isLUB` and `dissipation_eq`.

- **U10 — `eq:Fclose` (mixed-norm closeness).** New `Section3/T18/MixedRate.lean`. Targets `forceDiffMixedConst`
  (`Spec.lean:1899`), `forceDiffMixedConst_nonneg` (`:1902`), `forceDifference_mixed_memLp` (`:1910`),
  `forceDifference_mixed_bound` (`:1919`). Route: `g_ε-g=H_ε+F_ε`; the honesty guard `MemMixedLebesgueT q p`
  from `scaling.mixed_memLp` (`:722`, `F_ε` path) + `correction.force_spatial_memLp` (`Spec.lean:1528`, `H_ε`
  path) via `MemLp.add`; the bound by `mixedLebesgueENormT` triangle ≤ `ε^{α}‖F‖` (`scaling.packetMixedScaling`,
  `:736`) + `C_{pq}ε^{α+1}` (`correction.force_mixed_bound`, `Spec.lean:1541`), `α := Contracts.V1.alpha`;
  `forceDiffMixedConst p q` absorbs both, `_nonneg` on `1≤p,q`. **M-L, Opus.** No named input. Deps: U1, U2.
  **Gated on T15 U5 + T17 U10.**
  **Lane 443 status:** complete.  All four exact canonical fields close; finiteness of
  `correction.force_mixed_bound` supplies the correction's honest mixed path, so no
  additional continuity reconstruction or named input is required.

- **U11 — `eq:Hsclose` + the `s<0` tail (Sobolev closeness).** New `Section3/T18/SobolevRate.lean`. Targets
  `forceDiffSobolevConst` (`Spec.lean:1928`), `forceDiffSobolevConst_pos` (`:1932`),
  `forceDifference_sobolev_memLp` (`:1938`), `forceDifference_sobolev_bound` (`:1948`, `0≤s<1/2`,
  `C_s(ε^{1/2-s}+ε^{3/2-s})`), `forceDifference_negativeSobolev_tendsto` (`:1957`), `negative_s_memLp`
  (`:1965`). Route: `forceSobolevENormT 1 s` triangle on `H_ε+F_ε`: `‖F_ε‖ ≤ C_s ε^{1/2-s}` from
  `scaling.packetSobolevBound` (`:778`, absorbing the `ε^{1/2}` lower term since `0≤s`, `ε≤1`); `‖H_ε‖ ≤
  C_s ε^{3/2-s}` from `correction.force_sobolev_bound` (`Spec.lean:1560`); honesty guards from
  `scaling.forceSobolev_memLp` (`:766`) + `correction.forceSobolev_memLp` (`Spec.lean:1555`) via `MemLp.add`
  (both for `s≥0` and, for `negative_s_memLp`, `s<0`); the `s<0` `Tendsto`→0 from `scaling.forceConvergence`
  (`:797`, `q=1`) + the correction tail. Precedent `Paper1/PeriodicInsertionPositiveConvergence.lean:73`.
  **L, Opus.** No named input. Deps: U1, U2. **Gated on T15 U13+U14 and T17 U11 — both transitively on
  T13.localization (`correction.localization`).**

- **U12 — assembly + statement + contract/bindings/tests + non-vacuity.** New `Section3/T18/Assembly.lean`
  + a fresh `Contracts/V1/…` (T18 registration, T03 umbrella per PLAN §8) + `Bindings` + `Tests`. Bundle
  U1-U11 into `PeriodicInsertionAPI` and close `periodicInsertionStatement` (`Spec.lean:1977`,
  `Nonempty (…)` under `0<ν, δ>0, g∈𝓕, a∈𝓧`). Because `scaling`/`correction` are threaded parameters, the
  **statement closes as soon as U1-U11 are proved**; the **non-vacuity example** (a concrete inhabited
  `scaling`/`correction`/`reference`) is **gated on T15 U15 + T17 U12 + T13 assembly**. Register every field;
  stage the closeness/non-vacuity tests behind the gates, exactly as T15/T17 staged their T13-gated fields.
  **G1 spec note (`research/T17/SPEC_ISSUES.md`):** if T17 assembly adds `reference_smooth` to `CorrectionAPI`,
  U1's `velocity_formula`/U3 pick it up for free (reference is a classical solution, globally smooth after a
  time cutoff); no T18 field changes. **M, codex-sol.** Deps: all.

## 2. Proof-dependency ledger (which T11-T17 declaration each unit consumes; from RECONCILIATION §4)

| unit | T11 (registered) | T12 | T13 | T14/T15 (`scaling`,`P`) | T16/T17 (`correction`,`D`) |
|---|---|---|---|---|---|
| U1 | — | — | — | `periodizedScaled*` (copied defs) | `D.correction`,`correctionForce` (copied) |
| U2 | — | — | — | `scaling.force_mem` | `correction.force_smooth/periodic/support` |
| U3 | `ClassicalRegularity` | — | — | packet zero-past; `scaling.solution` regularity | `correction.correction_smooth/periodic/support` |
| U4 | — | — | — | `scaling.solution.divergence` | `correction.correction_divergence_free` |
| U5 | — | — | — | packet zero-past | `correction.potential.correction_cancels`,`potential_curl` (T16); `latticeLift_cancels` |
| U6 | — | — | — | `scaling.solution.momentum` | `correctionForce` residual identity + U5 |
| U7 | — | — | — | `scaling.velocity_singleCopy`,`place.eps_space` | `latticeLift_sliceSupport`; `correction_support_ball` |
| U8 | `torusLocalTheoryAPI.{velocity_unique,solution,regularity}`, `torusContinuationH3API.{higherOrderBound,extendsBeyond,lifespanInfiniteOfLocallyFinite}` | `boundedRepresentative` (H²↪L∞) | — | `scaling.unboundedSpeed`,`scaling.solution` | U5 (`u_ε=U_ε` on active support) |
| U9 | — | — | — | `scaling.packetEnergyIdentity`,`packetDissipationIdentity` | `correction.correction_energy_bound`,`energyConst` |
| U10 | — | — | — | `scaling.packetMixedScaling`,`mixed_memLp`; `Contracts.V1.alpha` | `correction.force_mixed_bound`,`force_spatial_memLp` |
| U11 | — | — | via `correction.localization` (T13) | `scaling.packetSobolevBound`,`forceConvergence`,`forceSobolev_memLp` | `correction.force_sobolev_bound`,`forceSobolev_memLp` |

## 3. Waves (≤ 3 concurrent per current lane cap)

| wave | units | sizes / models | status |
|---|---|---|---|
| W1 | **U1** triple+formulas · **U2** force class · **U3** kinematics | S sol / S-M sol / M sol | unblocked |
| W2 | **U4** divergence · **U5** cross-transport · **U7** localization support | S-M sol / M Opus / M sol | unblocked (T16/T11 DONE) |
| W3 | **U6** momentum · **U8** lifespan-exactly-`T` | M-L Opus / L Opus | U6→U8; H³-narrowed API + T12, no `PeriodicRestartH1` |
| W4 | **U9** energy rate\* · **U10** mixed rate\* · **U11** Sobolev rate\* | M / M-L / L Opus | \* gated (closeness bounds) |
| W5 | **U12** assembly + registration\* | M sol | \* non-vacuity gated |

`*` = the closeness units consume the **T15/T17 quantitative bound fields** (T15 U4/U5/U13/U14, T17 U9/U10/U11;
U11 additionally T13.localization). Their field *theorems* are provable now against the threaded
`scaling`/`correction` hypotheses; only U12's non-vacuity/`Nonempty` closure is truly gated (T15 U15 + T17 U12 +
T13 assembly). W1/W2 (the inserted triple, class memberships, kinematics, the two cross-transport identities
via T16 `correction_cancels`/`potential_curl`, and the localization support via the lattice lift) and W3
(lifespan, via T11 uniqueness + H³-narrowed continuation + H²↪L∞) are unblocked today. U5 is on the critical
path (U6 rewrites through it; U8 uses `u_ε=U_ε` from it). Lane numbers allocated by the lead in `PLAN.md`.

## 4. Risks

1. **U8 Sobolev datum path for `solution` (analytic long pole, mirrors R42 residual 1e-i).** The full-horizon
   `ClassicalSolutionT` needs a `t`-continuous `H^m` datum path for `u_ε` on `[0,T)`; the difference `w_ε+U_ε`
   is compactly supported, so a time cutoff + `contDiff_angularPath` + `reference.sobolev` gives it, but the
   cutoff/`Ico 0 S` bookkeeping is the M-residual R42 flagged (`LIFESPAN_SPLIT.md` #1). Must not weaken any
   other clause if it stalls.
2. **Closeness-rate non-vacuity (highest external).** U9/U10/U11 are gated on the T15/T17 bound lanes; U11 is
   transitively gated on **T13.localization** (via `correction.force_sobolev_bound` and
   `scaling.packetSobolevBound`). Stage, don't drop — register the field theorems, gate the non-vacuity, as
   T15/T17 did.
3. **T17 G1 (`SPEC_ISSUES.md`).** `CorrectionAPI` may gain `reference_smooth` at T17 assembly; T18 is forward-
   compatible (U1/U3 pick it up), but the *finalized* `CorrectionAPI` field set must be frozen before U12
   registers, or U12's bundle drifts.
4. **U5/U6 periodic cross-transport.** The cancellation is the periodic analogue of Theorem 4.2's whole-space
   step; the operand order and the directional-Fréchet `spatialDerivative` encoding (`RECONCILIATION.md` §1)
   must match `Spec.lean:1838-1852` exactly, and the `b_ε=0`-with-derivatives germ (not just pointwise) is what
   kills `(U_ε·∇)b_ε`.
