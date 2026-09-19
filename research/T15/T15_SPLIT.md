# T15 — proof-lane split (`prop:scaling`, `paper/sections/03-torus.tex:99-175`)

Lead-facing, 2026-09-18. Target = the reconciled `ScalingAPI` (21 fields) + `scalingStatement`
exactly as stated in `research/T15/Spec.lean:654-922`, over `PlacementData` (`Spec.lean:560-643`).
Design = `research/T15/RECONCILIATION.md` §3 + `COMPARISON.md` "Proof dependencies" (14 numbered
lemmas). House style = `research/T11/T11_SPLIT.md`. Size: **S** ≤ ~100 lines; **M** one
self-contained lemma with a known proof; **L** a multi-file campaign. Model: `codex-sol` =
reuse-heavy conversions/algebra/bookkeeping, `Opus` = analytic core.

## 0. Ground rules

**Peeling rule** (from T11). A unit that cannot close its target from the tree names **exactly one**
input hypothesis, as a `def … : Prop` in `Section3/T15/`, written out here, non-tautological,
satisfiable at a nonzero packet, and discharged by a named later unit. No named input for hard
analytic units. Every unit ends in a `theorem` whose statement **is** a `ScalingAPI`/`PlacementData`
field of `Spec.lean` verbatim (or a lemma directly consumed by one).

**Two classes of field.** Reconciliation §3 fixes what is *transport of the registered Euclidean
`I03.scaling` through the single-copy periodization* and what is a *genuinely new torus estimate*:

- **Pure transport** (reuse `Contracts/V1/Scaling.lean` + `Bindings/Scaling.lean` + `Section4/I03/*`,
  then one single-copy equality + one Haar↔Lebesgue bridge): `packetEnergyIdentity`,
  `packetDissipationIdentity`, `packetMixedScaling`, `unboundedSpeed`, the momentum/divergence half of
  `solution`, and the real-power-limit shape of `forceConvergence` (q=1).
- **Genuinely new torus** (no ℝ³ precedent): the three `*_summable` + three `*_singleCopy` (lattice
  theory), the Haar/Lebesgue & Parseval-0 bridges, all three MemLp-path fields, `force_mem`, the
  pressure normalization/gauge/integrability, the velocity `H^m` datum path + `pressure_gradient`, and
  `packetSobolevBound` (eq:packetHs via T13) which is **blocked on T13.localization** (lanes 354/359).

**Key reuse (lane 352 bridge).** `periodize` (`Section3/T13/Localization.lean:42`, per-slice spatial
sum over `PeriodicFrequency`) is `rfl`-equal (lane 352) to the space-slice of vendor
`NavierStokes/PeriodicLocalization.lean:62` `periodize`. That vendor file already proves the entire
lattice toolkit T15 needs: `periodize_locally_eq_sum:136` (locally a finite sum → summability +
single copy), `contDiff_periodize:155` / `contDiffOn_periodize:176` (smoothness), `periodize_add_lattice:192`
(unit periodicity). Every `*_summable`/`*_singleCopy`/smoothness obligation routes through these once
U1 lands the `rfl` bridge; do **not** reprove lattice finiteness from scratch.

**Missing T10 lemmas** (have no local precedent; each is its own small unit): the Haar-vs-Lebesgue
single-copy L² bridge and the Parseval-at-0 identity `periodicSobolevENorm 0 z = eLpNorm (torusLift z) 2 periodicTorusMeasure`
(U-TB1, U-TB2). `T10/Parseval.lean:116 parseval_forward` gives the datum form; U-TB2 only packages it
through `periodicSobolevENorm`. The gradient companion bridges `T13`'s `gradientENorm`
(`Localization.lean:86`) to `T10`'s `energyGradientT` (`Spec.lean:139`).

## 1. Units

- **U1 — rescaling & copied-decl `rfl` bridges.** New `Section3/T15/Bridges.lean`. Promote every
  `example … := rfl` of `Spec.lean:411-419,453-467,493-496,551-552` to `theorem`: `scaledVelocity =
  Contracts.V1.scaledPacket` / `scaledPressure = Contracts.V1.scaledPressure`
  (`Contracts/V1/Scaling.lean:107`) / `scaledForce = Contracts.V1.scaledForce` (`:115`),
  `alphaT = Contracts.V1.alpha` (`Data.lean`), `normalizedScaledPressure` formula, plus the **lane-352
  `rfl` bridge** `T13.periodize (slice) = (vendor periodize) space-slice`. **S, codex-sol.** Deps: —.

- **U2 — scaled-support placement** (needs-a-lemma ③). New `Section3/T15/Placement.lean`. For
  `ε ∈ Ioc 0 place.ε₀`: each spatial slice of `scaledVelocity`/`scaledPressure`/`scaledForce` is
  supported in `x₀ + ε • K_* ⊆ Metric.ball chartCenter chartRadius ⊆ interior fundamentalCube`
  (`place.eps_space`, `place.chartBall_in_cube`; `PacketAPI.carrier`, `force_support`,
  `Spec.PlacementData.Kstar_compact/carrier_subset/force_projection_subset`). Reuse `I03/Energy.lean:197
  scaled_slice_hasCompactSupport`, `:181 scaled_smoothOn` for the ℝ³ support shape. Ends in support
  lemmas consumed by U3–U8. **M, codex-sol.** Deps: U1.

- **U3 — lattice summability + single copy** (④). New `Section3/T15/SingleCopy.lean`. Targets the six
  fields `velocity_summable/pressure_summable/force_summable` (`Spec.lean:671,682,693`) and
  `velocity_singleCopy/pressure_singleCopy/force_singleCopy` (`:704,715,726`). Route: U2 puts each
  slice's support in `interior fundamentalCube`; then `periodize_locally_eq_sum` /
  `periodize_add_lattice` (vendor, via U1) — mirrored locally by `T13/ConstantEndpoints.lean:332
  periodize_eq_of_mem_cube`, `:308 eq_zero_of_mem_cube`, `:349 tsupport_subset_cube` — give
  summability and the `n=0` single copy on `Q`. **M, codex-sol.** Deps: U2.

  **Status (lane 421, 2026-09-18): complete.** `Section3/T15/SingleCopy.lean`
  proves all six canonical fields from the raw packet support clauses and
  `PlacementData`.  Strict cube support feeds the vendor locally finite
  translate theorem for summability; a value-generic version of the T13
  nonzero-translate argument gives the single copy for both vector fields and
  scalar pressure.  The probe fires all six results on the explicit nonzero
  bump placement at active time `t=7/8`.

- **U-TB1 — energy Haar/Lebesgue single-copy bridges** (missing T10; ⑩). New `Section3/T15/HaarBridge.lean`.
  `eLpNorm (torusLift (periodize f)) 2 periodicTorusMeasure = eLpNorm f 2 volume` for `f` supported in
  `interior fundamentalCube`, and the `gradientENorm`/`energyGradientT` companion. Route:
  `T13/ConstantEndpoints.lean:364 endpoint_zero_eq` (Lebesgue-on-cube = whole ℝ³) composed with
  `T13/TorusIdentity.lean:419 lintegral_fundamentalCube_ofReal`, `:402 fundamentalCube_ae_eq_halfOpenCube`,
  `:459 torusLift_torusPoint` (Haar-on-torus = Lebesgue-on-cube). **M, Opus.** Deps: —.

- **U-TB2 — Parseval-at-0 norm bridge** (missing T10). New `Section3/T15/ParsevalZero.lean`.
  `periodicSobolevENorm 0 z = eLpNorm (torusLift z) 2 periodicTorusMeasure` for smooth periodic `z`,
  by packaging `T10/Parseval.lean:116 parseval_forward` (`‖A‖ₑ = eLpNorm (torusLift z) 2 …` for the
  unique datum `A`) through `periodicSobolevENorm` (`T10/PeriodicData.lean:119`) and `datum_unique`.
  **S, codex-sol.** Deps: —.

  **Status (lane 363, 2026-09-18): complete.** `Section3/T15/ParsevalZero.lean` proves the stronger
  `IsPeriodicSpatial z ∧ MemLp (torusLift z) 2 periodicTorusMeasure` version via
  `parseval_backward`, the explicit `iInf` singleton collapse, `datum_unique`, and
  `parseval_forward`; the smooth theorem and `≠ ⊤` corollary follow. A constant nonzero mode is
  instantiated in `research/T15/probes/parseval_zero_closes.lean`.

- **U4 — energy identities + honest slices** (transport; ⑩). New `Section3/T15/Energy.lean`. Targets
  `energySlices_memLp` (`Spec.lean:793`), `packetEnergyIdentity` (`:804`), `packetDissipationIdentity`
  (`:815`). Route: U3 collapses each torus slice to the ℝ³ scaled slice on `Q`; `U-TB1` moves the Haar
  norm to `volume`; then `I03/Energy.lean:487 energyEssSup_scaled_eq` and `:304 energyGradient_scaled_eq`
  (equivalently `Bindings/Scaling.lean:658/667`) give `ε^{1/2}M`, `ε^{1/2}D`; `essSup`/`IsLUB` and
  endpoint-insensitive `Ioo` handled as in I03. `MemLp` slices from `I03/Energy.lean:211 eLpNorm_scaled_slice`.
  **L, Opus.** Deps: U3, U-TB1.

  **Status (lane 439, 2026-09-18): complete.** `Section3/T15/Energy.lean` proves all three
  canonical fields from the raw packet clauses and `PlacementData`.  The canonical torus chart
  always yields a representative in the *closed* fundamental cube, so `velocity_singleCopy` makes
  the Haar lift of the periodization *literally* the Haar lift of the rescaled slice; the velocity
  `MemLp` guard is then `T10.memLp_torusLift_vector`.  The gradient guard does need `periodize`
  smooth (the two gradients differ on the cube frontier) — supplied by the vendor [Lead correction after review 439: withdrawn — both gradients vanish at the frontier; the gradient guard comes from smoothness of the periodization, since the value-level single-copy identity is not a derivative statement.]
  `contDiff_periodize` through the lane-352 bridge.  The two identities are U-TB1's Goal 1 / Goal 2
  slicewise, then `I03.energyEssSup_scaled_eq` / `I03.energyGradient_scaled_eq`.  **No time-interval
  transport was needed**: both I03 lemmas are already over `Ioo 0 T`, literally T10's interval.

- **U5 — mixed scaling + honest paths** (transport; ⑪). New `Section3/T15/Mixed.lean`. Targets
  `mixed_memLp` (`Spec.lean:828`), `packetMixedScaling` (`:842`). Route: `force_singleCopy` (U3) + the
  `|Q|=1` Haar↔Lebesgue slice identity (U-TB1 style) reduce `mixedLebesgueENormT` to the whole-space
  `Data.mixedLebesgueENorm`; then `Bindings/Scaling.lean:318 mixedLebesgueENorm_scaledForce` gives
  `ε^{alpha p q}‖F‖`; torus/ℝ³ `MemLp` paths from `I03/Mixed.lean:104 mixedNorm_parabolicForce`,
  `:164 eLpNorm_slicePath_eq`. Covers `p=∞`/`q=∞` by `toReal ⊤ = 0` with no endpoint cases. **L, Opus.**
  Deps: U3, U-TB1.

  **Status (lane 439, 2026-09-18): complete.** `Section3/T15/Mixed.lean` proves both canonical
  fields.  The `|Q|=1` bridge is upgraded to **every** exponent by identifying the pushforward
  `Measure.map torusChart periodicTorusMeasure = volume.restrict fundamentalCube` and applying
  `eLpNorm_map_measure`, so `p=∞` needs no separate argument.  Both defining infima are shown
  *attained*: `mixedLebesgueENorm_eq` (formalization twin of `Bindings/Scaling.lean:296`, which
  `formalization/` cannot import) and its torus counterpart `mixedLebesgueENormT_eq`, whose
  admissible path is the Haar slice path — continuous because the torus is a probability space.
  `I03.positiveMixedNorm_parabolicForce` then supplies `ε^{alphaT p q}` directly.

- **U6 — unbounded speed** (transport; ⑨). New `Section3/T15/Blowup.lean`. Target `unboundedSpeed`
  (`Spec.lean:781`). Route: `Bindings/Scaling.lean:110 scaled_blowup` gives `SpeedUnboundedAt place.T`
  for the ℝ³ `scaledPacket`; U3 identifies it with `periodizedScaledVelocity` on `Q`; the blow-up
  witnesses `t ↑ T`, `x ∈ Q` (map source-time-1 witnesses into the cube) supply the periodic form.
  Needs `place.eps_time` for `ε^2 ≤ T`. **M, codex-sol.** Deps: U3.

  **Status (lane 442, 2026-09-19): complete.** `Section3/T15/Blowup.lean`
  proves the literal canonical field from the raw `SpeedUnboundedAtOne`,
  carrier compactness/support, and `PlacementData`.  The Euclidean rescaling
  supplies the witnesses; nonzero witness values lie in the placed cube, where
  U3's `velocity_singleCopy` transfers them to the periodized field.  The probe
  includes an explicit compact bump with `(1-t)⁻¹` amplitude.

- **U7 — `force_mem`** (new torus, easy). New `Section3/T15/ForceMem.lean`. Target `force_mem`
  (`Spec.lean:738`): `MemForceT (periodizedScaledForce …)` = smooth + unit-periodic + compact
  positive-time support. Route: `contDiff_periodize` (vendor, via U1) for smoothness,
  `periodize_add_lattice` for periodicity, U2's compact spatial support + the packet's positive-time
  force support (`T10/ForcePaths.lean:395 memForceT_time_smul` pattern) for the time-support witness.
  **M, codex-sol.** Deps: U2, U3.

  **Status (lane 442, 2026-09-19): complete.** `Section3/T15/ForceMem.lean`
  proves the literal canonical field from the raw global smoothness and
  `CompactPositiveTimeSupport` clauses plus `PlacementData`.  Vendor local
  finiteness gives smoothness, lattice reindexing gives periodicity, and the
  compact projection of the scaled force support supplies the positive-time
  support witness; periodization introduces no new support time.

- **U8 — periodized PDE transport** (transport core + ⑤⑦). New `Section3/T15/Equation.lean`. Proves the
  momentum (at the **unchanged** `ν`), divergence-free, and zero-initial obligations of `solution`
  **for the periodized fields**. Route: `Bindings/Scaling.lean:88 scaled_equation`, `:100
  scaled_divergence_free`, `:58 navierStokesResidual_eq`, `:79 source_time_lt_one` give the ℝ³
  identities; U3's single copy on `Q` + periodicity (periodization commutes with every derivative in
  `navierStokesResidual`, incl. the nonlinear term, via `contDiffOn_periodize` and locally-finite-sum
  differentiation) transport them to the torus fields. **L, Opus.** Deps: U3.

- **U9 — velocity `H^m` datum path + `pressure_gradient`** (new; ⑧). New `Section3/T15/SobolevPath.lean`.
  Proves `ClassicalSolutionT.sobolev` (a `ContinuousOn` `PeriodicSobolev m` datum path for every `m : ℕ`)
  and `pressure_gradient` (`MemLp` of the torus pressure gradient) for the periodized velocity/pressure.
  Route: the periodized velocity slice is smooth periodic (U7-style); reuse `T10/ForcePaths.lean:82
  continuous_datum_path` and `T10/DatumBasics.lean:129 datum_unique` at each `m`, with continuity in `t`
  from the packet's joint smoothness. **L, Opus.** Deps: U3.

- **U10 — pressure normalization** (new; ⑥). New `Section3/T15/Pressure.lean`. Targets
  `pressureSlice_integrable` (`Spec.lean:766`) and the gauge `PressureGaugeT` used inside `solution`.
  Route: U3 collapses the raw pressure to its single copy, smooth compactly supported on `Q`, hence
  Haar-integrable; `normalizedScaledPressure = normalizePressureT (…)` (`rfl`, U1) subtracts the mean,
  so `∫_{T³} = 0` follows from `T13/TorusIdentity.lean:419 lintegral_fundamentalCube_ofReal`. The
  gradient/residual are unchanged by a spatially constant shift. **M, Opus.** Deps: U3.

- **U11 — `solution` assembly.** New `Section3/T15/Solution.lean`. Target `solution` (`Spec.lean:753`):
  build one `ClassicalSolutionT ν 0 F_ε place.T` from U8 (momentum/div/initial), U9 (sobolev/pressure_gradient),
  U10 (gauge), U7 (regularity/periodicity), with the two pinning equations `S.velocity = U_ε^per`,
  `S.pressure = p_ε` by `rfl`. **M, codex-sol.** Deps: U7, U8, U9, U10.

- **U12 — `forceSobolev_memLp` + `sobolevConst`/`sobolevConst_pos`** (new; ⑬). New
  `Section3/T15/SobolevBoundMem.lean`. Targets `forceSobolev_memLp` (`Spec.lean:872`), the data field
  `sobolevConst` (`:855`) and `sobolevConst_pos` (`:862`). Route: honest `L¹_tH^s(T³)` datum path from
  U9's per-`m` construction restricted to `s ∈ [0,1]`; `sobolevConst` defined as the (positive)
  constant assembled in U13 from T13's localization constant × the Euclidean rate. **L, Opus.** Deps: U3, U9.

- **U13 — `packetSobolevBound` (eq:packetHs)** (⑫; **BLOCKED on T13.localization**). New
  `Section3/T15/SobolevBound.lean`. Target `packetSobolevBound` (`Spec.lean:884`). Route:
  time-integrated localization — apply the structure's `localization : LocalizationAPI` field
  (`T13/…`: `wholeSpace_identity`, `torus_identity:1174`, `endpoint_zero:407`, `endpoint_one:416`, and
  the `localization` sub-field) slice by slice with one `ε`-independent constant, combine the Euclidean
  homogeneous scaling `ε^{-3/2-s}` (`I03/HomogeneousScaling.lean:237 homogeneous_vector_datum_scaling`,
  `:330 homogeneous_datum_time_scaling`) with the `ε²` time change to reach `C_s(ε^{1/2}+ε^{1/2-s})`.
  Endpoint interpolation from `Paper1/PeriodicScalingBounds.lean:19,40`; endpoint rates from
  `Paper1/PeriodicPacketEndpointRates.lean:22,49,76,103`. **Named input:** none at the theorem level (the
  `LocalizationAPI` is a *structure field*), but the `.localization` sub-field of that witness is what
  lanes 354/359 are still proving, so this unit is **exercisable/testable only once T13.localization
  lands**; keep it as a separate lane and gate its non-vacuity on 354/359. **L, Opus.** Deps: U12; **T13.localization**.

- **U14 — `forceConvergence`** (⑭; **partly blocked on T13.localization**). New
  `Section3/T15/Convergence.lean`. Target `forceConvergence` (`Spec.lean:903`),
  `q∈{1,2}`, `s < criticalOrder q.toReal` (`Data.lean:259`). Route: for `q=1, 0≤s<1/2` feed U13's bound
  into the real-power limit `Paper1/ScalingLimits.lean:11 sobolev_error_tendsto_zero`; for `s<0`
  negative-order monotonicity `forceSobolevENormT 1 s f ≤ forceSobolevENormT 1 0 f` under the amended
  datum; the `q=2` branch (`criticalOrder 2 = -1/2`, all `s<-1/2`) by the same monotonicity from the
  `s=0` mixed base (U5). The `s∈[0,1/2)` sub-range inherits U13's **T13.localization** dependency; the
  `s<0` sub-range is independent. **L, Opus.** Deps: U12, U13.

- **U15 — non-vacuity + assembly + registration** (②; assembly Nonempty **blocked on T13.localization**).
  New `Section3/T15/Assembly.lean` + `Contracts/V1/Scaling*`?→ a fresh `Contracts/V1/…` for T15
  (`T02.scaling`) + `Bindings` + `Tests`. Constructs a `PlacementData` witness for the non-vacuity
  example: compact `K_* ⊇ P.carrier ∪ pr_x (tsupport P.force)` (`PacketAPI.force_support` gives
  `HasCompactSupport`, so the projection is compact) and a chart ball with `closure ⊆ interior fundamentalCube`;
  then bundles all 21 fields into `ScalingAPI` and closes `scalingStatement` (`Spec.lean:919`,
  `Nonempty (ScalingAPI (𝔉.select ν hν) place)`). The `localization` field needs a **real** T13
  `LocalizationAPI` inhabitant, so the `Nonempty` assembly is **gated on lanes 354/359**; until then
  register everything except `localization`/`packetSobolevBound`/`forceConvergence[s≥0]` and keep the
  gated fields staged. **M, codex-sol.** Deps: all; **T13.localization**.

## 2. Waves (≤ 3 concurrent per current lane cap)

| wave | units | sizes / models |
|---|---|---|
| W1 | **U1** bridges · **U-TB1** Haar bridge · **U-TB2** Parseval-0 | S sol / M Opus / S sol |
| W2 | **U2** placement → **U3** single-copy+summability | M sol / M sol (serial pair) |
| W3 | **U4** energy · **U5** mixed · **U6** unbounded · **U7** force_mem | L Opus / L Opus / M sol / M sol |
| W4 | **U8** PDE transport · **U9** velocity Sobolev path · **U10** pressure · **U11** solution | L Opus / L Opus / M Opus / M sol |
| W5 | **U12** forceSobolev-memLp · **U13** packetSobolevBound* · **U14** forceConvergence* · **U15** assembly* | L Opus / L Opus / L Opus / M sol |

`*` = consumes **T13.localization** (lanes 354/359); start the lane against the structure's
`localization` field, but its non-vacuity/assembly is gated until T13.localization lands. U3 is on the
critical path: U4–U11 all wait on it, so W2 must finish before W3 opens. Lane numbers allocated by the
lead in `PLAN.md`.

## 3. Risks

1. **T13.localization (highest).** `packetSobolevBound`, the `s≥0` half of `forceConvergence`, and the
   `Nonempty` assembly cannot be *exercised* until lanes 354/359 register a `LocalizationAPI` inhabitant.
   The field *theorems* are provable now (the witness is a structure hypothesis); only the end-to-end
   `scalingStatement` and non-vacuity tests are gated. Do not silently drop the field — stage it.
2. **`ClassicalSolutionT.sobolev` (U9).** The velocity `H^m` datum path for *every* `m : ℕ` with `t`-continuity
   is the analytic long pole flagged in RECONCILIATION §2's PDE-clause ruling; if it stalls, it is the
   only obstruction to `solution` and must not force a weakening of the other 20 fields.
3. **Nonlinear-term periodization (U8).** Periodization must commute with the convective derivative
   across cell boundaries; rely on `contDiffOn_periodize` + local finite-sum differentiation, not termwise
   `tsum` differentiation.

## U1 status — lane 362 (`362-T15-U1-bridges`)

**Complete.** `formalization/NSFormalization/Section3/T15/Bridges.lean` now
contains the canonical T15 rescaling definitions and the `rfl` bridges to the
upstream parabolic rescalings, the normalized-pressure formula, both completed-
density spellings, and the lane-352 T13/vendor periodizer equality.  The
contract-side conformance probe is
`research/T15/probes/api_on_canonical.lean`; its packet-specific definitions
are token-for-token copies of the Spec definitions and all close by `rfl`.
The axiom audit is `research/T15/axioms_u1.lean`.

## U-CAN status — lane 384 (`384-T15-UCAN-canonical-scaling`)

**Complete.** `formalization/NSFormalization/Section3/T15/Scaling.lean`
restates the reconciled T15 interface over raw packet fields: the 17-field
`PlacementData`, the complete 21-field `ScalingAPI`, and `scalingStatement`
with all 26 `PacketAPI` clauses and both `PacketEnergyAPI` clauses explicit.
It imports no `Contracts.*` module and uses lane 362's canonical rescaling
definitions together with T13's canonical `LocalizationAPI`.

The structure-exception probe is
`research/T15/probes/scaling_canonical.lean`: it copies the two Spec
structures, proves all ten rescaling-definition bridges by `rfl`, and gives
fieldwise conversions with round trips for both structures.  The raw/contract
mapping is recorded in `research/T15/ATTEMPTS_UCAN.md`; the axiom audit is
`research/T15/axioms_ucan.lean`.

No U2--U15 analytic field is claimed here; those are the remaining gaps listed
above and in §1.
## 4. Status log

- **U-TB1 — DONE (lane 364, 2026-09-18).** `formalization/NSFormalization/Section3/T15/HaarBridge.lean`
  (namespace `NSFormalization.Section3.T15`, builds clean, all decls
  `[propext, Classical.choice, Quot.sound]`). Shipped:
  - `eLpNorm_torusLift_restrict g` — the **measure-free** Haar/Lebesgue change of variables
    `eLpNorm (torusLift g) 2 periodicTorusMeasure = eLpNorm g 2 (volume.restrict fundamentalCube)`
    for *any* `g : Space → F` (no regularity, no measurability). Core reused by every downstream field.
  - `eLpNorm_torusLift_periodize f _hf hsupp` (Goal 1) — needs only
    `tsupport f ⊆ interior fundamentalCube` (smoothness unused, kept for interface parity).
  - `eLpNorm_torusLift_spatialGradient_periodize f hf t hsupp` (Goal 2) — the gradient companion,
    identifying `eLpNorm (torusLift (fun x ↦ spatialGradient (fun p ↦ periodize f p.2) t x)) 2 periodicTorusMeasure`
    with `T13.gradientENorm f volume`. `periodize f`'s regularity is **not** needed (the bridge is
    measure-free; its gradient is replaced a.e.-on-cube by `f`'s, differing only on the null frontier). [Lead correction after review 439: withdrawn — both gradients vanish at the frontier; the gradient guard comes from smoothness of the periodization, since the value-level single-copy identity is not a derivative statement.]
  - `eLpNorm_torusLift_periodize_slice F t hf hsupp` (Goal 3) — per-slice corollary for `energyEssSupT`.
  - Helpers `lintegral_enorm_torusLift`, `eLpNorm_gradientVector_eq_gradientENorm` (the
    `energyGradientT`-vs-`gradientENorm` identity), `gradientENorm_restrict_eq`, and interior-hypothesis
    single-copy lemmas `periodize_eq_of_mem_interior` / `periodize_eventuallyEq_interior` (generalising
    the ball-hypothesis `T13.eq_zero_of_mem_cube` / `periodize_eventuallyEq`).
  Non-vacuity: `research/T15/probes/haar_bridge_closes.lean` instantiates all three at the lane-344
  `ContDiffBump` packet. Audit: `research/T15/axioms_utb1.lean`.
  Note for U4/U5 consumers: the hypothesis is `interior fundamentalCube`, strictly weaker than the
  `place.chartBall_in_cube` ball form, so a ball placement discharges it via
  `hsupp.trans (subset_closure.trans hball)`.

### U2 status (lane 376)

**Complete (r2, 2026-09-18).** `formalization/NSFormalization/Section3/T15/Placement.lean`
(namespace `NSFormalization.Section3.T15`, builds clean, all 16 decls
`[propext, Classical.choice, Quot.sound]`).  r0 goal-aliases and r1 (narrow time
domain + dead force binder) were both rejected
(`REVIEW_376-T15-U2-placement.md`); r2 is genuine transport from the raw
`PacketAPI` clauses over the U3 time domains.  Shipped:

- `scaledVelocity_tsupp_subset` / `scaledPressure_tsupp_subset` — for `0 < ε`,
  **every `t < T`**, slice support `⊆ (fun y ↦ x₀+ε•y) '' Kstar`, from
  `velocity_support`/`pressure_support` (`Ico 0 1`), `carrier_compact`,
  `carrier_subset`.  Split at activation `t_ε = T-ε²`: pre-activation zero slice
  (`scaled*_slice_eq_zero` via `zeroPast_dilate_early`), active window via
  `parabolic_support`/`dilate_support` + `inv_inv` + `Set.image_mono`.  Domain
  matches `velocity_singleCopy`/`pressure_singleCopy` (`Spec.lean:704-718`).
- `scaledForce_tsupp_subset` — for **every** `t`, from the verbatim packet clause
  `CompactPositiveTimeSupport f` used through `parabolicForce_support hf.1`, and
  `force_projection_subset`.  Domain matches `force_singleCopy` (`Spec.lean:726-731`).
- `scaledVelocity_slice_eq_zero`/`scaledPressure_slice_eq_zero`,
  `tsupport_subset_of_slice_zero`; `affineImage_compact`,
  `affineImage_subset_ball` (`eps_space`), `ball_subset_interior_cube`
  (`chartBall_in_cube`), composed `scaled{Velocity,Pressure,Force}_slice_subset_cube`
  (strict `interior fundamentalCube`, U3 / `HaarBridge.eLpNorm_torusLift_periodize`);
  `scaled{Velocity,Pressure,Force}_slice_hasCompactSupport`.

Non-vacuity: `research/T15/probes/placement_closes.lean` (explicit geometric
instance — bump packet, cube-centre `x₀`, chart ball `3/8`, `ε₀=1` — firing the
cube/compact-support lemmas at the active `t = 7/8` with a nonzero slice),
reviewer probes `rev376_honest_nonvacuity.lean` / `rev376_contract_shape.lean` /
`rev376_nonvacuity.lean`, mutation guard `rev376_negative.lean`, audit
`axioms_u2.lean`.  A `PlacementData` inhabitant for the abstract `Bindings.packet`
is U15 (gated on T13.localization).  Consumers U3, U7 take the
`*_slice_subset_cube` / `*_slice_hasCompactSupport` lemmas.

### U4 / U5 status (lane 439)

**Complete (2026-09-18).** `formalization/NSFormalization/Section3/T15/Energy.lean` (8 decls)
and `formalization/NSFormalization/Section3/T15/Mixed.lean` (21 decls); both build clean and
every declaration prints `[propext, Classical.choice, Quot.sound]`
(`research/T15/axioms_u4_u5.lean`).  No `set_option maxHeartbeats` in either module.

Shipped, U4 (`Energy.lean`):

- `energySlices_memLp hext hK hu place`, `packetEnergyIdentity hP hu place`,
  `packetDissipationIdentity hP hu place` — the three canonical field types verbatim.
  `hP : NSFormalization.Section4.I03.PacketData u K M D` is the Section 4 bundle of the eight
  verbatim `scalingStatement` packet clauses (probe Part 1b builds it from them).
- Helpers: `torusChart_mem_fundamentalCube`, `torusLift_congr_cube` (chart ⊆ closed cube ⇒
  agreeing-on-cube fields have equal lifts), `contDiff_periodize_of_subset_interior` (vendor
  `contDiff_periodize` via the lane-352 `rfl` bridge), `memLp_torusLift_gradientVector`
  (`MemLp.of_eval_piLp` on `WithLp 2 (Fin 3 → Space)`), `scaledVelocity_slice_contDiff`.

Shipped, U5 (`Mixed.lean`):

- `mixed_memLp hf hfc place`, `packetMixedScaling hf hfc place` — the two canonical field types
  verbatim, for **all** `1 ≤ p, q ≤ ∞`.
- §1 exponent-generic Haar/Lebesgue: `torusChart`, `measurable_torusChart`, `torusChart_coe`,
  `lintegral_comp_torusChart`, `map_torusChart`, `eLpNorm_torusLift_eq_restrict`,
  `eLpNorm_torusLift_eq_volume`.
- §2 `mixedLebesgueENorm_eq` (whole-space infimum attained at `I03.positiveMixedNorm`).
- §3 `torusSlicePath`, `enorm_torusSlicePath`, `continuous_torusSlicePath`, `continuous_slice`.
- §4 `mixedLebesgueENormT_eq` (torus infimum attained).
- §5 `scaledForce_contDiff`, `scaledForce_hasCompactSupport`, `scaledForce_slice_tsupport_cube`,
  `torusLift_periodizedScaledForce`, `mixedLebesgueENormT_periodizedScaledForce`.

Non-vacuity: `research/T15/probes/energy_mixed_closes.lean` — Part 1 closes all five canonical
field types by a bare `exact`; Part 1b rebuilds `I03.PacketData` from `scalingStatement` clauses;
Part 2 fires all five on the `placement_closes.lean` geometry (cube centre, spatial bump radius
`1/4`, chart ball `3/8`, `T = 1`, `ε₀ = 1/2`, `ε = 1/2`) with a **nonzero** time-localized packet
(time bump supported in `[1/4,3/4] ⊆ (0,∞)`), a complete `PlacementData` and a complete
`I03.PacketData` with `M = √∫‖U₀‖² > 0`.  Dead ends: `research/T15/ATTEMPTS_U4_U5.md`.
