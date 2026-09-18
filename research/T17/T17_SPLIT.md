# T17 — proof-lane split (`lem:correction`, `paper/sections/03-torus.tex:218-286`)

**U-CAN status (lane 394, DONE 2026-09-18).**
`Section3/T17/Correction.lean` now restates the full 45-field `CorrectionAPI`
over T15 U-CAN's raw-field `PlacementData u p f K`, canonical T16/T13 records,
and the bare `place.x₀`/`place.T` profile spelling required by T18 U1.  The
contract-side probe supplies fieldwise conversions in both directions through
lane 384's placement adapter and exact checks against U3/U4/U5/U6.  The Spec
field list remains unchanged (no `reference_smooth`); G1 is still an assembly
hypothesis/truncation decision.  Because lane 375 was absent from this base,
its canonical `ForceProfile.lean` source was restored as a new file here.

Lead-facing, 2026-09-18. Target = the reconciled `CorrectionAPI` (Spec.lean:752-960, 45 fields) +
`correctionStatement` (`Spec.lean:980`) over T15's `PlacementData`, T16's `CutoffData`/`LocalPotentialAPI`,
and T13's `LocalizationAPI`. Design = `research/T17/RECONCILIATION.md` §3 + `COMPARISON.md` "Proof
dependencies" (8 numbered items). House style = `research/T11/T11_SPLIT.md`, `research/T15/T15_SPLIT.md`.
Size: **S** ≤ ~100 lines; **M** one self-contained lemma with a known proof; **L** a multi-file campaign.
Model: `codex-sol` = reuse-heavy transport/algebra/bookkeeping, `Opus` = analytic core.

## 0. Ground rules

**Peeling rule** (from T11/T15). A unit that cannot close its target from the tree names **exactly one**
input hypothesis, as a `def … : Prop` in `Section3/T17/`, written out here, non-tautological, satisfiable
at a nonzero reference, and discharged by a named later unit. No named input for hard analytic units.
Every unit ends in a `theorem` whose statement **is** a `CorrectionAPI` field of `Spec.lean` verbatim, or a
lemma **directly consumed** by one. (Most quantitative fields are stated over the abstract `D : CutoffData`;
their proofs are lemmas about the concrete correction `latticeLift (physicalCorrection …)` that the assembly
unit U12 maps onto `D.correction`, exactly as T16's `localPotential` bundled `LocalPotentialAPI` against its
concrete witness. So most units land the concrete-correction lemma.)

**The single structural fact.** The T16-constructed correction is (`Assembly.lean:414-461`, worktree 358,
definitionally in the `localPotential` witness)

```
D.correction ε  =  latticeLift (physicalCorrection v place.x₀ place.T D.θ D.η ε)
```

where `physicalCorrection = NSFormalization.Paper1.CorrectionProfile.physicalCorrection` is **the same single
Euclidean copy** on which Section 4's registered `I02.CorrectionAPI` is built. Therefore **every quantitative
field of T17 is either (i) reuse of a Paper1/I02 estimate about `physicalCorrection` / its force
`Source.correctionForce ν v (physicalCorrection …)` (`Source/Insertion.lean:92`), transported through the
lattice lift, or (ii) an identification of a torus (Haar) norm/measure with the whole-space (Lebesgue) norm
of the single copy on the fundamental cube.** Two genuinely-missing bridges (U1, U2) carry (i); the Haar↔Lebesgue
bridges of (ii) come from T15's in-flight `Section3/T15/{HaarBridge,ParsevalZero,Mixed}.lean` (lanes 363/364).

**Three classes of field** (per RECONCILIATION §3; the task's transport-vs-new split):

- **Euclidean profile reuse** (no periodization; reuse `Paper1/CorrectionProfile.lean`,
  `CorrectionForceProfile.lean` after one T17-profile↔Paper1-profile `def` bridge): `correction_profile_*`,
  `correction_profile_identity`, `force_profile_*`, `force_profile_identity` (U3, U4).
- **Pure transport of registered `I02` Euclidean bounds through the single-copy lattice lift** (reuse the
  registered bound verbatim, add only U1/U2 + T16's `latticeLift_*`): both halves of `eq:derivativebounds`
  (`correction_derivative_bound`, `force_derivative_bound` — U5, U6), `force_smooth`/`force_periodic`/
  `force_support` (U7), and the `≤ Cε^k` **content** of `force_spatial_volume`/`force_time_length` (U8),
  `correction_energy_bound` (U9), `force_mixed_bound` (U10).
- **Genuinely new torus estimates** (no ℝ³ precedent; the Haar/Lebesgue single-copy identification is the new
  work): the norm/measure identifications wrapping U8/U9/U10, and **all of `eq:HHs`** (U11) which has no `I02`
  counterpart and routes through T13's `localization` — **blocked on T13.localization (lanes 354/359)**.

**T13 gate.** `eq:HHs` (`force_sobolev_bound`, `forceSobolev_memLp`, `sobolevConst`, `sobolevConst_pos`) and
the `localization` field consume T13's `LocalizationAPI.localization` sub-field, still being proved by lanes
354/359 (→ 359 assembly needs the Parseval-at-0 bridge, lane 363). The field *theorems* are provable now (the
`LocalizationAPI` is a structure hypothesis), but their non-vacuity and the `Nonempty` closure are gated. Split
these off (U11) and stage them, exactly as T15 staged `packetSobolevBound`. Do not silently drop the field.

**External dependency (T15 bridges).** U8/U9/U10 reuse T15's single-copy Haar↔Lebesgue identities:
`Section3/T15/HaarBridge.lean` (energy L², U-TB1), `ParsevalZero.lean` (U-TB2), `Mixed.lean` (mixed L^p).
Not yet in the tree (lanes 363/364). Start the U9/U10/U8 lanes against these as named imports; their
non-vacuity waits on 363/364. The whole-space (Lebesgue) halves (`I02.Energy`, `I02.Mixed`, `Paper1`) are
in the tree today.

## 1. Units

- **U1 — lattice-lift iterated-derivative bridge** (missing bridge). New `Section3/T17/LatticeDeriv.lean`.
  Target: `latticeLift_iteratedFDeriv_eq` — for `w` with each spatial slice supported in `ball x₀ ρ`,
  `ρ + ρ' ≤ 1`, and every `z` and order `n`,
  `‖iteratedFDeriv ℝ n (latticeLift w) z u‖ = ‖iteratedFDeriv ℝ n w (z - (0, latticeVector k)) u‖` for the one
  nearby copy (`k = 0` when `z.2 ∈ cube`). Route: `latticeLift` is locally a single translate on the disjoint
  periodic ball family (T16 `LatticeLift.latticeLift_eq_of_ball:135`, `latticeLift_sliceSupport:271`), so
  `latticeLift w =ᶠ[𝓝 z] (· - shift) ∘ w`; conclude with `Filter.EventuallyEq.iteratedFDeriv_eq`.
  **S–M, codex-sol.** Deps: — (T16).

- **U2 — concrete data + force-operator transport** (missing bridge). New `Section3/T17/Transport.lean`.
  (a) `def correctionData … : CutoffData` re-running T16 `Assembly.localPotential:414` so
  `(correctionData …).correction ε = latticeLift (physicalCorrection v place.x₀ place.T θ η ε)` by `rfl`;
  (b) `force_eq : correctionForce ν v (correctionData …) ε = latticeLift (Source.correctionForce ν v
  (physicalCorrection …))`, using `reference_periodic` (`IsPeriodicOn univ v`) and locality of each operator
  (`temporalDerivative`, `spatialLaplacian`, `spatialDerivative`, `advection`) — the T17 spelling reorders the
  two middle summands, matched by `add_comm`. Reuse T16 `LatticeLift.spatialDivergence_translate:176`,
  `isPeriodicOn_sub_latticeVector:327`. **M, Opus.** Deps: — (T16).
  **Status (lane 373, DONE):** `Section3/T17/Transport.lean` closed with 0 `sorry`/`axiom`, all decls
  `[propext, Classical.choice, Quot.sound]`. `correctionData := localPotentialData v x₀ T θ η O θR ε₀` (plain
  `x₀ T` args, no `PlacementData` — lane 362 not yet in tree; the `place` form is a projection corollary once it
  lands); `correctionData_correction` by `rfl`. `correctionForce` copied verbatim from `Spec.lean:726-733`;
  `correctionForce_eq_source` bridges to `Source.correctionForce` by `abel` (the two middle summands swap).
  `force_eq` proved **pointwise, by cases on `x ∈ periodicSet (ball x₀ r)`** (not a finite-sum expansion): the
  active-copy germ is a *single* translate (via `latticeLift_eq_of_ball` + `latticeLift_periodic`), so the
  nonlinear advection term never produces cross copies; outside the periodic support both sides vanish
  (`latticeLift_sliceSupport` + a new `source_correctionForce_support`). New reusable equivariance lemmas
  `temporalDerivative_translate`/`spatialDerivative_translate`/`spatialLaplacian_translate`/`advection_translate`
  and germ-congruence `source_correctionForce_congr` (all downstream of U5/U6 will reuse these). Hypotheses are
  the honest T16 ones (`hv : IsPeriodicOn univ v`, `hvsm : ContDiffOn v cylinder`, θ/η smoothness+support,
  `ε*θR < r < 1/2`, `2ε² < min T δ`) — no named `Prop` input. `correctionForce_periodic` (part c) via
  `latticeLift_periodic`.

- **U3 — correction profile fields + identity** (Euclidean reuse). New `Section3/T17/CorrectionProfile.lean`.
  Targets `correction_profile_smooth`, `correction_profile_support`, `correctionProfileConst`,
  `correctionProfileConst_nonneg`, `correction_profile_uniform`, `correction_profile_identity`
  (`Spec.lean:784-830`). Route: prove the `def` bridge `rescaledCorrectionProfile v place ε D z =
  CorrectionProfile.profile v place.x₀ place.T D.θ D.η (ε, z)` — unfold `rescaledPotential` (the literal
  display `∫₀¹ρ v(…)×z`) against `jointPotential`/`cutPotential` (`RECONCILIATION §4 ①`; the potential is the
  radial display, `LocalPotentialAPI.potential_formula` / `centeredPotential_eq_integral`); then Paper1
  `profile_smooth:49`, `profile_support:187`, `profile_uniform_global_derivative_bound:201`,
  `physicalCorrection_eq_profile:223` (identity via `inverseScale`, matching `correctionChartPoint`).
  `fixedProfileCylinder D = Icc(-2,2)×closedBall 0 D.θRadius` contains `tsupport(profile)` by
  T16 `eta_support`/`theta_support`. **L, Opus.** Deps: —.
  **STATUS 2026-09-18 (lane 370, DONE, module builds / axioms clean).** All six fields proved in
  `formalization/NSFormalization/Section3/T17/CorrectionProfile.lean` (`correction_profile_smooth`,
  `correction_profile_support`, `correctionProfileConst` (def) + `_nonneg`, `correction_profile_uniform`,
  `correction_profile_identity`), each `[propext, Classical.choice, Quot.sound]`. Bridge
  `rescaledCorrectionProfile_eq_profile` is `rfl` (the display `𝒜_ε` = Paper1 `jointPotential`) + one
  curl-slice fderiv lemma; identity via `LocalPotentialAPI.correction_formula`/`potential_formula` →
  `physicalCorrection` → `physicalCorrection_rescale`. **REV after codex REJECT (2026-09-18):** merged
  `origin/erenup/integration-section3` (brings `Section3/T16/Assembly.lean` #330); probe now builds a real
  `LocalPotentialAPI` via `localPotential` on a nonzero constant divergence-free periodic reference and
  **instantiates `correction_profile_identity`** (`nonvacuous_correction_profile_identity`) — periodicity/
  divergence-freeness proved, not commented. **One residual for U12/spec** (G1, logged in
  `research/T17/SPEC_ISSUES.md`): the fields need **global** `hv : ContDiff ℝ ∞ v` (Paper1 `profile_*`),
  which `CorrectionAPI` does not expose (`reference_periodic` only, no `reference_smooth`) — the assembly
  must add that field or truncate v à la T16 `BallPotential`; the six theorem docstrings mark `hv` as an
  added premise. G3 (lead ruling): placement bundling stays bare `x₀ : Space`, `T : ℝ` (canonical T16;
  `PlacementData`/`PacketAPI` live in `verification/`, unreachable from `formalization/`); assembly
  instantiates `place.x₀`/`place.T`.

- **U4 — force profile fields + identity** (Euclidean reuse). New `Section3/T17/ForceProfile.lean`.
  Targets `force_profile_smooth`, `force_profile_support`, `forceProfileConst`, `forceProfileConst_nonneg`,
  `force_profile_uniform`, `force_profile_identity` (`Spec.lean:805-837`). Route: `def` bridge
  `rescaledForceProfile ν v place ε D z = CorrectionForceProfile.forceProfile ν v place.x₀ place.T D.θ D.η
  (ε, z)` (shares U3's potential bridge); then Paper1 `forceProfile_smooth:57`, `forceProfile_support:75`,
  `forceProfile_uniform_derivative_bound:204`, and **`physicalForce_eq_profile:185`** which is exactly
  `Source.correctionForce … p = (ε²)⁻¹ • forceProfile ν … (ε, inverseScale ε (p-(T,x₀)))` — the affine
  `ε⁻²` rescaling of `force_profile_identity` under `correctionChartPoint` (`RECONCILIATION §4 ②`). **L, Opus.**
  Deps: U3.
  **STATUS 2026-09-18 (lane 375; rev1 after merge closes all six fields incl. Spec-form identity; module builds / axioms clean).**
  `formalization/NSFormalization/Section3/T17/ForceProfile.lean`: `force_profile_smooth`,
  `force_profile_support`, `forceProfileConst` (def) + `_nonneg`, `force_profile_uniform` proved **verbatim**
  (each `[propext, Classical.choice, Quot.sound]`). The `def` bridge `rescaledForceProfile_eq_forceProfile`
  needed **one chain-rule step** (not `rfl`): the Spec's `ε²•∂ₓv(physical)·W` term vs Paper1's
  `ε•∂ₓV_ε·W` term, reconciled by `spatialDerivative_rescaledReference` (`∂ₓV_ε = ε•∂ₓv(physical)`) +
  `smul_add`/`abel` over `forceProfile_eq_operators`. Identity: `force_profile_identity` proved for the
  **chart force** `Source.correctionForce ν v (physicalCorrection …) (chart) = (ε²)⁻¹ • rescaledForceProfile …`
  (`physicalForce_eq_rescaledForceProfile`, via `physicalForce_eq_profile:185` +
  `inverseScale_correctionChartPoint`). **Three residuals** (see `research/T17/ATTEMPTS_U4.md`): (G0) the lift
  from the chart force to the Spec's `correctionForce ν v D ε` (over `D.correction`) — `force_eq_chart` =
  operator `add_comm` + field agreement on `univ ×ˢ ball x₀ r`; this is U2/lane 373's `force_eq` restricted to
  the chart, **not on this base** (no `Transport.lean` yet), left to U12; (G1) global `hv` premise (same as U3,
  no `reference_smooth` field); (G3) bare `x₀,T` placement.
  **REV1 2026-09-18 (post-review merge with `origin/erenup/integration-section3`).** G0 **resolved**: with lane
  373's `Transport.lean` now on the base, `ForceProfile.lean` imports it, drops its own `correctionForce` (name
  clash), and adds `force_eq_chart` (= `correctionForce_eq_source` reorder + `source_correctionForce_congr`
  locality + lane 370 `correction_eq_physicalCorrection` on `univ ×ˢ ball x₀ r`) then the **Spec-form**
  `force_profile_identity` (over `correctionForce ν v D ε`), `[propext, Classical.choice, Quot.sound]`. The
  chart-force lemma `physicalForce_eq_rescaledForceProfile` is kept. Remaining: Spec-form identity **non-vacuity**
  needs a concrete `LocalPotentialAPI` inhabitant (T16 `localPotential`), staged for U12; G1/G3 unchanged.
  `check_contracts --base-ref origin/erenup/integration-section3` now exits 0 (base compatible).

- **U5 — `correction_derivative_bound`** (pure transport). New `Section3/T17/CorrectionDeriv.lean`. Target
  `correction_derivative_bound` (`Spec.lean:878`) verbatim on the concrete correction. Route: U2(a) rewrites
  `D.correction ε` to `latticeLift (physicalCorrection …)`; U1 moves the iterated derivative to the single copy;
  Paper1 `physical_mixed_derivative_bound:291` (`|∂ₜʲ∂ₓᵝ physicalCorrection| ≤ C(ε⁻¹)^{2j+m}` on `Ioc 0 1`)
  closes it; `D.ε₀ ≤ 1` from `eps_le_placement` + `place.eps_le_one`. **M, codex-sol.** Deps: U1, U2.
  **Status (lane 385, DONE):** `CorrectionDeriv.lean` defines the Paper1-selected
  `correctionDerivConst`, proves its nonnegativity, and proves the concrete field at every spacetime point via
  `correctionData_correction` + the general `latticeLift_iteratedFDeriv_eq`.  It carries the necessary global
  `hv : ContDiff ℝ ∞ v` and the placement premise `ε₀ ≤ 1`; all declarations have exactly the standard three axioms.

- **U6 — `force_derivative_bound`** (pure transport). New `Section3/T17/ForceDeriv.lean`. Target
  `force_derivative_bound` (`Spec.lean:893`). Route: U2(b) `force_eq` + U1 + Paper1
  `physicalForce_spatial_derivative_bound:270` (`|∂ₓᵝ Source.correctionForce| ≤ C(ε⁻¹)^{2+m}`). **M, codex-sol.**
  Deps: U1, U2.
  **Status (lane 385, DONE):** `ForceDeriv.lean` defines the Paper1-selected `forceDerivConst`, proves
  nonnegativity, and proves the concrete field through `force_eq` + the general lattice derivative bridge.  The
  force slice-support input is derived from `correctionForce_support` + `physical_support`; global `hv` supplies
  both the Paper1 hypothesis and `force_eq`'s local smoothness.  All declarations have exactly the standard three axioms.

- **U7 — `force_smooth` / `force_periodic` / `force_support`** (transport + T16 reuse). New
  `Section3/T17/ForceSupport.lean`. Targets `Spec.lean:840,844,848`. Route: U2(b) `force_eq`; `force_smooth`
  from Paper1 `CorrectionVectorNorms.physicalForce_smooth:22` + T16 `latticeLift_smooth:120`; `force_periodic`
  from T16 `latticeLift_periodic:128`; `force_support` from Paper1 `physicalForce_compact:37` (support in
  `Ioo(T±2ε²) × ball x₀ (ε·θRadius)`, **open ball**) + T16 `latticeLift_timeSupport:251` /
  `latticeLift_sliceSupport:275` → `periodicSet (ball x₀ (ε·θRadius))`. **M, codex-sol.** Deps: U2.
  **Status (lane 425, DONE):** `Section3/T17/ForceSupport.lean` proves all three fields at the concrete
  `correctionData` under the global `hv : ContDiff ℝ ∞ v` (G1), with the manuscript's **open** ball.
  `latticeLift_sliceSupport` could not be used: it needs a strictly larger radius and bounds a single
  spatial slice.  §0 of the module therefore adds `latticeLift_spaceSupport`, the space-time companion of
  T16's `latticeLift_sliceSupport_closed`, applied to the compact `C = Prod.snd '' tsupport` of the
  single-copy force.  All declarations have exactly the standard three axioms.

- **U8 — force torus support volume/duration** (new torus wrapping I02 content). New
  `Section3/T17/ForceVolume.lean`. Targets `spatialVolumeConst`, `spatialVolumeConst_nonneg`,
  `force_spatial_volume` (`Spec.lean:861`), `force_time_length` (`Spec.lean:866`). Route: U2(b)+U7 put
  `tsupport (torusSpaceTimeLift (correctionForce …))` = torus image of the **one** Euclidean copy support;
  the **new** single-copy set-measure bridge gives `periodicTorusMeasure (torusSpatialSupport …) =
  volume (Prod.snd '' tsupport (Source.correctionForce …))` (Haar-on-cube = Lebesgue, T15 `HaarBridge` style
  for indicator sets), bounded `≤ ofReal(C ε³)` by registered `I02.force_spatial_volume`
  (`Contracts/V1/Correction.lean:454`); temporal projection is not periodized, so
  `torusTemporalSupport = Prod.fst '' tsupport` directly ≤ `ofReal(4ε²)` by `I02.force_time_length`
  (`:460`). **M–L, Opus.** Deps: U2, U7; T15 `HaarBridge`.

- **U9 — energy bound + honest slices** (new torus wrapping I02 content). New `Section3/T17/Energy.lean`.
  Targets `correction_slice_memLp` (`Spec.lean:902`), `correction_gradient_memLp` (`:906`), `energyConst`,
  `energyConst_nonneg`, `correction_energy_bound` (`:918`). Route: single-copy Haar/Lebesgue energy bridge
  (T15 `HaarBridge` U-TB1 + its `gradientENorm`/`energyGradientT` companion) gives
  `energyENormT place.T (D.correction ε) = Data.energyENorm place.T (physicalCorrection …)` (the periodic
  torus slice is the single copy on the cube); then registered `I02.correction_energy_bound`
  (`Contracts/V1/Correction.lean:486`, `≤ C ε^{3/2}`, from `CorrectionEnergy.physicalCorrection_uniform_energy:54`).
  Torus `MemLp` slices from `I02.correction_slice_memLp`/`correction_gradient_memLp` + `torusLift` single-copy.
  **L, Opus.** Deps: U2; **T15 U-TB1** (lane 363/364).

  **U9 status (lane 434, DONE 2026-09-18).** All five targets closed in the new
  `Section3/T17/Energy.lean` (namespace `NSFormalization.Section3.T17`), at the concrete
  `correctionData` of U2: `correction_slice_memLp`, `correction_gradient_memLp`, `energyConst`,
  `energyConst_nonneg`, `correction_energy_bound` (`≤ ofReal (energyConst · ε^(3/2))`), with
  `energyConst = √A + √D` — literally the constant the Section 4 binding registers
  (`Bindings/Correction.lean:349`), `A` from `Paper1.CorrectionEnergy.physicalCorrection_uniform_energy`,
  `D` from `Paper1.InsertionEnergy.correction_gradientSquare_bound`.  The route is the planned one:
  each torus slice of `D.correction ε` is **definitionally** T13's `periodize` of the single-copy
  slice, so T15 U-TB1's `eLpNorm_torusLift_periodize` and
  `eLpNorm_torusLift_spatialGradient_periodize` identify both summands of `energyENormT` with the
  whole-space summands bounded by `I02.energyEssSup_le` / `I02.energyGradient_le`.  The two `MemLp`
  fields do **not** use the bridge (there is no `memLp_torusLift_*` in `HaarBridge.lean`): §1 of the
  module reproves `Paper1.memLp_torusLift` for an arbitrary normed value type
  (`memLp_torusLift_of_continuous`), which is what the `Space`- and
  `WithLp 2 (Fin 3 → Space)`-valued lifts need.  Premises = lane 385's cutoff block + the documented
  G1 `hv : ContDiff ℝ ∞ v` + one placement clause
  `hcube : closure (ball x₀ r) ⊆ interior fundamentalCube`, which
  `research/T17/probes/energy_closes.lean:hcube_of_placement` derives from
  `PlacementData.chartBall_in_cube` ∘ `CorrectionAPI.ball_in_chart` (so it is not a new assumption).
  Note for later units: a non-vacuity witness for anything Haar-normed must be placed **inside** the
  cube — lane 425's `x₀ = 0` does not satisfy `hcube`; this lane uses the cube centre.

- **U10 — mixed bound + honest slices** (new torus wrapping I02 content). New `Section3/T17/Mixed.lean`.
  Targets `force_spatial_memLp` (`Spec.lean:923`), `mixedConst`, `mixedConst_nonneg`, `force_mixed_bound`
  (`Spec.lean:936`). Route: U2(b) `force_eq` + single-copy Haar/Lebesgue mixed bridge (T15 `Mixed.lean`,
  `|Q|=1`) give `mixedLebesgueENormT q p (correctionForce …) = Data.mixedLebesgueENorm q p
  (Source.correctionForce …)`, then registered `I02.force_mixed_bound` (`Contracts/V1/Correction.lean:502`,
  `≤ C ε^{α(p,q)+1}`, from `CorrectionMixedNorms.physical_force_mixed_bound:123`, both `∞` endpoints via
  `toReal ⊤ = 0`); honest `L^p` slices from `physical_force_spatial_memLp:164`. Quantifiers `[Fact (1≤p)],
  1≤q`; exponent `alpha` by the Spec drift `example`. **L, Opus.** Deps: U2; **T15 mixed bridge** (lane 363/364).

- **U11 — `eq:HHs` (Sobolev)** (**BLOCKED on T13.localization, lanes 354/359**). New `Section3/T17/Sobolev.lean`.
  Targets `sobolevConst` (`Spec.lean:944`), `sobolevConst_pos` (`:947`), `forceSobolev_memLp` (`:950`),
  `force_sobolev_bound` (`:955`). Route (`RECONCILIATION §4 ⑦`): express each force slice as `periodize` of its
  compact central copy (U2 + T13 single-copy adapter); apply the structure's `localization : LocalizationAPI`
  field — `wholeSpace_identity`/`torus_identity`/`localization` for `0<s<1`, `endpoint_zero`/`endpoint_one` at
  `s=0,1` — with **one** ε-independent constant; feed Paper1
  `PeriodicCorrectionEndpointRates.correction_vector_whole_endpoint_rates:49` (H⁰ rate `ε^{3/2}`, H¹ rate
  `ε^{1/2}` at `q=1`) and `PeriodicCorrectionEndpointInstantiation:30` through the `ε²` time change to
  `C_s(ε^{3/2}+ε^{3/2-s})`; assemble the `MemForceSobolevT 1 s` datum path. **No named input at theorem level**
  (`localization` is a structure field), but its `.localization` sub-field is what 354/359 prove — exercisable
  and non-vacuous only after T13.localization lands. **L, Opus.** Deps: U2; **T13.localization**.

- **U12 — assembly + statement + contract/bindings/tests + non-vacuity.** New `Section3/T17/Assembly.lean`
  + a fresh `Contracts/V1/…` (T17 registration; T02 umbrella per PLAN). Bundle the `CorrectionAPI` over the
  concrete `correctionData` (U2): `potential` = T16 `localPotential` witness, `localization` = T13 witness
  (**gated**), all quantitative fields U3–U11, structural fields (`viscosity_pos`, `radius_pos`,
  `ball_in_chart`, `eps_le_placement` — shrink `D.ε₀ ≤ place.ε₀`, `reference_periodic`) from hypotheses; close
  `correctionStatement` (`Spec.lean:980`, `Nonempty (CorrectionAPI …)` under T16's hypotheses). Register every
  field except `localization`/`sobolev` and stage those; the `Nonempty` closure and non-vacuity gate on T13
  (354/359) and the T15 bridges (363/364). **M, codex-sol.** Deps: all; **T13.localization**, T15 bridges.

## 2. Waves (≤ 3 concurrent per current lane cap)

| wave | units | sizes / models |
|---|---|---|
| W1 | **U1** deriv bridge · **U2** transport identities · **U3** correction profile | S–M sol / M Opus / L Opus |
| W2 | **U4** force profile · **U5** correction deriv · **U6** force deriv | L Opus / M sol / M sol |
| W3 | **U7** force smooth/support · **U8** support volume · **U9** energy | M sol / M–L Opus / L Opus |
| W4 | **U10** mixed · **U11** Sobolev\* · **U12** assembly\* | L Opus / L Opus / M sol |

`*` = consumes **T13.localization** (lanes 354/359); U9/U10/U8 additionally consume the **T15 Haar/Lebesgue
bridges** (lanes 363/364). U2 is on the critical path (U5–U11 all rewrite through it); W1 must land U2 before
W2 opens. Start the gated lanes against the structure/import hypotheses, but stage their non-vacuity and the
`correctionStatement` closure until T13 (354/359) and T15 (363/364) land. Lane numbers allocated by the lead
in `PLAN.md`.

## 3. Risks

1. **T13.localization (highest).** `eq:HHs` (U11), the `localization` field, and the `Nonempty` closure (U12)
   cannot be *exercised* until 354/359 register a `LocalizationAPI` inhabitant. The field theorems are provable
   now (structure hypothesis); only end-to-end `correctionStatement` and non-vacuity are gated. Stage, don't drop.
2. **T15 Haar↔Lebesgue bridges (U8/U9/U10).** The single-copy identifications reuse `Section3/T15/{HaarBridge,
   Mixed}.lean` (lanes 363/364, not yet in tree). If they slip, U9/U10 stall on the *identification* only — the
   whole-space `≤ Cε^k` halves (`I02`, Paper1) are ready. U8's set-measure bridge is T17-new (Haar-on-cube of an
   indicator); prove it in-lane if T15 exposes only the norm form.
3. **Profile `def` bridge (U3/U4).** `rescaledPotential`/`rescaledCorrectionProfile`/`rescaledForceProfile`
   (Spec.lean literal displays) must be shown equal to Paper1's `profile`/`forceProfile` before any Paper1 lemma
   applies. This is `RECONCILIATION §4 ①②`; the potential display uses `LocalPotentialAPI.potential_formula`.
   If the `def` bridge is not `rfl`-clean, it is the analytic long pole of W1–W2 (both profile lanes wait on it).
4. **`eps_le_placement` shrink.** T16 hands `D.ε₀`; T17 needs `D.ε₀ ≤ place.ε₀` and `≤ 1`. Handle by shrinking
   the threshold in U12's `correctionData`, not by weakening any field's `Ioc 0 D.ε₀` quantifier.
5. **Abstract-`D` vs concrete correction.** Fields are stated over abstract `D`; proofs need
   `D.correction ε = latticeLift (physicalCorrection …)`. U2's `correctionData` makes this `rfl`, but every
   quantitative lane must state its lemma about that concrete term and let U12 bundle — do not attempt to prove
   a quantitative field for an arbitrary `LocalPotentialAPI`-satisfying `D` (it is false without the construction).

### U1 status (lane 369 → r1 → r2, DONE after two codex REJECTs)
`Section3/T17/LatticeDeriv.lean` now carries **both** forms, each
`[propext, Classical.choice, Quot.sound]`:
- `latticeLift_iteratedFDeriv_eq` / `latticeLift_iteratedFDeriv_norm_le_iSup` —
  the `k = 0` fundamental-ball equality and its `ℝ≥0∞`/`⨆` corollary (unchanged
  from lane 369 r0).
- **`latticeLift_iteratedFDeriv_eq`** (the U1 target) — the general **arbitrary-`z`**
  `∃ k` shifted-copy equality
  `‖iteratedFDeriv ℝ n (latticeLift w) z u‖ = ‖iteratedFDeriv ℝ n w (z - (0, latticeVector k)) u‖`,
  covering the no-copy/zero case (`k = 0`, both sides `0`).  Route: periodicity
  (`isPeriodicOn_sub_latticeVector`) + `latticeLift_eq_of_ball` give a
  single-translate neighbourhood, then `Filter.EventuallyEq.iteratedFDeriv` and
  `iteratedFDeriv_comp_sub`; the zero case builds an explicit `ball z.2 (r-ρ)` of
  vanishing terms.  Hypotheses = `latticeLift_eq_of_ball`'s (`hslice`, `r+ρ≤1`)
  **plus** the strict separation `hlt : ρ < r` (satisfied downstream,
  `hεspace : ε·θRadius < r`; load-bearing — `research/T17/probes/rev369r1_negative_lt.lean`).
- **`latticeLift_iteratedFDeriv_norm_le_iSup`** — the all-`z` `ℝ≥0∞`/`⨆`
  corollary in the norm spelling `CorrectionAPI.correction_derivative_bound`
  consumes (arbitrary `u : Fin n → SpaceTime` subsumes the `Fin.append` tuple).

U5 (`correction_derivative_bound`) and U6 (`force_derivative_bound`) are now
**DONE in lane 385**.  They transport the Paper1 Euclidean derivative bounds to
**every** spacetime point through `latticeLift_iteratedFDeriv_eq`, no longer only
the fundamental ball; see the unit status notes above and `REPORT_385.md`.
