# T11 — proof-lane split (证明拆分表)

Lead-facing, 2026-09-17. Targets = the five reconciled structures exactly as stated on the canonical
module in `research/T11/probes/api_on_canonical.lean` (vocabulary `Section3/T11/LocalTheory.lean` +
`Section3/T10/PeriodicData.lean`; design `research/T11/RECONCILIATION.md` §0–§3; candidates
`research/T11/IMPLEMENTATION_CANDIDATES.md`). 26 fields: `PeriodicLocalRegularity` 3 (a predicate, never
a standalone target), `PeriodicLocalTheoryAPI` 8, `PeriodicContinuationAPI` 5, `PeriodicMeanReductionAPI` 6,
`PeriodicViscosityRescalingAPI` 4. Size: **S** ≤ ~100 lines; **M** one self-contained lemma with a known
proof; **L** a multi-file campaign. Model: `sol` = conversions/algebra/bookkeeping, `astra` = analytic core.

## Lead review (2026-09-18 00:55Z)
Drafted by an Opus subagent from the survey; **approved** by the lead as the T11 proof plan. Lane numbers: W1 = 308 (U1), 309 (U2, after 308 lands), 310 (U3), 311 (U9a). The `H¹` restart risk is handled exactly as Section 4 did: manuscript statement kept in V1 as a named unproved predicate if it cannot be proved, explicit `H⁷` fixed-force V2 registered, consumers checked; no silent weakening.

## 0. Ground rules

**Peeling rule.** A unit that cannot close its target with what is in the tree names **exactly one**
input hypothesis, as a `def … : Prop` in `Section3/T11/`, written out here, and proves the target
conditionally on that one name. The name must be (i) non-tautological — never the target field restated;
(ii) satisfiable at a nonzero solution and a nonzero force (`logs/LESSONS.md` 09-15 1901/1905: two
Section 4 lanes proved theorems whose named input was unsatisfiable); (iii) discharged by a named later
unit here. Silent weakening of a V1 field is forbidden; an honest narrowing is a new **named predicate**
+ a V2 contract, as `Contracts/V2/Continuation.lean:88` `RestartFixedForce` / `:105`
`ManuscriptHorizonLowerBoundH1` did for A04.

**Key finding.** `ClassicalPeriodicLocalTheory` (`Paper1/PeriodicLocalLifespan.lean:73`) is **never
instantiated**: every occurrence in `formalization/` and `vendor/` is a hypothesis binder
`(H : ClassicalPeriodicLocalTheory)`; its two fields (`local_flow`, `finite_h2_extension`) carry the entire
unproved analytic content. **But** these Paper 1 theorems are *unconditional*, hence free:
`flow_velocity_agree_on_common_interval` (`:175`), `normalized_flows_agree` (`:229`), `maximal_solutions_agree`
(`:515`), `exists_maximal_periodic_solution_of_lifespan_pos` (`:411` — gluing needs only `0 < lifespan`),
`Flow.restrict`/`nonempty_restrict` (`PeriodicFlowRestriction.lean:20,48`), `normalizedFlow`
(`PeriodicPressureNormalization.lean:237`), `integral_torusLift` (`Paper1/TorusCube.lean:40`). So uniqueness,
maximality and gluing are reachable today; **existence is the only genuine hole**, as A01 was on `ℝ³`.

## 1. Units

- **U1 — `ClassicalSolutionT ↔ Flow` conversion** (structure exception). New `Section3/T11/FlowConversion.lean`.
  `toFlow (w : ClassicalSolutionT ν a f T) : Flow ν a f T` (11 of 14 fields transfer, §4);
  `ofFlow (U : Flow ν a f T) (hs hg hn) : ClassicalSolutionT ν a f T` with `hn : PressureGaugeT (Ico 0 T) U.pressure`;
  round-trips by `rfl` on data fields. Two spelling lemmas needed: `Source.residual ν u p t x =
  NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x` (`Source/Insertion.lean:21` vs
  `vendor/…/R3/ProblemStatement.lean:57`, identical bodies → `rfl`) and `IsPeriodicOn I z ↔ UnitSpatialPeriodsOn I z`
  (`PeriodicData.lean:62` vs `vendor/…/ProblemStatement.lean:49` → `Iff.rfl`). **S–M, sol.** Deps: —.
  **Status (308): complete — both spelling bridges, fieldwise conversions, full round trips, force transport, probe, non-vacuity example, and exact axiom audit pass with no named input.**
- **U2 — datum existence, finiteness, criterion bridge.** New `Section3/T11/CriterionBridge.lean`.
  (a) a smooth periodic `z` has an order-`s` datum at every real `s`, hence `periodicSobolevENorm s z ≠ ⊤`
  (componentwise `smoothPeriodicWeightedFourierLp`, `PeriodicSmoothSobolev.lean:45`, + `realPeriodicSubmodule`
  membership + Haar integrability); (b) `periodicSobolevENorm s z = ENNReal.ofReal (periodicVectorSobolevNorm s …)`
  via registered `T01.torus_data`.`datum_unique` and `:53` `norm_smoothPeriodicWeightedFourierLp`;
  (c) measurability of `t ↦ periodicSobolevENorm 2 (u t ·)` from `ClassicalSolutionT.sobolev`'s `ContinuousOn G`;
  (d) **both directions** of `squaredHTwoIntegralT S w.velocity ≠ ⊤ ↔ FiniteH2Energy (toFlow w)`
  (= `IntegrableOn (h2SquaredProfile ·) (Ioc 0 S)`, `PeriodicLocalLifespan.lean:60`; land via
  `PeriodicFiniteH2Bridge.lean:25`). **L, astra.** Deps: U1; reuses lane 305's Fourier calculus for (a).
  **Status (309): complete — all-real-order datum existence/finiteness, exact norm identification, restricted-time measurability, and both criterion directions proved without named input; see `REPORT_309.md`.**
- **U3 — Galilean class and translation algebra.** New `Section3/T11/GalileanClasses.lean`. Targets
  `translation_preserves_sobolev` (datum case: coefficients pick up the unimodular `e^{2πi k·y}`; `⊤` case:
  translate back by `-y`), `transformed_classes`, `transformed_mean_zero`. Supporting: `ContDiff ℝ ∞ (forceMeanT f)`,
  hence of `galileanMeanT`/`galileanShiftT` — the vector analogue of `cubeIntegral_contDiffOn_Ico`
  (`PeriodicPressureNormalization.lean:93`). Compact positive-time support of `galileanForceT a f` is inherited
  from `f` (spatial translation does not move time support). **M, sol.** Deps: —.
  **Status (310): complete — all three exact fields, global mean/primitive smoothness, inherited support, internal solution-mean evolution, probe, non-vacuity witness, and guarded exact axiom audit pass with no named input.**
- **U4 — viscosity algebra.** New `Section3/T11/Rescaling.lean`. `inverse_identities` (three `funext` +
  positive-`ν` algebra), `scaled_classes` (time dilation maps a compact subset of `Ioi 0` to one). **S, sol.** Deps: —.
  **Status (314): complete — both exact fields, compact positive-time support transport, probe, non-vacuity example, and guarded exact axiom audit pass with no named input.**
- **U5 — uniqueness package.** New `Section3/T11/Uniqueness.lean`. `velocity_unique`, `pressure_unique`
  (pointwise on `Ico 0 (min T₁ T₂)`): `toFlow` both sides; `w.pressure_gauge` + `pressureMeanT = cubeIntegral`
  (from `integral_torusLift`) gives `IsNormalized (toFlow w)` (`PeriodicLocalLifespan.lean:44`); then
  `normalized_flows_agree` (`:229`) verbatim. `horizon_le_lifespan` is `le_iSup_of_le T (le_iSup_of_le ⟨w⟩ le_rfl)`
  on `maximalLifespanT` (`PeriodicData.lean:303`) — no conversion. **M, sol.** Deps: U1.
  **Status (315): complete — all three exact fields close, the nonzero constant-flow probe and exact three-axiom audit pass, with no named input; see `REPORT_315.md`.**
- **U6 — solution transport under smooth change of variables.** New `Section3/T11/Transport.lean`. One shared
  constructor: given `w : ClassicalSolutionT ν a f T`, a `C∞` time-dependent translation `X : ℝ → Space` and
  constants `(α,β,γ)`, rebuild a `ClassicalSolutionT` for the transformed data, transporting all 14 fields (chain
  rules for `temporalDerivative`/`spatialLaplacian`/`pressureGradient`/`spatialDivergence`; datum path via U3's
  translation isometry; gauge via translation-invariance of `meanT`). `transformed_solution`, `to_unit`,
  `from_unit` are instances. **L, astra.** Deps: U2, U3, U4.
- **U7 — mean identity.** New `Section3/T11/MeanIdentity.lean`. `mean_formula`
  (`velocityMeanT w.velocity t = galileanMeanT a f t` on `Ico 0 T`) and `mean_derivative`
  (`HasDerivAt (velocityMeanT w.velocity) (forceMeanT f t) t` on `Ioo 0 T`). Route: integrate `w.momentum`
  over `T³`; `meanT (Δu) = meanT (∇p) = meanT (convectionDivergenceT u) = 0` (each a periodic derivative, mean
  zero by `integral_torusLift` + periodicity); differentiate under the Haar integral as in
  `pressureMean_hasDerivAt_interior` (`PeriodicPressureNormalization.lean:149`); FTC for `galileanMeanT`;
  `t = 0` via `w.initial`. **L, astra.** Deps: U3.
  **Status (316): complete — exact `mean_formula` and `mean_derivative`, via U3 cancellation + Haar invariance + FTC; no named input; non-vacuity and exact axiom audit; see `REPORT_316.md`.**
- **U8 — transformed / rescaled solutions.** `transformed_solution`, `to_unit`, `from_unit` as instances of U6
  (`from_unit` inverts via U4; horizon `T ↦ ν·T`), each carrying `PeriodicLocalRegularity`. **M, sol.** Deps: U6, U7.
- **U9 — quantitative periodic local existence (the long pole).** New `Section3/T11/LocalExistence.lean`.
  Discharges the one named input of U10:
  ```
  def PeriodicQuantitativeLocalInput : Prop :=
    ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ : ℝ, 0 < δ ∧
      ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
        ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
          (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ K) →
            ∃ w : ClassicalSolutionT ν a g δ, PeriodicLocalRegularity ν a g δ w
  ```
  Not `restart` restated: the force here is an arbitrary smooth periodic field with finite `L¹_tH^m` norms,
  *not* an `F_T` member — a positive time shift of an `F_T` force need not vanish at its new time zero, so
  `timeShiftT t₀ f ∉ forceClassT` (`RECONCILIATION.md` §1(vi), "needs a lemma" ⑨). Routes, in order:
  **(R1)** instantiate HeliCorgi's abstract endpoint layer `FlowMapUniformRestartPackage`
  (`vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:29`) on the torus carrier — that layer supplies
  only endpoint bookkeeping (`:59`), and its `restart_past_terminal` field *is* the PDE obligation, so R1
  buys the `t₀↑S` argument, not existence. **(R2)** `SECTION3_PLAN.md` §7's fallback: copy A01's cylinder
  route to the coefficient level (Horizon / a-priori bound family / causal-window uniqueness), already
  validated once here. **L+ (expect 3–5 sub-lanes), astra.** Deps: U1, U2.
- **U10 — `restart`.** New `Section3/T11/Restart.lean`. From U9's input: for fixed `f ∈ forceClassT` and `S ≥ 0`,
  `{timeShiftT t₀ f : t₀ ∈ Icc 0 S}` has `forceSobolevENormT 1 m` uniformly bounded (compact time support in
  `Ioi 0` + smoothness), so one `K'` covers the window and one `δ` results. Mirror of A04 lane 215. **M, sol.**
  Deps: U9 (as named input while U9 runs), U2.
- **U11 — `horizon` / `solution` / `regularity`.** Same module. `restart` at `S = 0`, `t₀ = 0`,
  `K := periodicSobolevENorm 1 a` (finite by U2(a)), plus `timeShiftT 0 f = f` (`funext`, `add_zero`), gives
  existence; `horizon` is extracted by `Classical.choice`, defaulting to `1` off the class. **S–M, sol.** Deps: U10, U2.
- **U12 — `higherOrderBound`.** New `Section3/T11/HighOrder.lean`. Periodic `eq:Rhigh` (`appendix-a:127-147`) +
  Grönwall; mirror of A04's `energyIdentityHigh → higherOrderBound` chain (`research/A04/G1_SPLIT.md` SL0–SL8;
  `Contracts/V2/Continuation.lean:140`): pair the momentum equation against `u` in `H^m` on the T10 coefficient
  carrier — Laplacian identity, pressure drop (Leray self-adjointness), nonlinear IBP + tame product, force
  Cauchy–Schwarz, assembly, Grönwall. Torus tame product and `H²↪L^∞` come from T12 (`Section3/T12/SpectralGap.lean`,
  registered). **L (3–4 sub-lanes), astra.** Deps: U2; T12.
- **U13 — `restartBeyond`.** Same module as U10. Take `δ` from U10 at the `H¹` bound `K`; patch the
  `SolvesBelowT` pair with the restart solution at `t₀` near `S` into one `ClassicalSolutionT ν a f (S+δ)` with
  **exact** normalized-pressure agreement on `[0,S)` ("needs a lemma" ⑩; overlap bookkeeping =
  `extension_agrees_on_common_interval`, `:564`). **M–L, sol.** Deps: U10, U5.
- **U14 — `extendsBeyond`.** Same module. `squaredHTwoIntegralT S u ≠ ⊤` → U12 at `m = 1` → the `H¹`
  trajectory bound → U13 gives the concrete `ClassicalSolutionT ν a f (S+δ)` with agreement, which *is*
  `ExtendsBeyondT` (`LocalTheory.lean:68`) — strictly stronger than registered `A04.extendsBeyond`
  (`Contracts/V2/Continuation.lean:175`, conclusion only `ofReal S < maximalLifespanR`). **M, sol.** Deps: U12, U13.
- **U15 — `exists_maximal` + `maximal_unique`.** New `Section3/T11/Maximal.lean`. `0 < maximalLifespanT` from
  U11; gluing is `exists_maximal_periodic_solution_of_lifespan_pos` (`:411`, unconditional) after U1, then
  `ofFlow` back at each horizon (the three extra fields come from U11's solutions via U5). `maximal_unique` at
  presingular times: from `IsMaximalPeriodicSolution` (`LocalTheory.lean:52`) pick `S` with `t < S` and
  `ofReal S < maximalLifespanT` (`ENNReal` supremum density), then U5. Also prove `maximalLifespanT =
  PeriodicLifespan.lifespan` here (§4 last row). **M, sol.** Deps: U5, U11.
  **Status (323): complete conditional only on `PeriodicMaximalExistenceInput` pending U11; both exact fields, unconditional lifespan equality, nonzero compact-force probe, and exact axiom audit pass.**
- **U16 — `lifespanInfiniteOfLocallyFinite`.** Same module. Contrapose: if `maximalLifespanT = L ≠ ⊤`, the
  hypothesis at `S = L.toReal` (the `≤` is load-bearing, `RECONCILIATION.md` §2) plus U14 gives a solution on
  `L.toReal + δ`, hence `ofReal (L.toReal + δ) ≤ L`, absurd. **M, sol.** Deps: U14, U15.
- **U17 — assembly, contract, binding, tests.** Assemble the four API terms (`PeriodicLocalTheoryAPI` is a `def`,
  the other three `theorem`s); write `Contracts/V1/TorusLocalTheory.lean` (or `V2` if §3.1 fires) registering
  `T01.torus_local_theory` with the tier-(b) solution-class restatements deferred by `T01.torus_data`
  (`ClassicalSolutionT` via the structure exception: fieldwise conversions + round-trips, **not** `rfl`), plus
  bindings, tests and non-vacuity at a nonzero force/datum. **M, sol.** Deps: all.

- **U9a / lane 311 status:** R2 coefficient route selected; canonical real-vector heat contraction/smoothing/semigroup/coherence and nonzero forced classical witness proved; exact `PeriodicQuantitativeLocalInput` remains open; U9→U10 same-K-over-all-orders issue recorded in `EXISTENCE_ROUTE.md`; details and gates in `REPORT_311.md`.

- **U9c / lane 317 status:** complete — `ConvolutionBound.lean` proves `torusConvolutionInput : TorusConvolutionInput` and `torusTwoSpaceContract_nonempty'` unconditionally by the discrete weighted convolution bound; no residual input; probe, exact three-axiom audit and all gates pass; see `REPORT_317.md`.

- **U9d1 / lane 319 status:** conditional half-order common-horizon induction, real-order descent and nonzero forced mild witness proved; ONE residual `TorusHalfStepInput` → **U9d1-analytic follow-up** (unassigned); raw `.1` equality is a phantom-index statement defect, not regularity; exact input and limitations in `EXISTENCE_ROUTE.md` §U9d1 and `REPORT_319.md`.
- **U9d / lane 318 status:** partial, not closed — unconditional H³ Fourier inverse, exact datum/path and initial recovery, joint continuity, and full affine-constant forced recovery on arbitrary T; general bootstrap, divergence, pressure and PDE recovery remain open; no new named input; see `REPORT_318.md`.

- **U9d1a / lane 328 status:** complete — `ConvolutionBoundReal.lean` proves the real-order projected convection bound `torusConvolutionCLM_real r hr : H^r →L H^r →L H^(r-1)` for every real `r ≥ 3`, with the coefficient identity (intrinsic and transported to lane 317's `torusProjectedConvectionSymbol` via `persistenceDown r 3`), the explicit bound `9·sqrt (2·4^r·∑ W^(-r))`, the order-transport/reweighting-compatibility lemma (no `r ≤ r'` needed) and `torusConvolutionInput_ofReal : TorusConvolutionInput`; no residual input; one elaborator workaround for the nested bilinear type at index `r-1` (output index carried as a parameter, codomain pinned by an `example`) — see `REPORT_328.md` §3 and `ATTEMPTS_CONVOLUTION_BOUND_REAL.md`.

- **U9d2 status (320, partial):** `ClassicalAssembly` proves exact persistence/reweight and Sobolev paths, spatial C∞, full mild-to-physical divergence on Ico, and projected-from-classical; sole input `PersistenceInput T u`; time regularity, pressure and general classical assembly remain open. See `REPORT_320.md`.

- **U9d2a status (326, partial; codex REJECT resolved):** `MildPressure.lean` constructs the pressure as the genuine Leray complement of `F − Q` and proves `pressure_periodic`, `pressure_gauge`, `pressure_gradient` (`MemLp`), spatial `C^∞` slices, `∇p = (I−P)(F−Q)` **in canonical coefficient data** (via the new periodic convolution theorem `periodicFourierCoeff_mul`, which also identifies the physical convection coefficient with `torusConvectionDatum` — reusable by lane 327), every-`H^m` membership of the pressure coefficients, and `PeriodicLocalRegularity.pressure_poisson`; sole input `PersistenceInput T u`, no new named input, nonzero instance included, every one of the 95 module declarations audited to exactly the standard three axioms. Residual = exactly `ContDiffOn ℝ ∞ (mildPressure g u) (Ico 0 T ×ˢ univ)` (plus joint continuity), not derivable from `PersistenceInput` (no time regularity). See `REPORT_326.md`, `ATTEMPTS_MILD_PRESSURE.md`.
- **U9d2b status (327, partial):** `MildMomentum.lean` differentiates the Duhamel formula coefficientwise (`mild_coeff_hasDerivAt` / `mild_physicalCoeff_hasDerivAt`: `d/dt û = −ν4π²|k|²û + (P̂(F−Q))^`), gives the physical velocity's first time derivative on `Ioo 0 T ×ˢ univ` (`torusPhysicalVelocity_hasDerivAt`, `temporalDerivative_torusPhysicalVelocity'`), proves the exact `ClassicalSolutionT.momentum` and `PeriodicLocalRegularity.projected` fields for any pressure with gradient datum `(I−P)(F−Q)` (`momentum_of_pressure`, `projected_of_pressure`) and instantiates them with lane 326's `mildPressure` (`momentum_of_mildPressure`, `projected_of_mildPressure`); new general tools: `W(k) ≤ 2W(l)W(k−l)` + `convolution_norm_bound` (one weight-power gain), the frequency-local Leray symbol `lerayAt`, and `torusPhysicalCoeff_bilinear` (the contract's bilinear map is `lerayAt` of lane 326's canonical `torusConvectionDatum`); the convolution theorem and the convection identification are reused from merged 326 (dedupe recorded in `ATTEMPTS_MILD_MOMENTUM.md` §5). **Single named input `PersistenceInput T u`**: the force side is discharged by the new `persistenceInput_force_of_smooth` (smooth periodic `g` + order-three datum path ⟹ continuous datum paths at every order, via `exists_periodicDatum_smooth` + `T10/ForcePaths.continuous_datum_path`), closing codex review gap 1. Residual = exactly the two joint `C^∞` fields (velocity and pressure), which need the mild equation at orders 5, 7, …. See `REPORT_327.md`, `ATTEMPTS_MILD_MOMENTUM.md`.
- **U9d1b / lane 329 status:** complete and unconditional — new `Section3/T11/FractionalSmoothing.lean` proves the `σ = 3/2` symbol bound `W(k)^{3/4} e^{-νtΛ(k)} ≤ (νT + (3/4)e^{-1})^{3/4} (νt)^{-3/4}` on `0 < t ≤ T`, the order-`(s+3/2)` datum `torusHeatSmoothingFrac` with `IsPeriodicReweight s (s+3/2)` compatibility to the heat image and the matching norm bound, the CLM `torusHeatSmoothingCLM_frac : PeriodicSobolev s →L[ℝ] PeriodicSobolev (s+3/2)` with its operator-norm bound, endpoint-kernel integrability on `Ioc 0 t` and the exact mass `∫₀ᵗ (ν(t−τ))^{-3/4} dτ = 4 t^{1/4} ν^{-3/4}`, and strong continuity on `Ioc 0 T`. **No named input**; `TorusHalfStepInput` is NOT discharged (the endpoint Duhamel argument and a real-order `H^r×H^r→H^{r-1}` bound remain). Probe on a genuine single lattice mode at `s = 3`; all 32 declarations print the three standard axioms. See `REPORT_329.md`, `ATTEMPTS_FRACTIONAL_SMOOTHING.md`.
- **U9d1c / lane 330 status:** complete and unconditional — new `Section3/T11/DuhamelHalfStep.lean` proves `theorem torusHalfStepInput : TorusHalfStepInput` outright, hence `persistence_halfOrder_ladder_unconditional` and `persistence_unconditional` (lane 319's conditional persistence with its single named input discharged, same horizon, no shrinkage). Route: `w(t) = e^{νtΔ}A′ + ∫₀ᵗ e^{ν(t−τ)Δ}P_σ(τ)dτ − ∫₀ᵗ S_frac(ν(t−τ))Q_r(v τ,v τ)dτ` at `σ = r+1/2`, with the exponent identity `W^{3/4}W^{(r−3)/2} = W^{(σ−3)/2}W^{1/2}`. Two new pieces of infrastructure: `torusLerayCLM (s : ℝ)` (the Leray projector as a **bounded** operator at every real order, with order-transport and uniqueness) and `exists_continuous_lerayForcePath σ` (a **continuous** order-`σ` Leray force path for a smooth periodic force, via `T10.ForcePaths.continuous_datum_path` at `m = ⌈σ⌉₊` + `persistenceDown`); the brief's variant, which sent the force through the fractional kernel too, is impossible (gain `σ` costs `(t−τ)^{-σ/2}`, integrable only for `σ < 2`). Singular-integral integrability/continuity are inherited from a genuine `torusFracContract : MNS2.EndpointSafeTwoSpaceDuhamelContract ℝ (PeriodicSobolev (r+1/2)) (PeriodicSobolev (r-1))` built from lanes 328/329. No named input; nonzero constant-datum non-vacuity; all 45 declarations print the three standard axioms. See `REPORT_330.md`, `ATTEMPTS_DUHAMEL_HALF_STEP.md`.

## 2. Waves (≤ 4 concurrent)

| wave | units | sizes / models |
|---|---|---|
| W1 | **U1** conversion · **U2** criterion bridge · **U3** Galilean algebra · **U9a** existence route probe (R1 vs R2; the `T³` two-space contract) | S–M sol / L astra / M sol / L astra |
| W2 | **U4** viscosity algebra · **U5** uniqueness · **U7** mean identity · **U9b** existence construction | S sol / M sol / L astra / L+ astra |
| W3 | **U6** transport · **U12** high-order energy (3–4 sub-lanes) · **U10** restart · **U11** horizon/solution | L astra / L astra / M sol / S–M sol |
| W4 | **U8** transformed+rescaled · **U13** restartBeyond · **U15** maximal · (spill: U12 sub-lanes) | M sol / M–L sol / M sol |
| W5 | **U14** extendsBeyond · **U16** lifespan infinite · **U17** assembly | M sol / M sol / M sol |

U9 is the critical path and starts in W1 even though U1/U2 are unfinished — it runs against its own named
input until it lands. Lane numbers are allocated by the lead in `PLAN.md` (next free: 308).

## 3. Risks

1. **`restart`'s `H¹` ball (highest).** Section 4 could not prove the manuscript's `H¹` restart and narrowed to
   fixed-force `H⁷` (`Contracts/V2/Continuation.lean:88`, owner-approved; `research/A01/V2_DECISION.md`); the
   torus proof runs the same Picard estimates, so the same wall is expected. **Honest V2 route:** keep the `H¹`
   sentence as a named, unproved predicate `PeriodicRestartH1`, docstringed as not implied (shape of
   `ManuscriptHorizonLowerBoundH1`, `:105`); register `PeriodicRestartFixedForceH7` as the proved field; verify
   every T11 consumer (T18/T19/T20) restarts *the same* force with data bounded by U12's Grönwall bound, as
   A04's consumers did. Never silently change `1` to `7` inside the V1 statement.
2. **One common horizon for all Sobolev orders.** `horizon ν a f` occurs in both `solution` and the `∀ m`
   `regularity` record. If the construction yields an order-dependent horizon, the honest narrowing is a
   named `PeriodicCommonHorizon` predicate, not a per-order API.
3. **`pressure_poisson` vs the Leray form.** The reconciliation chose the Poisson prescription
   (`02-preliminaries.tex:84-88`); the nearest declaration (`Paper1/PeriodicPressureSymbolOperator.lean:37`) is
   coefficient-level under a zero-mode premise, so physical reconstruction + uniqueness + gauge identification
   is new work ("needs a lemma" ④). Falling back to the order-0 Leray form is a *contract* change → owner.
4. **`transformed_classes` smoothness.** `galileanForceT a f ∈ forceClassT` demands global `ContDiff ℝ ∞`, hence
   `forceMeanT f` smooth — differentiation under the Haar integral at every order. Provable (scalar analogue
   `PeriodicPressureNormalization.lean:93`), but it is the clause that made draft B's original wording *false*;
   no lane may weaken it to `ContDiffOn`.
5. **`squaredHTwoIntegralT ≠ ⊤` vs `FiniteH2Energy`** are different finiteness notions (`lintegral` of an
   `ℝ≥0∞` `⨅` vs `IntegrableOn` of a real profile); U2(d) must prove both directions incl. measurability.
6. **HeliCorgi route R1 may not close.** `SECTION3_PLAN.md` §7 flags that `EndpointSafeTwoSpace*` needs a
   `T³` Stokes smoothing `H²→H³`. Cap the probe (U9a) at one lane, then switch to R2.

## 4. Conversions — `ClassicalSolutionT ν a f T` ↔ `Paper1.PeriodicLifespan.Flow ν a f T`

Structure exception (`CLAUDE.md`): no `rfl` bridge exists; fieldwise conversion functions with defeq field
types + round-trip lemmas. `SpatialField`/`SpaceTimeField`/`SpaceTimeScalar` (`Contracts/V1/Data.lean:99,104,108`)
are `abbrev`s of vendor `Space → Space`/`VelocityField`/`PressureField`, so carriers are already defeq.

| `ClassicalSolutionT` (`PeriodicData.lean:265`) | `Flow` (`PeriodicLifespan.lean:12`) | status |
|---|---|---|
| `velocity`, `pressure`, `horizon_pos` | same names | **match**, `rfl` |
| `velocity_smooth`, `pressure_smooth` (`ContDiffOn ℝ ∞ · (Ico 0 T ×ˢ univ)`) | same | **match**, `rfl` |
| `initial`, `divergence` | same | **match**, `rfl` |
| `momentum`: `navierStokesResidual ν u p t x = f (t,x)` on `Ioo 0 T` | `equation`: `Source.residual ν u p t x = f (t,x)` | **name mismatch only**: `Source/Insertion.lean:21` and `vendor/…/R3/ProblemStatement.lean:57` have identical bodies → `rfl` |
| `velocity_periodic`, `pressure_periodic`: `IsPeriodicOn (Ico 0 T)` | `UnitSpatialPeriodsOn (Ico 0 T)` | **name mismatch only**: `PeriodicData.lean:62` vs `vendor/…/ProblemStatement.lean:49`, identical bodies → `Iff.rfl` |
| `sobolev`: `∀ m, ∃ G, ContinuousOn G (Ico 0 T) ∧ ∀ t ∈ Ico 0 T, IsPeriodicDatum m (u t ·) (G t)` | **absent** | **extra**: argument of `ofFlow`; supplied by U2(a) on a smooth periodic slab |
| `pressure_gradient`: `MemLp (torusLift (∇p t ·)) 2` | **absent** | **extra**: argument of `ofFlow`; automatic for a continuous field on a probability torus |
| `pressure_gauge`: `PressureGaugeT (Ico 0 T) p` = `∫_{T³} p(t) ∂Haar = 0` | **absent**; analogue is `IsNormalized U` (`PeriodicLocalLifespan.lean:44`), `cubeIntegral (p (t,·)) = 0` | **gauge-convention mismatch, closed by** `integral_torusLift` (`Paper1/TorusCube.lean:40`): `∫ z, torusLift g z ∂periodicTorusMeasure = cubeIntegral g`, hence `pressureMeanT p t = PeriodicPressureNormalization.pressureMean p t` and `PressureGaugeT I p ↔ IsNormalized`. `normalizedFlow` (`:237`) supplies the gauge for any `Flow` |
| force class `f ∈ forceClassT` = `MemForceT` (`:239`: global `ContDiff ℝ ∞`, `IsPeriodicOn univ`, `tsupport f ⊆ K ×ˢ univ`, `K` compact `⊆ Ioi 0`) | `IsSmoothPeriodicForce` (`PeriodicLocalLifespan.lean:31`: `ContDiffOn` on each `Icc 0 S ×ˢ univ`, `UnitSpatialPeriodsOn (Ici 0)`) | **one-directional**: `MemForceT f → IsSmoothPeriodicForce f` is easy; the converse is false (no support clause). Every use goes T11 → Paper 1 |
| initial class `a ∈ initialClassT` (`:234`: `ContDiff ℝ ∞ a ∧ IsPeriodicSpatial a ∧ IsSolenoidal a`) | `IsAdmissibleInitialData` (`Paper1/PeriodicInitialData.lean:21`: `smooth`, `UnitPeriods`, `∀ x, ∑ i (fderiv ℝ a x eᵢ) i = 0`) | **match**: `IsPeriodicSpatial = UnitPeriods` (`PeriodicIntegration.lean:40`), `IsSolenoidal` (`Section4/A02/SolutionClass.lean:93`) unfolds to the same sum → `Iff.rfl` / one `simp` |
| time intervals: `Ico 0 T` (smoothness/periodicity/divergence), `Ioo 0 T` (equation) | identical | **match** |
| `maximalLifespanT` (`:303`, `⨆` over `ClassicalSolutionT`) | `lifespan` (`PeriodicLifespan.lean:27`, `⨆` over `Flow`) | **not equal a priori**: `≤` from `toFlow`; the reverse needs the three extra fields at every horizon (U2(a) + U1). Prove the equality once, in U15 |

- **U10/U11 / lane 321 status:** complete — exact conditional `restart`, order-wise shifted-force bounds via landed `ForcePaths`, and the selected `horizon`/`solution`/`regularity` partial API all close from the sole allowed `PeriodicQuantitativeLocalInput'`; probe, non-vacuity, and exact three-axiom audit pass.

- **U12 / lane 322 status:** partial, honest — new `Section3/T11/HighOrder.lean` proves the exact `higherOrderBound` field **verbatim** from ONE written-out hypothesis, the periodic `eq:Rhigh` on a `ClassicalSolutionT` (`higherOrderBound_of_energyInequality`; no `def … : Prop` named input, because two independent facts are missing and naming one would misrepresent the gap). Unconditional: order descent `‖z‖_{H^r} ≤ ‖z‖_{H^s}` with constant 1, the horizon-uniform running `H²` cap from `squaredHTwoIntegralT S u ≠ ⊤`, the `L¹_tH^m` forcing cap for `f ∈ F_T`, the **pressure drop** by coefficient-side solenoidality (exhibited in the probe at a nonzero velocity datum and a nonzero pressure-gradient datum), the Laplacian pairing value `−|2πk|²∑|û|²`, force Cauchy–Schwarz, Young's absorption (`C_{m,ν} = C_m²/(4ν)`) and the full `ζ↓0` + Grönwall chain reusing `Section4.A04.sqrt_le_primitive_linear` / `Section4.A01.gronwall_bddAbove_Ico`. Residual = eq:Rhigh, needing (a) time differentiability of the coefficient path + momentum in datum form (Section 4's SL1/SL2; blocked on lane 321's `regularity`, hence on `PeriodicQuantitativeLocalInput'`) and (b) the torus tame product at the **pairing** level (T12's `tameProduct` is a scalar physical-field bound; lane 328's real-order convection CLM is the starting point). Suggested follow-ups **U12a** (energy identity) and **U12b** (nonlinear pairing bound); their conjunction is exactly the hypothesis. 24 module declarations, each printing exactly the three standard axioms (the shear-mode witness lives in the probe); see `REPORT_322.md`, `ATTEMPTS_HIGH_ORDER.md`.

- **U12a / lane 335 status:** complete, no named input — new `Section3/T11/EnergyIdentity.lean` proves lane 322's **missing fact A** outright for a genuine `ClassicalSolutionT`: `hasDerivAt_velocityCoeffT` (time differentiation of the Fourier coefficient integral under the integral sign, from `velocity_smooth` alone, via `Paper1.periodicFourierCoeff_eq_cube` + `PeriodicIntegration.hasDerivAt_cubeIntegral_of_contDiffOn`), `velocityDerivCoeffT_momentum` (the coefficient form `d/dt û ᵢ(k) = −ν|2πk|²û ᵢ(k) + (f̂ ᵢ(k) − Q̂ ᵢ(k)) − 2πikᵢp̂(k)`), `solenoidal_velocityCoeffT` + `torusPressureSymbol_drop_raw` (the pressure drops at every frequency), `hasDerivAt_torusSobolevNormAt_sq` (termwise differentiation of `∑ₖ W(k)^m∑ᵢ|û ᵢ|²`, dominated by `6MD·W(k)⁻²` from the **continuous order-`2m+4` datum path** of `ClassicalSolutionT.sobolev` plus one sup bound of `∂ₜu` on a compact slab piece — so no `ContDiffOn ℝ ∞ G` regularity predicate and no `PeriodicQuantitativeLocalInput'` is needed), and `energyIdentity_of_classical`: `d/dt‖u(t)‖²_{H^m} = −2ν‖∇u‖²_{H^m} − 2⟪(u·∇)u,u⟫_{H^m} + 2⟪f,u⟫_{H^m}` with `‖∇u‖_{H^m} = torusGradientNormAt m u t`. `hRhigh_of_pairingBound` then takes **U12b's pairing estimate as an explicit theorem argument** and returns `hRhigh` in lane 322's exact binder (`g := torusGradientNormAt m u t`), and `higherOrderBound_of_pairingBound` composes with 322 so that `PeriodicContinuationAPI.higherOrderBound` is now conditional on **missing fact B alone**. 51 module declarations, each printing exactly the three standard axioms; non-vacuity in `research/T11/probes/energy_identity_closes.lean` at the nonzero forced solution `u(t,x)=eᵗc`, where the identity's right-hand side is forced to `2e^{2t}‖K‖² > 0`. See `REPORT_335.md`, `ATTEMPTS_ENERGY_IDENTITY.md`.
