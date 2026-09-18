# T20 — proof-lane split (`prop:critical`, `paper/sections/03-torus.tex:383-505`)

Lead-facing, 2026-09-18. Target = the reconciled `CriticalRegularityTAPI` on the canonical module
`formalization/NSFormalization/Section3/T20/CriticalRegularity.lean` (lane 381; 23 fields = 12
constant/positivity/shrinking data + 11 mathematical), and its `criticalRegularityStatement :=
Nonempty CriticalRegularityTAPI`. Vocabulary = the copied T10/T11/T12 blocks (`research/T20/Spec.lean`,
identified `rfl` against the canonical modules by `research/T20/probes/api_on_canonical.lean`). Design =
`research/T20/RECONCILIATION.md` §3 + §4 "Needs a lemma" ①–⑫, `COMPARISON.md` "Proof dependencies".
House style = `research/T11/T11_SPLIT.md`, `research/T17/T17_SPLIT.md`. Section 4 twin = the registered
`R43.critical_regularity` (`prop:Rcritical1`) + `R44.critical_finite_horizon` (`prop:Rcritical2`) and the
modules under `Section4/R43/`, `Section4/R44/` (splits `research/R43/R43_SPLIT.md`, `research/R44/R44_SPLIT.md`).
Size: **S** ≤ ~100 lines; **M** one self-contained lemma with a known proof; **L** a multi-file campaign.
Model: `codex-sol` = reuse/transport/algebra/bookkeeping, `Opus` = analytic core.

## Status (lane 390, 2026-09-18)

- **U3 `bIntegral`** — DONE. `Section3/T20/BIntegral.lean`, theorem
  `NSFormalization.Section3.T20.bIntegral` (verbatim field type). Axioms
  `[propext, Classical.choice, Quot.sound]`.
- **U4 `constantTransportSkew`** — DONE. `Section3/T20/ConstantTransport.lean`,
  theorem `NSFormalization.Section3.T20.constantTransportSkew` (verbatim field type).
  Axioms `[propext, Classical.choice, Quot.sound]`.
- Probe `research/T20/probes/bintegral_transport_closes.lean`; axiom audit
  `research/T20/axioms_u3_u4.lean`; attempts `research/T20/ATTEMPTS_U3_U4.md`.
- **U7 critical trilinear estimate** — DONE (lane 413).
  `Section3/T20/CriticalTrilinear.lean`, theorem
  `NSFormalization.Section3.T20.criticalTrilinear` (`.toReal` form, the shape U8
  applies at each time) with `criticalTrilinear_enorm` (`ℝ≥0∞` form, no
  finiteness hypothesis) and `criticalTrilinear_pairing` (`periodicPairing`
  spelling).  Explicit constant
  `criticalTrilinearConst = CcriticalHalf * CcriticalThreeHalves ^ 2
  = 16 * CcriticalHalf ^ 3`, with `criticalTrilinearConst_pos`; this is the `C₀`
  U13 installs.  Built on the now-merged T12 U4 `velocityCriticalL3` (lane 401)
  and T12 U6 `gradientLambdaCriticalL3` (lane 405), so **U7 is no longer blocked
  on T12** and U8 is unblocked.  No named input.  Axioms
  `[propext, Classical.choice, Quot.sound]` for all 13 declarations.
  Probe `research/T20/probes/critical_trilinear_closes.lean` (nonzero witness
  `probeMZ`, plus the U8 slice shape check); audit `research/T20/axioms_u7.lean`;
  attempts `research/T20/ATTEMPTS_U7.md`.
- **U9 `yBound`** — DONE (lane 428).
  `Section3/T20/YBound.lean`, theorem
  `NSFormalization.Section3.T20.yBound` (verbatim field type, at
  `c = criticalSmallness = 1/(8*criticalTrilinearConst)`), with the general form
  `yBound_of_le` for any `c ≤ 1/(2*criticalTrilinearConst)`.  No named input, no
  residual.  `criticalSmallness_pos` and `criticalSmallness_lt_quarter`
  (`c < 1/(4*C₀)`, the structure's strict shrinking) are exported for U13.
  Route: one bounded even symbol `critSymbol k = |2πk|^{1/2}/(1+4π²|k|²)^{1/2}`,
  packaged by `T11.torusMultiplierCLM` as a contraction
  `critLower : PeriodicSobolev 1 →L[ℝ] PeriodicSobolev (1/2)`, sends an order-one
  inhomogeneous datum to the order-`1/2` **homogeneous** datum of the mean-free
  part (torus copy of `R43/ForcePath.lean`).  Applied to lane 312's
  `T10.force_coefficient_path` it makes `b(t)` continuous on all of `ℝ`, so the
  primitive `N(t)=∫₀ᵗ b` is everywhere differentiable with `N'=b`
  (`intervalIntegral.integral_hasDerivAt_right`) — the force-path FTC was **not**
  the long pole.  Applied to `w.sobolev 1` it makes `y(t)` continuous on
  `Ico 0 T`, and `y(0)=0` from `w.initial`.  The scalar core is
  `Paper1.critical_norm_bound` on the clamped profile
  `ŷ s = y (min (max s 0) t)` (the scalar lemma needs `Continuous`, T11 gives
  only `ContinuousOn`), followed by a **second** pass through
  `Paper1.sqrt_energy_le_primitive` to upgrade `y ≤ ρ` into the paper's
  `y(t) ≤ ∫₀ᵗ b`.  The `∫₀ᵗ b ≤ ρ` half is U3 `bIntegral` plus
  `lintegral_mono_set Ioc_subset_Ioi_self`.
  Axioms `[propext, Classical.choice, Quot.sound]` for all 36 declarations.
  Probe `research/T20/probes/ybound_closes.lean`; audit
  `research/T20/axioms_u9.lean`; attempts `research/T20/ATTEMPTS_U9.md`.
- **U8 `criticalEnergy`** — DONE (lane 415).
  `Section3/T20/CriticalEnergy.lean`, theorem
  `NSFormalization.Section3.T20.criticalEnergy` (verbatim field type, with
  `C₀ = criticalTrilinearConst`).  No named input, no residual.
  The `y²` derivative is the T11 `hasDerivAt_torusSobolevNormAt_sq` template at
  the homogeneous order-`1/2` weight (`hasDerivAt_tsum_critFreqEnergy`); the
  pressure drop is T11's `freqEnergyDerivT_split` at order `0`
  (`rawEnergyDeriv_split`); the force term is `T11.torusRealPairing_le` on the
  order-`1/2` homogeneous data; the nonlinear term is lane 413's
  `criticalTrilinear_pairing`, reached through a new torus Parseval for the real
  `L²` pairing (`hasSum_periodicPairing`) and `T12.lambda_exists`.
  **U8 does not use U5**: the constant transport is dropped on the Fourier side
  (`re_sum_conj_fderiv_dir_zero`), because the physical skew route would need
  both U5 and self-adjointness of `Λ`, neither of which is in the tree.
  Axioms `[propext, Classical.choice, Quot.sound]` for all 21 declarations.
  Probe `research/T20/probes/critical_energy_closes.lean`; audit
  `research/T20/axioms_u8.lean`; attempts `research/T20/ATTEMPTS_U8.md`.
- **U10a `H¹` trilinear estimate** — DONE (lane 429).
  `Section3/T20/H1Trilinear.lean`, theorem
  `NSFormalization.Section3.T20.h1Trilinear`
  (`|⟪(v·∇)v,Δv⟫| ≤ C₁·y·laplacianSqT v`, the U10b `hOneEnergy` spelling) with
  `h1Trilinear_enorm` (`ℝ≥0∞` form, no finiteness hypothesis),
  `h1Trilinear_toReal` (`‖Δv‖₂²` written out), `h1Trilinear_pairing`
  (`periodicPairing` spelling) and `h1Trilinear_slice` (the `criticalY` /
  `laplacianSqT` slice form).  Explicit constant
  `h1TrilinearConst = CcriticalHalf * Csix`, with `h1TrilinearConst_pos`; this
  is the `C₁` U10b/U13 install.  Built on T12 U4 `velocityCriticalL3` (lane 401)
  and T12 U5 `gradientLSix` (lane 400), so **U10a is no longer blocked on T12**
  and U10b is unblocked on its analytic side.  The article's auxiliary Fourier
  step `‖∇(∂ⱼv)‖₂ ≤ ‖Δv‖₂` (`:475-477`) turned out to be internal to lane 400's
  `gradientLSix` and was not needed.  No named input.  Axioms
  `[propext, Classical.choice, Quot.sound]` for all 16 declarations.
  Probe `research/T20/probes/h1_trilinear_closes.lean` (nonzero witness
  `probeMZ`, plus the U10b slice shape check); audit
  `research/T20/axioms_u10a.lean`; attempts `research/T20/ATTEMPTS_U10A.md`.
  **Lead item, blocks U10b/U13 assembly:** `Section3/T12/GradientLSix.lean:184`
  and `Section3/T12/GradientLambdaL3.lean:210` both declare
  `NSFormalization.Section3.T12.contDiff_dirDeriv`, so no module can import both
  `GradientLSix` and `CriticalTrilinear` (which needs `GradientLambdaL3`).
  `H1Trilinear` therefore sits on the `GradientLSix` side and repeats four small
  lane-413 helpers under `…H1` names; U10b needs both sides, so the duplicate
  must be deleted upstream (lane-400's general version subsumes lane-405's).

## 0. Ground rules

**Peeling rule** (from T11/T15/T17). Every unit ends in a `theorem` whose statement **is** a
`CriticalRegularityTAPI` field verbatim (paper reference in the table) or a lemma **directly consumed** by
one. A unit that cannot close from the tree names **exactly one** non-tautological `def … : Prop` input in
`Section3/T20/`, satisfiable at a nonzero force, discharged by a named later unit. **No named input for the
hard analytic units** (U7, U8, U10a, U10b). A unit that needs a T12 embedding still being proved is marked
**blocked on T12 U4/U5/U6** (a real external dependency, not a Prop input) — do not fake it with a
finite-mode constant (`SECTION3_PLAN.md` §7; `PeriodicCriticalBridge`/`PeriodicFiniteCriticalInterface`
lose uniformity, forbidden).

**The T12 gate.** The reconciliation assembles the estimate constants inside the proof from three T12 fields
that are **not yet in the tree** — lanes 377→U4/U5/U6 of `research/T12/T12_SPLIT.md`, probe locations
`research/T12/probes/api_on_canonical.lean`:
`velocityCriticalL3` (`:148-151`, `‖v‖₃ ≤ C·‖v‖_{Ḣ^{1/2}}`, T12 U4),
`gradientLambdaCriticalL3` (`:170-175`, `‖∇v‖₃+‖Λv‖₃ ≤ C·‖v‖_{Ḣ^{3/2}}`, T12 U6),
`gradientLSix` (`:184-187`, `‖∇v‖₆ ≤ C·‖Δv‖₂`, T12 U5). The proved T12 fields are usable now:
`hTwo_le_laplacian` (`Section3/T12/FourierEmbeddings.lean:165`), `spectralGap`/`homogeneous_le_sobolev`
(`SpectralGap.lean`), `tameProduct` (`TameProduct.lean`), the `IsPeriodicLambda` / `lambdaCoeff` machinery
(`FourierEmbeddings.lean`).

**Transport vs new torus estimate** (the task's split). Section 4 solved `prop:Rcritical1/2` on `ℝ³` where the
mean is automatically zero; the torus adds a mean and a periodic geometry. Therefore:

- **Pure transport of the R43/R44 whole-space arguments through torus vocabulary** — reuse the domain-agnostic
  scalar/continuation machinery, only re-spell norms: **U9** `yBound` (the scalar bootstrap is
  `Paper1/ScalarEnergy.lean:147 critical_norm_bound`, whose `henergy` premise **is** `eq:criticalenergy`
  verbatim — this is the exact R43 S2 reuse), **U12** `globalRegularity` (the R44 S5 continuation, now through
  the proved T11 `periodicContinuationH3API`), and the constant-selection in **U13** (the R43
  `Section4/R43/Pieces.lean exists_critical_radius` pattern). The `y²`-differentiation, pressure drop, Λ/Δ
  symbol pairing and Grönwall/Young infrastructure that U8/U10 lean on is the torus copy already built in
  T11 `EnergyIdentity.lean`/`HighOrder.lean` — reused, at fractional/critical order.
- **Genuinely new torus estimates with no ℝ³ precedent** — the whole **mean reduction** (repository zero
  coverage per `SECTION3_PLAN.md`:11): **U1** `reductionRegular`, **U2** `meanBound` (`m'=ḡ`, `eq:meanbound`),
  **U3** `bIntegral`, **U6** `meanFreeEquation` (`eq:meanfree` keeps `(m·∇)v`); the constant-transport
  **U4** skew-adjointness and **U5** `Λ`-commutation (`:411`); the orthogonal constant/mean-zero `H²`
  decomposition in **U11**; and above all the **mean-zero critical trilinear estimates** **U7**
  (`|⟨(v·∇)v,Λv⟩| ≤ C₀ y z²`) and **U10a** (`|⟨(v·∇)v,Δv⟩| ≤ C₁ y ‖Δv‖²₂`) built on the T12 torus
  embeddings — these are the analytic core and the reason T20 is **L**.

**One reconciliation quirk.** The estimate constants are five **data fields** of the structure, selected
before `ν,g`; the two shrinkings `c_lt_C₀`, `c_lt_C₁` are fields. So no field mentions a raw T12 constant —
`C₀` is built in U7, `C₁`/`CH1` in U10, `Ccriterion` in U11, and `c = min(1/(4C₀),1/(4C₁))`-style in U13.

## 1. Units

The 12 non-mathematical fields (`c,hc,C₀,C₀_pos,C₁,C₁_pos,CH1,CH1_pos,Ccriterion,hCcriterion,c_lt_C₀,c_lt_C₁`)
are **not standalone targets**; they are set in the assembly U13 from the constants the estimate units
produce. The 11 mathematical fields split as follows.

- **U1 — `reductionRegular`** (new torus; §4 ①③⑧). New `Section3/T20/Reduction.lean`. Target: the field
  verbatim (`CriticalRegularity.lean:reductionRegular`, `:392-394,414-418,467-488`) — for every
  `w : ClassicalSolutionT ν 0 g T` and `t ∈ Ico 0 T`, `v(t)=meanFreeVelocity g w.velocity` and
  `h(t)=meanFreeForce g` are mean-zero smooth periodic, `v(t) ∈ Ḣ^{1/2}∩Ḣ^{3/2}∩H²`, `h(t) ∈ Ḣ^{1/2}`, and
  `∇v(t),Δv(t),h(t)` are `MemLp 2`. Route: subtracting the spatial constant `m(t)` (resp. `ḡ(t)`) preserves
  smoothness, periodicity, `div=0` and kills the zero mode (`IsMeanZeroT`); classical T10 slices +
  `T12.MemPeriodicHomogeneous`/`SmoothPeriodicT` supply the fractional `1/2,3/2` and `H²` memberships
  (the integer-smooth→fractional bridge ⑧); `MemLp 2` from `torusLift` of a bounded measurable smooth
  field on the probability torus (①). **M, codex-sol.** Deps: — (T10, T12 vocab). Unblocked.

- **U2 — `meanBound`** (new torus; §4 ⑤). New `Section3/T20/MeanBound.lean`. Target verbatim
  (`:meanBound`, `eq:meanbound` `:404-406`): for `g ∈ forceClassT`, `t ≥ 0`,
  `‖m(t)‖ ≤ meanForceIntegralT g t ≤ criticalRho g`. Route: `m'=ḡ`, `m(0)=0` give
  `‖m(t)‖ ≤ ∫₀ᵗ‖ḡ(s)‖`; the pointwise bound `|ḡ(s)| ≤ ‖g(s)‖_{H^{1/2}}` because the `k=0` Fourier weight is
  `1` (`Paper1/PeriodicMeanZeroEstimate.lean:71 one_le_periodicAngularMagnitude` reusable); integrate to
  `≤ forceSobolevENormT 1 (1/2) g = ρ`. **S–M, codex-sol.** Deps: — (uses T11 `mean_derivative`, proved).
  Unblocked.

- **U3 — `bIntegral`** (new torus; §4 ⑥). New `Section3/T20/BIntegral.lean`. Target verbatim (`:bIntegral`,
  `eq:bintegral` `:442-444`): `criticalBIntegral (meanFreeForce g) ≤ criticalRho g` for `g ∈ forceClassT`.
  Route: removing the zero mode is contractive on the inhomogeneous `H^{1/2}` datum path (`k=0` weight `1`),
  with a strongly measurable centered datum witness ⇒ `∫₀^∞‖h(t)‖_{Ḣ^{1/2}} ≤ ∫₀^∞‖g(t)‖_{H^{1/2}} = ρ`;
  mirror of R43's `forceHomogeneousENorm_le_forceSobolevENormL1` (`Section4/R43/ForcePath.lean`) but on the
  torus datum. **M, Opus.** Deps: —. Unblocked.

- **U4 — `constantTransportSkew`** (new torus; §4 ⑦). New `Section3/T20/ConstantTransport.lean`. Target
  verbatim (`:constantTransportSkew`, `:411`): for smooth periodic `v,w`,
  `⟪(m·∇)v,w⟫_{L²(T³)} = -⟪v,(m·∇)w⟫`. Route: periodic integration by parts on the probability torus —
  `(m·∇)` is a constant-coefficient first-order transport with `div m = 0`, so it is skew on `L²(T³)`; the
  two `Integrable` premises the manuscript field carries follow from `torusLift` boundedness (they are in the
  field only to protect the Bochner integral). **M, Opus.** Deps: —. Unblocked.

- **U5 — `constantTransportCommutesLambda`** (new torus; §4 ⑦). Same module. Target verbatim
  (`:constantTransportCommutesLambda`, `:411`): `IsPeriodicLambda v Lv →
  IsPeriodicLambda ((m·∇)v) ((m·∇)Lv)`. Route: on Fourier side `(m·∇)` is the multiplier `2πi(m·k)`, which
  commutes with the `Λ`-symbol `√(4π²|k|²)` coefficientwise; discharge via the T12 `lambdaCoeff` /
  `IsPeriodicLambda` graph (`FourierEmbeddings.lean:225,289`). **M, codex-sol.** Deps: —. Unblocked.

- **U6 — `meanFreeEquation`** (new torus; §4 ④). New `Section3/T20/MeanFree.lean`. Target verbatim
  (`:meanFreeEquation`, `eq:meanfree` `:408-410`): at interior `t`,
  `∂ₜv + advection v + (m·∇)v - ν•Δv + ∇p = h`. Route: differentiate the data-defined mean
  (T11 `PeriodicMeanReductionAPI.mean_derivative`, proved `Assembly.lean:412` / `MeanIdentity.lean:155`,
  gives `m'=ḡ`), use `w.momentum` (the `navierStokesResidual` spelling `ClassicalSolutionT` itself uses),
  the constant shift invariance of spatial derivatives, and `(u·∇)u = (v·∇)v + (m·∇)v`. **M, codex-sol.**
  Deps: — (consumes proved T11 `mean_derivative`). Unblocked.

- **U7 — mean-zero critical trilinear estimate** (new torus analytic core; §4 ⑨). New
  `Section3/T20/CriticalTrilinear.lean`. Target: the lemma consumed by `criticalEnergy` —
  `|⟪(v·∇)v, Λv⟫| ≤ C₀ · y(t) · z(t)²` for mean-zero smooth periodic `v`, with the explicit constant `C₀`.
  Route: Hölder `‖v‖₃‖∇v‖₃‖Λv‖₃`, then T12 `velocityCriticalL3` (`‖v‖₃ ≤ C·y`) and
  `gradientLambdaCriticalL3` (`‖∇v‖₃+‖Λv‖₃ ≤ C·z`) ⇒ `≤ C₀ y z²`, `C₀` a product of the two T12 constants.
  Torus analogue of R43 `Section4/R43/Trilinear.lean`/`TrilinearJ`, but through the T12 torus embeddings.
  **L, Opus. Blocked on T12 U4/U6.** No named input. Deps: T12 U4, T12 U6.

- **U8 — `criticalEnergy`** (new torus analytic core; §4 ⑨). New `Section3/T20/CriticalEnergy.lean`. Target
  verbatim (`:criticalEnergy`, `eq:criticalenergy` `:438-440`): `∃ E', HasDerivAt (fun s ↦ y(s)²) E' t ∧
  E'/2 + (ν - C₀ y(t)) z(t)² ≤ b(t) y(t)`. Route: differentiate `y² = ‖v‖²_{Ḣ^{1/2}}` (the order-`1/2`
  analogue of T11 `EnergyIdentity.lean:434 hasDerivAt_torusSobolevNormAt_sq`), pair `meanFreeEquation` (U6)
  against `Λv`: pressure drops (`div Λv = 0`, T11 `HighOrder.lean:312 torusPressureDrop`), constant transport
  cancels (U4 skew at `w = Λv`), dissipation gives `+ν z²`, nonlinear term is U7, force term
  `|⟪h,Λv⟫| = |⟪Λ^{1/2}h,Λ^{1/2}v⟫| ≤ b y`. Torus analogue of R43 `CriticalMomentum.lean`
  `rcritical1_of_classical'`. **L, Opus. Blocked on T12 U4/U6** (via U7). No named input. Deps: U4, U6, U7.

- **U9 — `yBound`** (transport of R43 S2; §4 ⑩). New `Section3/T20/YBound.lean`. Target verbatim
  (`:yBound`, `eq:ybound` `:454-458`): under `ρ < cν`, `y(t) ≤ ∫₀ᵗ b ≤ ρ` on all of `Ico 0 T`. Route:
  **reuse** `Paper1/ScalarEnergy.lean:147 critical_norm_bound` (`henergy` = U8's `eq:criticalenergy`,
  `hK : C₀·K ≤ ν/2` and `hρK : ρ < K` from `c < 1/(4C₀)` at `K = ν/(2C₀)`); supply the torus continuity of
  `t ↦ y(t)` (from T11 `HighOrder.lean:146 continuousOn_torusSobolevNormAt_velocity`) and the continuity/FTC
  of `N(t)=∫₀ᵗ b` (torus copy of R43 `ForcePath.lean` — `criticalB` slice continuity + interval
  integrability + primitive FTC). The `∫₀ᵗ b ≤ ρ` half is U3 restricted. **M, Opus** (scalar core is pure
  reuse; the critical-primitive FTC is the analytic residue). No named input. Deps: U8, U3. Blocked via U8.

- **U10a — mean-zero `H¹` trilinear estimate** (new torus analytic core; §4 ⑪). New
  `Section3/T20/H1Trilinear.lean`. Target: the lemma consumed by `hOneEnergy` —
  `|⟪(v·∇)v, Δv⟫| ≤ C₁ · y(t) · ‖Δv(t)‖²₂` for mean-zero smooth periodic `v`, explicit `C₁`. Route: Hölder
  `‖v‖₃‖∇v‖₆‖Δv‖₂`, T12 `velocityCriticalL3` (`‖v‖₃ ≤ C·y`) and `gradientLSix` (`‖∇v‖₆ ≤ C·‖Δv‖₂`), and
  `‖∇(∂_j v)‖₂ ≤ ‖Δv‖₂` by its Fourier series (`:475-477`). **L, Opus. Blocked on T12 U4/U5.** No named
  input. Deps: T12 U4, T12 U5.

- **U10b — `hOneEnergy`** (new torus analytic core; §4 ⑪). New `Section3/T20/H1Energy.lean`. Target verbatim
  (`:hOneEnergy`, `eq:H1energy` `:482-484`): under `ρ < cν`, `∃ E', HasDerivAt (fun s ↦ ‖∇v(s)‖²₂) E' t ∧
  E' + ν‖Δv(t)‖²₂ ≤ CH1·ν⁻¹·‖h(t)‖²₂`. Route: differentiate `gradientSqT` (T11 EnergyIdentity machinery at
  order 1), pair `meanFreeEquation` (U6) against `-Δv`: pressure/mean-transport vanish
  (`HighOrder.lean:312,345,367`), the convection term is U10a and is absorbed via `yBound` (U9, `y ≤ cν <
  ν/(4C₁)`) into `(ν/4)‖Δv‖²₂`, Young on the force term (T11 `HighOrder.lean:386 torusYoungAbsorb`) gives
  `CH1·ν⁻¹‖h‖²₂`. Sets `C₁`, `CH1`. Torus analogue of R44 `Absorption.lean`. **M–L, Opus. Blocked on T12
  U4/U5** (via U10a). No named input. Deps: U6, U9, U10a.

- **U11 — `continuationBound`** (orthogonal decomposition new + R44 S4 budget transport; §4 ⑫). New
  `Section3/T20/Continuation.lean`. Target verbatim (`:continuationBound`, `:490-500`): under `ρ < cν`, for
  `0 < S ≤ T`, `squaredHTwoIntegralT S w.velocity = meanModeCriterionIntegral S g w.velocity`, that quantity
  `≤ Sρ² + Ccriterion·ν⁻²·∫₀^∞‖h‖²₂`, and the bound `≠ ⊤`. Route: the orthogonal constant/mean-zero mode
  identity `‖u‖²_{H²} = |m|² + ‖v‖²_{H²}` (`k=0` weight `1`, **new torus**); `‖v‖²_{H²} ≤ C‖Δv‖²₂` by T12
  `hTwo_le_laplacian` (proved, `FourierEmbeddings.lean:165`); integrate U10b (`∫‖Δv‖²₂`) and U2 (`∫|m|² ≤
  Sρ²`); `∫₀^∞‖h‖²₂ < ∞` from `MemForceT` compact time support ⇒ `≠ ⊤`. Sets `Ccriterion`. Torus analogue
  of R44 S4 `Endpoint.lean maximal_h2TimeIntegral`. **M–L, Opus.** No named input. Deps: U10b, U2. Blocked
  via U10b.

- **U12 — `globalRegularity`** (transport of R44 S5; §4 ⑫). Same module. Target verbatim
  (`:globalRegularity`, `prop:critical` `:383-390`): under `ρ < cν`, `maximalLifespanT ν 0 g = ⊤`. Route
  (H1_CHECK §Consumer): from U11, `squaredHTwoIntegralT S u ≠ ⊤` for every `ofReal S ≤ maximalLifespanT`
  (monotone convergence to the unattained maximal lifespan + T11 maximality/uniqueness), then the **proved**
  T11 `periodicContinuationH3API.lifespanInfiniteOfLocallyFinite` (`Assembly.lean:318,379`) — the ball-free
  `H³` criterion suffices, `PeriodicRestartH1` is **not** a T20 obligation (H1_CHECK). Torus analogue of R44
  `Prop44.lean`/R43 `Endpoint.lean` S5. **M, codex-sol.** No named input (T11 API proved). Deps: U11.
  Blocked via U11.

- **U13 — assembly + constants + contract/bindings/tests + non-vacuity.** New `Section3/T20/Assembly.lean`
  + `Contracts/V1/…` (T20 registration, `T03.` umbrella per `SECTION3_PLAN.md:83`). Bundle the 23-field
  `CriticalRegularityTAPI`: set `C₀` (U7), `C₁`,`CH1` (U10), `Ccriterion` (U11), and `c := min(1/(4C₀),
  1/(4C₁))`-shrunk positive (the R43 `Pieces.lean exists_critical_radius` pattern) so `hc,c_lt_C₀,c_lt_C₁`
  hold; fill the 11 mathematical fields U1–U12; close `criticalRegularityStatement = Nonempty …`. Register,
  bind (`ClassicalSolutionT` structure exception: fieldwise, not `rfl`), test, non-vacuity at a nonzero
  compact-support force. **M, codex-sol.** Deps: all. Blocked via the estimate units.

## 2. Waves (≤ 2–3 concurrent per current lane cap)

| wave | units | sizes / models | gate |
|---|---|---|---|
| W1 | **U1** reductionRegular · **U2** meanBound · **U3** bIntegral · **U4** skew · **U5** Λ-commute · **U6** meanFreeEquation | M sol / S–M sol / M Opus / M Opus / M sol / M sol | **none — start now** |
| W2 | **U7** critical trilinear · **U10a** `H¹` trilinear | L Opus / L Opus | **T12 U4/U6** and **T12 U4/U5** (lanes 377) |
| W3 | **U8** criticalEnergy | L Opus | U4,U6,U7 |
| W4 | **U9** yBound · **U10b** hOneEnergy | M Opus / M–L Opus | U8 ; U6,U9,U10a |
| W5 | **U11** continuationBound · **U12** globalRegularity · **U13** assembly | M–L Opus / M sol / M sol | U10b,U2 ; U11 ; all |

All six mean-reduction/transport-foundation units (W1) are **unblocked** — the entire torus-new mean
machinery and the constant-transport `:411` fields can land before any T12 embedding does, off the critical
path. The critical path is **T12 U4/U6 → U7 → U8 → U9 → U10b → U11 → U12 → U13** (U10a joins at U10b).
Lane numbers allocated by the lead in `PLAN.md`.

## 3. Risks

1. **T12 embeddings U4/U5/U6 (highest, external).** `criticalEnergy`, `hOneEnergy` and thence
   `continuationBound`/`globalRegularity` cannot be **proved** until lanes 377→U4/U5/U6 register
   `velocityCriticalL3`/`gradientLSix`/`gradientLambdaCriticalL3`. W1 is entirely independent of them; start
   there. Never substitute a finite-mode constant (`PeriodicCriticalBridge` etc. lose uniformity —
   `SECTION3_PLAN.md` §7, `T12_SPLIT.md` §3).
2. **The mean reduction is repository-new (U1–U6).** `SECTION3_PLAN.md`:11 records zero coverage for
   `m'=ḡ`, `v=u-m`, skew/Λ-commutation. These are new but elementary; the leverage is T11's proved
   `PeriodicMeanReductionAPI.mean_derivative` and the `k=0`-weight-`1` spectral facts
   (`PeriodicMeanZeroEstimate.lean`). Keep `(m·∇)v` in `meanFreeEquation` (the reconciliation's untranslated
   reduction) — do not silently translate to the Galilean frame.
3. **yBound is transport, not a re-proof (U9).** The scalar bootstrap is done
   (`Paper1/ScalarEnergy.lean:147`); only the torus continuity of `y` and the FTC of the critical primitive
   `∫₀ᵗ b` are new. Resist re-deriving the `ζ↓0` first-crossing argument — reuse `critical_norm_bound`
   verbatim, exactly as R43 S2 reused it.
4. **Orthogonal `H²` decomposition (U11).** `‖u‖²_{H²} = |m|² + ‖v‖²_{H²}` is the one genuinely new
   continuation step (the `k=0` weight is `1`); the rest of `continuationBound` transports R44 S4. Prove the
   identity from Parseval on the torus, not by a norm inequality that leaks the constant mode.
5. **T11 continuation is the `H³` narrowing (inherited).** `globalRegularity` consumes only
   `lifespanInfiniteOfLocallyFinite` from the proved `periodicContinuationH3API` (H1_CHECK); it does **not**
   touch the open `PeriodicRestartH1`. If a later refactor routes U12 through the manuscript `restart`/
   `restartBeyond` from only an `H¹/H²` bound, that reopens the owner-level `H¹`-vs-`H³` gap and must be
   flagged, not silently discharged by changing order 1 to 3.

## Implementation candidates (both COMPARISONs, deduped; none imported by the spec)

- `Paper1/PeriodicCriticalRegularity.lean`: `CriticalRegularityCertificate` (structure `:63`),
  `exists_critical_regularity_constant` (`:72`), `critical_regular_ball` (`:81`),
  `paper1_main_with_critical_interfaces` (`:99`), `paper1_main_topological` (`:113`),
  `periodicVectorSobolevNorm_mono` (`:33`), `forceDistance_order_mono` (`:47`) — the target certificate named
  in `SECTION3_PLAN.md`:50, but a **consumer** shape (hides the analytic bridge in one `global_lifespan`
  field, old `TestForce`/`forceDistance`/`PeriodicLifespan.lifespan` vocabulary), not an implementation.
- `Paper1/CriticalEnergyCertificate.lean` + `CriticalEnergy{Coercivity,Derivative,Forcing,Signatures}.lean`:
  `CriticalEnergyCertificate` (structure `:16`), `norm_le_radius` (`:44`), `dissipation_coercive`
  (Coercivity `:15`), `absorbed_energy_inequality_on_interval` (Derivative `:8`), `energy_derivative_le`
  (Derivative `:21`), `forcing_work_le_radius` (Forcing `:10`), `dissipation_coefficient_nonneg` /
  `forcing_work_nonneg` / `norm_sq_initial` (Signatures `:8,17,25`) — the abstract scalar bootstrap for
  **U9/⑩**, all continuity/derivative hypotheses still to be supplied from the PDE (subsumed by the more
  general `Paper1/ScalarEnergy.lean` which U9 uses directly).
- `Paper1/PeriodicMeanZeroEstimate.lean`: `finite_meanZero_l2_le_homogeneousHalfEnergy` (`:18`),
  `finite_periodicFourier_meanZero_l2_le_homogeneousHalfEnergy` (`:50`),
  `finite_meanZero_l2_le_homogeneousHalfEnergy_one` (`:94`), `one_le_periodicAngularMagnitude` (`:71`),
  `exists_nonzero_coordinate` (`:62`) — finite-mode spectral gap after removing the zero coefficient;
  `one_le_periodicAngularMagnitude` is the reusable `k=0`-weight-`1` arithmetic for U2/U3/U11, but the
  finite-mode `lp`/physical statements are **not** the uniform field estimate (do not import as the embedding).
- No `Paper1/PeriodicSmallData*.lean` exists (grep empty).

## 4. Field → unit → §4-lemma map (for the assembler)

| field (`CriticalRegularity.lean`) | paper | unit | §4 item | class |
|---|---|---|---|---|
| `c,hc,C₀,C₀_pos,C₁,C₁_pos,CH1,CH1_pos,Ccriterion,hCcriterion,c_lt_C₀,c_lt_C₁` | `:383-384,430,471,479-481,497-499,457,477` | U13 (from U7/U10/U11) | — | transport (R43 radius) |
| `reductionRegular` | `:392-394,414-418,467-488` | U1 | ①③⑧ | new torus |
| `meanBound` | `eq:meanbound :404-406` | U2 | ⑤ | new torus |
| `meanFreeEquation` | `eq:meanfree :408-410` | U6 | ④ | new torus |
| `constantTransportSkew` | `:411` | U4 | ⑦ | new torus |
| `constantTransportCommutesLambda` | `:411` | U5 | ⑦ | new torus |
| `criticalEnergy` | `eq:criticalenergy :438-440` | U8 (←U7) | ⑨ | new torus (blocked T12 U4/U6) |
| `bIntegral` | `eq:bintegral :442-444` | U3 | ⑥ | new torus |
| `yBound` | `eq:ybound :454-458` | U9 | ⑩ | transport (Paper1 bootstrap) |
| `hOneEnergy` | `eq:H1energy :482-484` | U10b (←U10a) | ⑪ | new torus (blocked T12 U4/U5) |
| `continuationBound` | `:490-500` | U11 | ⑫ | new (orthogonality) + transport (R44 S4) |
| `globalRegularity` | `prop:critical :383-390` | U12 | ⑫ | transport (R44 S5 via T11 H³ API) |

## 5. Status log

- **U1/U2/U6 — DONE (lane 389, 2026-09-18).**
  `formalization/NSFormalization/Section3/T20/MeanReduction.lean` proves the
  canonical `reductionRegular`, `meanBound`, and `meanFreeEquation` fields
  verbatim, with no named residual input.  U1 uses the T11
  `periodicMeanReductionAPI.mean_formula` to identify the data-defined mean,
  then the smooth periodic/mean-zero and finite-norm bridges.  U2 uses the
  zero Fourier mode estimate and the interval integral bound, followed by the
  infimum defining `forceSobolevENormT`.  U6 uses T11
  `mean_formula`/`mean_derivative`, transport slice calculus, and subtraction
  of `forceMeanT` from the classical momentum equation.  The exact target
  probes are in `research/T20/probes/mean_reduction_closes.lean`; the axiom
  audit is in `research/T20/axioms_u1_2_6.lean`.  All three declarations print
  exactly `[propext, Classical.choice, Quot.sound]`.  No T12 critical embedding
  is needed and no residual remains for these units; U3/U4/U5 and later W1
  units remain open.
