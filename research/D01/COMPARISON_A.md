# D01 draft A: source-to-target comparison

Target file: `research/D01/DraftA.lean`, namespace `BlowupDensity.D01.DraftA`.
Typechecked with `lake env lean ../research/D01/DraftA.lean` from
`verification/` (exit 0, no warnings). Definitions only; no `sorry`, no
`axiom`, no theorem with mathematical content.

Paths are relative to the worktree root. Line numbers are the declaration
lines in the current snapshot.

## 1. Object-by-object table

| Paper object | Paper location | Lean term in DraftA | Status | Differences and risks |
|---|---|---|---|---|
| Spatial domain `R^3`, Euclidean metric | `01-introduction.tex`, `eq:NS` | `Space` (opened from `NavierStokes.ProblemStatement`, `vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:30`) | reused-exact | `EuclideanSpace ℝ (Fin 3)`; real Euclidean norm, so vector norms are already the manuscript's. |
| Real vector field on `R^3` (initial velocity `a`) | `01-introduction.tex`, `eq:NS` | `SpatialField := Space → Space` | new (alias) | Pure alias; no measurability or decay built in. |
| Real space-time vector field (`u`, `f`) | `01-introduction.tex`, `eq:NS` | `SpaceTimeField := VelocityField` (`ProblemStatement.lean:35`) | reused-exact | Time is the **first** coordinate, `ℝ × Space`; the manuscript writes `f(x,t)`. Order flip is a transcription hazard for every downstream binder. |
| Scalar pressure `p` | `01-introduction.tex`, `eq:NS` | `SpaceTimeScalar := PressureField` (`ProblemStatement.lean:36`) | reused-exact | — |
| One-sided time domain `[0,∞)` | `02-preliminaries.tex`, after `eq:Rclasses` | `forceTimeDomain := Ici (0:ℝ)` | new (alias) | Encodes "one-sided time derivatives at zero" as `ContDiffOn ... (Ici 0)` downstream. |
| Force time interval `(0,∞)` for norms | `01-introduction.tex`, before `eq:time-norms` | `forceTimeMeasure := positiveTimeMeasure` (`formalization/NSFormalization/Paper3/PositiveTemporalDensity.lean:11`) | reused-exact | `volume.restrict (Ioi 0)`; agrees with `Ici 0` up to a null set. |
| Angular Fourier transform `(2π)^{-3/2} ∫ e^{-ix·ξ} z` | `01-introduction.tex`, displayed `hat z(ξ)` on `R^3` | `NSFormalization.Source.angularFourier` (`Source/FourierConvention.lean:23`), integral form proved in `angularFourier_eq_integral` (`:27`) | reused-exact | Exactly the manuscript's normalization; the proof discharges the `2π` convention rather than assuming it. |
| Distributional angular transform | same | `NSFormalization.Paper3.angularFourierDistribution` (`Paper3/AngularFourierDilation.lean:172`) | reused-exact | Built as `angularDistributionDilation ∘ 𝓕`; injective (`angularFourierDistribution_injective`). |
| `H^s(R^3)` datum space | `01-introduction.tex`, displayed `H^s(R^3)` | `SobolevHilbert s = Lp ℂ 2 volume` (`Paper3/SobolevHilbertModel.lean:21`); realization `angularRealization s` (`Paper3/AngularFourierDilation.lean:176`) | reused-exact | The datum is `(1+|ξ|^2)^{s/2} hat z`; `angularRealization` reconstructs in the angular convention (`weightedAngularFourier_realization`). Range equals Mathlib `TemperedDistribution.MemSobolev s 2` (`Paper3/AngularSobolevClass.lean:91`). |
| Real data (`F(-ξ) = conj F(ξ)`) | `02-preliminaries.tex`, last paragraph of §2.2 | `RealSobolevHilbert s = realSubspace s` (`Source/RealSobolev.lean:118,121`), `IsRealFrequencyDatum` | reused-exact | Reality is `realSymmetry G = G`, i.e. conjugate reflection; literally the manuscript's clause. |
| Real Euclidean 3-vector Sobolev data | `01-introduction.tex`, "for vectors and tensors we sum the squared component norms" | `RealVectorSobolev s = Product (Fin 3) (RealSobolevHilbert s)` (`Paper3/RealVectorPositiveDensity.lean:15`) | reused-exact | `PiLp 2`, so the vector norm is Euclidean. **Contrast** `ForceDatum m = Fin 3 → SobolevHilbert (m:ℝ)` (`Paper3/AdmissibleForce.lean:16`), which is the sup norm — the reason draft A does *not* reuse `AdmissibleForce`/`RealAdmissibleForce` verbatim. |
| Identification of a datum with a physical field | `01-introduction.tex` (Fourier is distributional) | `IsAngularDatum`, `IsAngularPath` | new | Modelled exactly on `angularRealVectorSlice_pairing` (`Paper3/AngularRealVectorBochner.lean:54`). Pairing is `∫ ψ(x) · z(x)_i`, a genuine Bochner integral for `z ∈ L^2`, `ψ` Schwartz. Risk: for `z ∉ L^1_loc ∩ L^2` the integral is Lean's totalized junk value; harmless inside `MemDatumR`/`MemForceR` where the `m = 0` clause forces `L^2`. |
| `X_R = H^∞(R^3;R^3) ∩ L^2_σ(R^3)` | `02-preliminaries.tex`, `eq:Rinitial` | `MemDatumR`, `datumClassR` | new | `H^∞` = an order-`m` angular datum for every `m : ℕ`; `L^2_σ` = pointwise Euclidean divergence zero (as in `Paper1/PeriodicInitialData.lean:21`). **Risks:** (a) pointwise vs distributional solenoidality — equivalent for smooth `L^2` fields, unproved here; (b) the Fréchet topology of `H^∞` is *not* attached (`eq:Rinitial` only fixes the set, and Theorem `thm:Rmain` topologizes only the force side); (c) `ContDiff ℝ ∞ a` is added, which the manuscript gets free from Sobolev embedding — a redundancy, not a strengthening. |
| `F_R` | `02-preliminaries.tex`, `eq:Rclasses` | `MemForceR`, `forceClassR` | reused-with-adaptation of `RealAdmissibleForce` (`Paper3/RealAdmissibleForce.lean:15`) | Same four clauses (`realization`, `ContDiffOn ℝ ∞ · (Ici 0)`, `MemLp · 1`, `MemLp · 2`) at every integer order, but: Euclidean instead of sup vector norm; angular instead of cycles realization; physical field instead of an abstract `ForceDistribution`; reality automatic instead of a fifth field. **Risks:** the manuscript's finiteness is `‖f‖_{L^1_tH^m} + ‖f‖_{L^2_tH^m} < ∞`, here two `MemLp` clauses, which additionally demand strong measurability of the path — the same convention the paper's Bochner footnote adopts. |
| `F_c = C_c^∞(R^3×(0,∞);R^3)` | `04-whole-space.tex`, §4.5 | `MemForceCompactR` | reused-exact | `CompactPositiveTimeSupport` (`vendor/.../R3/ProblemStatement.lean:66`) is exactly "compact support inside `t > 0`". `F_rd` and `S_σ` are **not** defined (not on the D01 deliverable list). |
| `‖z‖_{H^s(R^3)}` (scalar) | `01-introduction.tex`, displayed norm | `NSFormalization.Source.angularSobolevNorm` (`Source/FourierConvention.lean:47`) | reused-exact | Complex-valued argument; real fields enter as `(z x : ℂ)`. |
| `‖z‖_{H^s(R^3)}` (vector) | `01-introduction.tex`, "sum the squared component norms" | `angularVectorSobolevSq`, `angularVectorSobolevNorm` | new | Sum of three scalar squares. Risk: for `z ∉ H^s` the Bochner integral is junk `0`, so the *value* is only meaningful under a membership hypothesis. |
| `‖f‖_{L^q(0,∞;H^s)}`, physical form | `01-introduction.tex`, `eq:time-norms` | `forcePhysicalTimeNorm` | new | Literal `(∫_0^∞ ‖f(t)‖_{H^s}^q dt)^{1/q}` as a lower Lebesgue integral in `[0,∞]`; this is the form used by `eq:RpositiveScale`/`eq:RnegativeScale`. Risk: inherits the junk-value caveat above; `q` is a real exponent with no `1 ≤ q` guard. |
| `‖·‖_{L^q(0,∞;H^s)}`, Bochner form | `01-introduction.tex`, `eq:time-norms` + Hunter footnote | `forceBochnerNorm`, `forceBochnerNormL1`, `forceBochnerNormL2` | reused-exact (Mathlib `eLpNorm` on `positiveTimeMeasure`) | Same norm already used by `exists_angular_real_vector_positive_physical_approx` (`Paper3/AngularRealVectorBochner.lean:120`). **Gap:** agreement of `forceBochnerNorm` with `forcePhysicalTimeNorm` under `IsAngularPath` is unproved (unit L4 below). |
| `s_q = 2/q − 3/2` | `04-whole-space.tex`, Theorem `thm:Rmain` | `criticalOrder` | new (thin) | `NSFormalization.Paper3.forceExponent q s = criticalOrder q − s` (`Paper3/Thresholds.lean:12`) is already registered as V1 contract `R41.threshold_arithmetic`. Not re-derived here. |
| `‖z‖_{\dot H^s}` | `01-introduction.tex`, homogeneous weights `|ξ|^{2s}` | `angularVectorHomogeneousSq`, `angularVectorHomogeneousNorm` | new | Angular analogue of `NSFormalization.Source.homogeneousFourierNorm` (`Source/TimeNormScaling.lean:68`), which is in Mathlib's cycles convention. **Risk:** the two differ by `frequencyUnit^{...}` factors that must be tracked when reusing the existing scaling lemmas (`compact_homogeneous_norm_bound`, `Paper3/HomogeneousRealization.lean:17`). |
| `\dot H^{-1}(R^3)` realization | `02-preliminaries.tex`, `eq:homogeneous-realization` | `IsHomogeneousNegOneDatum`, `MemHomogeneousNegOne`, `homogeneousNegOneNorm` | new | Transcribes the displayed set *and* the displayed temperedness estimate: the datum is `G = |ξ|^{-1} hat h ∈ L^2` and the realization is fixed by pairing `angularFourierDistribution U ψ = ∫ ψ(ξ)|ξ|G(ξ)`. **Deliberately no multiplier CLM:** `ξ ↦ |ξ|^{-1}` has no temperate growth, so `TemperedDistribution.smulLeftCLM` cannot build `L^2 → 𝓢'`; `Paper3/HomogeneousRealization.lean` says the same ("A full `L² → 𝓢'` homogeneous multiplier is intentionally not introduced here"). Consequences: isometry and bijectivity onto `L^2` are unproved (units L6, L7). |
| `E_T` | `01-introduction.tex`, `eq:Enorm` | `energyEssSup`, `spatialGradient`, `energyGradient`, `energyNorm` | new | `essSup` over `Ioo 0 T` of the spatial `L^2` norm, plus the `L^2_t L^2_x` norm of the gradient. `spatialGradient` assembles `(∂_1 z, ∂_2 z, ∂_3 z)` in `WithLp 2`, so its norm is Hilbert–Schmidt — **not** the operator norm of `spatialDerivative`, which would be a different (equivalent but unequal) quantity. No endpoint value at `T`, as the paper says. |
| Classical solution `(u,p)` on `[0,T)` | `02-preliminaries.tex`, §2.1 and §2.3; `prop:local` | `ClassicalSolutionR` | new; adaptation of `SmoothLifespan.Flow` (`Source/SmoothLifespan.lean:23`) | Differences from `Flow`: (a) all-order continuous Sobolev path `C([0,S];H^m)` instead of uniform pointwise velocity/derivative bounds and `UniformFiniteEnergy`; (b) an explicit `MemLp 2` pressure gradient instead of no pressure condition; (c) same `navierStokesResidual ν` and same `Ico 0 T ×ˢ univ` one-sided smoothness. **Risks:** the equation is imposed on `Ioo 0 T` (interior times), matching the existing source convention, so the `t = 0` equation is only a limit; classical uniqueness is *not* a field, so `maximalLifespanR` is a supremum, not a chosen solution. |
| Pressure gauge (`p` up to a function of time) | `02-preliminaries.tex`, §2.3 after `eq:Rpressure` | `PressureGaugeEquiv` | new | Exactly "differ by `c(t)`". `∇p ∈ L^2` is a field of `ClassicalSolutionR`; no requirement `p ∈ L^2`. **Gap:** invariance of `ClassicalSolutionR` under the gauge is unproved (unit L8). |
| `∇p = (I−P)(f − ∇·(u⊗u))` and its potential | `02-preliminaries.tex`, `eq:Rpressure` and the displayed `p(x,t) = ∫_0^1 G(rx,t)·x dr` | `radialPressurePotential` | new | The potential formula is transcribed verbatim (`intervalIntegral` over `r ∈ [0,1]`). The Leray form `(I−P)(…)` is **not** encoded: it needs the Leray projector. Available externally as HeliCorgi `MNS2.r3HelmholtzPressure` / `r3HelmholtzPressure_gradient` (`vendor/HeliCorgi/Formal/R3HelmholtzPressure.lean`), which proves `∇p = −(I−P)F` for an arbitrary `L^2` source — but HeliCorgi is Lean/Mathlib 4.32.1 and cannot be imported (this project is 4.34.0-rc2), and it is in the cycles convention `e^{-2πi⟨x,ξ⟩}`. Encoded here instead by: momentum equation + `∇p(t) ∈ L^2` + gauge equivalence, which is equivalent for classical solutions. |
| `T^ν_{max,R}(a,f)` | `02-preliminaries.tex`, §2.1; used in `thm:Rmain`, `thm:Rinsert`, `prop:Rcritical1/2` | `maximalLifespanR` | reused-with-adaptation of `SmoothLifespan.lifespan` (`Source/SmoothLifespan.lean:41`) | Same `⨆ T, ⨆ _ : Nonempty (…), ENNReal.ofReal T` shape, over `ClassicalSolutionR` instead of `Flow`. Valued in `ℝ≥0∞`, so global regularity is `⊤` and the paper's `T^ν_{max,R}(a,f) = ∞` of `prop:Rcritical1` is literal. **Risk:** without a local-existence theorem the empty supremum is `0`, so `≤ T` is vacuously true for inadmissible data; every downstream statement must carry `MemDatumR`/`MemForceR`. |
| "regular through `T`" | `02-preliminaries.tex`, §2.1 | `RegularThrough` | new | `∃ δ > 0`, a classical solution on `[0, T+δ)`. The paper says "extends smoothly to `[0,T+δ]`"; the half-open form on `T+δ` is equivalent after shrinking `δ`. |
| `B^R_{ν,a,T}` | `02-preliminaries.tex`, `eq:Rsingularforces` | `breakdownSetR`, `breakdownSetRZero` | new | Literally `{f ∈ F_R : T^ν_{max,R}(a,f) ≤ T}`; the `MemForceR` conjunct keeps it inside `F_R`. |
| Relative `L^q(0,∞;H^s)` density on `F_R` | `04-whole-space.tex`, Theorem `thm:Rmain` (i)/(ii) | `RelativelyDenseInForceR`, `BreakdownDenseR` | new | The `ε`-form used at the start of the proof of `thm:Rmain`. The difference `f − g` is required to *have* an order-`s` angular path, and that path's Bochner norm is what is small; the path is unique because `angularRealization` is injective. **Risks:** (a) this is density of `B` in `F_R` for the relative topology, not density in the completion (that is `prop:Renergy`, out of scope here); (b) the manuscript reads the topology on `F_R` as a *relative norm* topology, so a metric formulation is faithful; (c) `s` is unrestricted real, `q : ℝ≥0∞` unrestricted — the theorem's `q ∈ {1,2}` is a hypothesis of the theorem, not of the definition. |

## 2. Cross-cutting risk register

1. **Fourier `2π`.** Everything in the draft goes through `angularFourier` /
   `angularRealization`. Every *existing* estimate in the repository that uses
   Mathlib `𝓕` (`fourierSobolevSq`, `homogeneousFourierNorm`,
   `compactSobolevTimeSlice`, all of `Source/TimeNormScaling.lean`) is in the
   cycles convention and transports with the factor `frequencyUnit^{|s|}`
   proved in `angularSobolevNorm_equivalence`
   (`Source/FourierConvention.lean`) — an *equivalence*, not an identity, at
   the level of inhomogeneous norms, and an *identity up to `(2π)^{3/2+s}`* at
   the level of homogeneous norms. Any binding that silently swaps the two
   conventions is wrong.
2. **Real vs complex.** Frequency data are complex `Lp ℂ 2`; reality is the
   closed real subspace `realSubspace`. The Euclidean vector norm is `PiLp 2`
   over that real subspace. The existing `AdmissibleForce`/`RealAdmissibleForce`
   pair uses the *sup* norm on `Fin 3 →`; norms therefore differ by a factor in
   `[1, √3]` and no isometry holds.
3. **`(0,∞)` vs `[0,T)`.** Force norms use `Ioi 0`; solution regularity uses
   `Ico 0 T`; solution smoothness at `0` is one-sided. `positiveTimeMeasure`
   ignores `t = 0`, but `IsAngularPath` and `ContDiffOn … (Ici 0)` do not: the
   `t = 0` value of a force is part of the data, as `eq:Rclasses` demands
   ("whole-space forces may be nonzero at zero").
4. **One-sided `t = 0` regularity.** Encoded only as `ContDiffOn ℝ ∞ · (Ici 0)`
   (forces) and `ContDiffOn ℝ ∞ · (Ico 0 T ×ˢ univ)` (velocity/pressure). The
   *equation* is imposed on `Ioo 0 T` only, following the existing source
   convention (`Flow.equation`, `CandidateProperties.navier_stokes`). If the
   lead wants the equation at `t = 0` with one-sided time derivative, that is a
   deliberate strengthening and must be decided before A01 binds to this.
5. **Pressure gauge.** `ClassicalSolutionR` carries a concrete `pressure`
   field, so two solutions differing by `c(t)` are two distinct terms. All
   downstream uniqueness statements must be modulo `PressureGaugeEquiv`.
6. **Distributional vs classical.** `IsAngularDatum` is a *distributional*
   identification (pairing with Schwartz tests) of a *classical* field. This is
   what makes negative-order `H^s` meaningful for smooth forces and is the same
   device as `angularRealVectorSlice_pairing`. The junk-value caveat on
   `∫ ψ · z` applies whenever the field is not locally integrable; inside
   `MemForceR` it never is, because the `m = 0` clause puts `f(t) ∈ L^2`.
7. **Lifespan without local existence.** `maximalLifespanR` is `0` when no
   solution exists at all. The pair (D01 spec, A01/A02 adapters) must supply
   local existence before `maximalLifespanR ν a f ≤ ENNReal.ofReal T` can be
   read as "breaks down by `T`" rather than "never started".

## 3. Bounded implementation split (≤ 10 units)

Each unit is one lemma-sized obligation that a registered V1 contract
(`structure … where` with obligation fields, in the style of
`verification/Contracts/V1/Thresholds.lean`) would carry. "Binds to" names an
existing declaration; "gap" means nothing suitable exists.

| # | Unit | Statement to discharge | Binds to / gap |
|---|---|---|---|
| L1 | Datum uniqueness | For fixed `s` and `z`, `IsAngularDatum s z A` determines `A`. | Binds to `NSFormalization.Paper3.angularRealization_injective` (`Paper3/AngularFourierDilation.lean`) plus injectivity of `PiLp` coordinates. |
| L2 | Compact smooth forces lie in `F_R` | `MemForceCompactR f → MemForceR f`. | Binds to `NSFormalization.Paper3.realAdmissibleForce_compactForceDistribution` (`Paper3/RealAdmissibleForce.lean:86`), `memLp_angularRealVectorSlice` and `angularRealVectorSlice_pairing` (`Paper3/AngularRealVectorBochner.lean:64,54`). Adaptation: sup-norm `ForceDatum` → Euclidean `RealVectorSobolev`. |
| L3 | `F_R` is an affine module | `MemForceR` closed under `+`, `−`, and `0`; and `MemForceR g → MemForceCompactR F → MemForceR (g+F)`. | Binds to `realAdmissibleForce_add/neg/sub/add_compact` (`Paper3/RealAdmissibleForce.lean:30,41,49,99`); needs the same proofs in the Euclidean-vector model. Required by `thm:Rinsert` ("their sum preserves membership in `F_R`"). |
| L4 | Physical norm = Bochner norm | `IsAngularPath s f G → forceBochnerNorm (ENNReal.ofReal q) s G = forcePhysicalTimeNorm q s f` for `1 ≤ q < ∞`. | Partial: `Source/FourierConvention.lean` gives the spatial identity `angularSobolevSq`; the fibrewise `‖G t‖ = angularVectorSobolevNorm s (f(t,·))` step is a **gap** (needs `‖·‖` of a `RealVectorSobolev` datum = weighted Fourier integral, for non-compactly-supported slices). |
| L5 | Sobolev monotonicity in `s` | `s ≤ r → ‖·‖_{H^s} ≤ ‖·‖_{H^r}` on the same datum, and hence `forceBochnerNorm q s ≤ forceBochnerNorm q r`. | **Gap** in the angular model. Needed by `thm:Rmain`'s converse (`H^s ↪ H^{1/2}` for `s ≥ 1/2`, `H^s ↪ H^{-1/2}` for `s ≥ −1/2`) and by the last step of the `thm:Rinsert` proof. |
| L6 | `\dot H^{-1}` realization is well posed | For every `G : FourierData` there is exactly one `U` with `IsHomogeneousNegOneDatum G U`. | **Gap** (existence is the temperedness estimate displayed in `eq:homogeneous-realization`; uniqueness is `angularFourierDistribution_injective`, `Paper3/AngularSobolevClass.lean:22`). |
| L7 | `\dot H^{-1}` isometry | `MemHomogeneousNegOne U` with datum `G` gives `‖U‖_{\dot H^{-1}} = ‖G‖`, and the map onto `L^2` is bijective. | **Gap**; the compact-input half is `compact_homogeneous_norm_bound` (`Paper3/HomogeneousRealization.lean:17`), which is a bound, not the isometry. |
| L8 | Pressure gauge invariance | If `S : ClassicalSolutionR ν T a f` and `PressureGaugeEquiv T S.pressure p`, the same velocity with pressure `p` is again a `ClassicalSolutionR` (needs `c` differentiable, or `pressureGradient` insensitivity on the slab). | **Gap**; elementary, but it is the formal content of "determined up to a function of time". |
| L9 | Pressure gradient from the Leray complement | `eq:Rpressure`: for a `ClassicalSolutionR`, `pressureGradient S.pressure t = (I−P)(f(t) − ∇·(u⊗u)(t))` in `L^2`, and `radialPressurePotential` is a representative. | **Gap in-tree**; the generic statement exists as HeliCorgi `MNS2.r3HelmholtzPressure_gradient` (`vendor/HeliCorgi/Formal/R3HelmholtzPressure.lean`, `∇p = −(I−P)F` for `F ∈ L^2`), but it is Lean 4.32.1, cycles convention, and cannot be imported (blocked on U05). |
| L10 | Lifespan interface | `maximalLifespanR ν a f ≤ ENNReal.ofReal T ↔ ∀ S > T, IsEmpty (ClassicalSolutionR ν S a f)`, plus restriction of a solution to a shorter horizon. | Binds to the proof pattern of `SmoothLifespan.lifespan_le_iff_no_extension` and `Flow.restrict` (`Source/SmoothLifespan.lean:58,83`); mechanical re-proof for `ClassicalSolutionR`. |

### Suggested contract shape

A `BlowupDensity.Contracts.V1.DataAndNormsAPI` would carry the eight required
objects as *fields of function type* (`datumClass`, `forceClass`,
`bochnerNorm`, `energy`, `lifespan`, `breakdown`, `dense`, `homogeneousNorm`)
together with the obligation fields L1–L3, L5, L10 (the ones with an existing
binding target) and would leave L4, L6–L9 to a later version, exactly as
`ThresholdAPI` restricts itself to threshold arithmetic and disclaims the PDE
content.
