# C01 source-to-target comparison

Task `collaboration/tasks/C01.md`; graph node `C01`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:275-281`), dependencies A02, A05,
consumers R43 and R44. Target: `research/C01/Spec.lean`,
`BlowupDensity.C01.Draft.EnergyAbsorptionAPI`.

Revised after `research/C01/REVIEW.md` (ACCEPT-WITH-NOTES); the per-finding
changes are in `research/C01/ATTEMPTS.md`.

Scope reminder: C01 owns **eq:RL2**, **eq:RH1** and the squared-`H²` assembly
(`paper/sections/04-whole-space.tex:107-131`, reused at `:171`). It does not own
eq:Rcritical1, eq:Rcritical2, the Grönwall of Proposition 4.4, the continuity
bootstrap of Proposition 4.3, or the continuation criterion (A04).

---

## 1. Field-by-field table

Domains: **cpt** = whole space but the velocity slice is assumed compactly
supported; **jet** = whole space, `SmoothL2Field` (smooth with every Fréchet jet
in `L²`), no support hypothesis; **T** = torus; **scalar** = a real-variable
statement with no field in it.

| Spec field | paper location | existing declaration (name, file:line, domain, hypotheses) | mismatch / gap |
|---|---|---|---|
| `gradientL6 : GradientL6API` | `appendix-b-embeddings.tex:32`, `04-whole-space.tex:110-112` | **registered**: `BlowupDensity.Contracts.V1.GradientL6API`, `verification/Contracts/V1/GradientL6.lean:118`, clauses `hessianLaplacianIdentity` `:130` and `gradientLSix` `:138`; jet; discharged by `verification/Bindings/GradientL6.lean:42` over `NavierStokesR3.SmoothSobolevL6.smooth_eLpNorm_six_le` (`vendor/NavierStokesAndEuler/NavierStokes/R3/SmoothSobolevL6.lean:72`, jet, no support) | none. Carried whole, not restated. Its hypothesis `SmoothSquareIntegrableJets` is supplied by `velocityJets`. |
| `C₁`, `CRH1`, `CH2`, `Cassembly` (+ positivity) | `:110`, `:115`, `:123`, `:127-130` | `NSFormalization.Paper1.CriticalEnergyCertificate` (`formalization/NSFormalization/Paper1/CriticalEnergyCertificate.lean:16`) bundles `ν, C, K, ρ` the same way; scalar | shape precedent only. That certificate carries the **critical** coefficient `C` of eq:Rcritical1, not `C₁` of eq:RH1. |
| `velocityJets` | `02-preliminaries.tex:29-30` | **gap (open).** `Data.ClassicalSolutionR.sobolev` (`verification/Contracts/V1/Data.lean:643`) gives the *datum* form only. D01 unit L2 (`formalization/NSFormalization/Section4/D01/SmoothDatum.lean`, `research/D01/REVIEW_L2.md`) proves **jet ⟹ datum**; `verification/Contracts/V1/BoundedRepresentative.lean:71-74` records **datum ⟹ jet** as open | the direction C01 needs is the open one. Every real-valued Bochner integral in the contract, and every application of the registered `gradientLSix`, rests on this field. |
| `forceTimeRegularity` | `02-preliminaries.tex:17-19` eq:Rclasses; `04-whole-space.tex:171` | **gap.** `Data.MemForceR` (`Data.lean:544`) states `MemLp G 1`/`MemLp G 2` for the *Bochner datum path* `G : ℝ → RealVectorSobolev m`, not for the physical slices. Nearest in tree: `NSFormalization.Source.PacketEnergy.l2Sq_continuousOn` via `NavierStokesR3.CompactEnergy.l2Sq_continuousOn` (`vendor/.../R3/CompactEnergy.lean:289`), cpt | the continuity/integrability route in tree is the compact-support one; `F_R` forces have no compact support. Needs the datum-path-to-slice transport. The field is stated **locally** (slice `MemLp 2` at each `t ≥ 0`, plus continuity of `t ↦ ‖f(t)‖₂` on `Ici 0`); interval integrability on each `[0,t]` follows from the continuity and is not restated, and the *global* `(0,∞)` finiteness of `04-whole-space.tex:171` is `MemForceR`'s own datum-path content, not claimed here. |
| `energyIdentity` | `04-whole-space.tex:117` | `NavierStokesR3.CompactEnergy.energy_balance` (`vendor/.../R3/CompactEnergy.lean:202`), cpt, viscosity **one**; arbitrary `ν` in `NSFormalization.Source.PacketEnergy.energy_balance_viscosity` (`formalization/NSFormalization/Source/PacketEnergy.lean:53`), cpt. Time derivative: `NavierStokesR3.CompactEnergy.energy_hasDerivAt` (`:302`) and `hasDerivAt_energy_balance` (`:323`), cpt | **compact support is the mismatch**, and it is fatal: Section 4 velocities are `H^∞` on `R³`. The support-free replacements exist: `EulerLpTranslation.SmoothL2Field` integration by parts `field_directional_ibp` (`vendor/NavierStokesAndEuler/Euler/OrdinaryL2Integration.lean:33`), `OrdinaryViscousStability.laplacian_pairing` (`formalization/NSFormalization/Source/OrdinaryViscousStability.lean:32`, `⟨W,ΔW⟩ = −∑ᵢ‖∂ᵢW‖₂²`), time derivative `EulerOrdinarySobolev.wordEnergy_hasDerivWithinAt` (`vendor/NavierStokesAndEuler/Euler/OrdinaryWordTime.lean:86`), pressure `EulerMeanSolenoidal.gradientSpace`/`solenoidalSpace` (`vendor/NavierStokesAndEuler/Euler/MeanSolenoidalSpace.lean:50,58`) with `gradient_mem` (`vendor/NavierStokesAndEuler/Euler/OrdinaryPressureCancellation.lean:84`), transport `differenceRhs_pairing` (`vendor/NavierStokesAndEuler/Euler/OrdinaryH3Energy.lean:34`). None is assembled into a forced energy identity. |
| `energyDifferentialBound` | `04-whole-space.tex:117-121` | `NSFormalization.Source.PacketEnergy.work_le` (`:17`) and `pde_energy_inequality` (`:35`), cpt, `2√(‖f‖₂²)√(‖u‖₂²)` — literally this display; also `NavierStokesR3.CompactEnergy.energy_rate_le` (`:253`), cpt, Young form | same compact-support mismatch. Support-free replacement is one line: `MeasureTheory.L2.inner` Cauchy–Schwarz on `SmoothL2Field.toLp` plus `field_inner` (`OrdinaryL2Integration.lean:26`). |
| `l2Bound` (**eq:RL2**) | `04-whole-space.tex:118-121` | `NSFormalization.Paper1.sqrt_energy_le_primitive` (`formalization/NSFormalization/Paper1/ScalarEnergy.lean:22`), scalar — the paper's `(y²+ζ²)^{1/2}`, `ζ↓0` device verbatim (the proof's `δ` is the paper's `ζ`), with `E' ≤ 2b√E ⟹ √E ≤ N`. Consumed via `energy_add_dissipation_le_primitive_sq` (`:156`) by `PacketEnergy.packet_energy` (`:143`) | **partial.** `sqrt_energy_le_primitive` requires `hE0 : E 0 = 0` and `hN0 : N 0 = 0`; eq:RL2 starts at `‖u(0)‖₂ = ‖a‖₂`, which need not vanish. The generalization is small (replace the two by `Real.sqrt (E 0) ≤ N 0`; the antitone argument is unchanged) but it does not exist today. |
| `trilinearHolder` | `04-whole-space.tex:107-109` | **gap.** No three-factor Hölder `L³·L⁶·L²` in tree. Two-factor: `MeasureTheory.integral_mul_norm_le_Lp_mul_Lq` used at `PacketEnergy.work_le:17`. `L⁶` membership: `NavierStokesR3.SmoothSobolevL6.smooth_memLp_six` (`vendor/.../R3/SmoothSobolevL6.lean:133`), jet. `L³` membership: nothing direct | new. `MemLp (u t) 3` is obtainable elementarily by interpolation between `L²` (the jet class) and `L⁶` (`smooth_memLp_six`); **A05's `criticalRepresentative` is not needed** — see §3. Hypothesis is `SmoothSquareIntegrableJets` (**not** `MemHInfty`), matching the registered clause it feeds; `velocityJets` hands consumers both forms for the only fields it is applied to. |
| `trilinearAbsorbed` | `04-whole-space.tex:109-112` | derived from `trilinearHolder` by the **registered** `gradientL6.gradientLSix` (`GradientL6.lean:138`), whose hypothesis is `SmoothSquareIntegrableJets` | new, but the only new content is the substitution; no analysis. With the jet hypothesis the derivation closes on the registered clause alone — no general-purpose datum ⟹ jet bridge is smuggled in. |
| `laplacianSqENorm` | none — an internal conversion, not a manuscript display | **gap (bookkeeping).** `MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm` and `Real.sqrt` lemmas; the same `ℝ≥0∞`-to-`ℝ` step is done inline at `NSFormalization.Section4.I02.Energy.eLpNorm_two_eq_ofReal_sqrt` (`formalization/NSFormalization/Section4/I02/Energy.lean:87`) for `L²` slices | new as a field, trivial as mathematics. Added after review finding 2: without it the two `ℝ≥0∞` trilinear fields cannot be combined with the three real-valued enstrophy fields, and they would be documentary rather than load-bearing. Only the `L²` Laplacian factor needs to cross; the `L⁶` gradient factor is an intermediate that `gradientLSix` eliminates. |
| `enstrophyIdentity` | `04-whole-space.tex:107` | **gap.** Nothing in tree differentiates `‖∇u(t)‖₂²` in time for a forced solution. Closest: `EulerOrdinarySobolev.wordEnergy_hasDerivWithinAt` (`OrdinaryWordTime.lean:86`) gives `d/dt ∑_{n≤s}∑_w ‖∂^w u‖₂² = 2∑⟨∂^w u, ∂^w ∂_t u⟩`, jet, no support; taking `s = 1` minus `s = 0` isolates `d/dt‖∇u‖₂²`. Spatial half: `field_directional_ibp` (`OrdinaryL2Integration.lean:33`) converts `∑ᵢ⟨∂ᵢu, ∂ᵢ∂_tu⟩` into `−⟨Δu, ∂_tu⟩` | new assembly of existing support-free pieces; see §2(b). |
| `enstrophyDifferentialBound` (**eq:RH1**) | `04-whole-space.tex:113-116` | **gap.** `NSFormalization.Paper1.critical_energy_absorption` (`ScalarEnergy.lean:68`) is the analogous scalar absorption for **eq:Rcritical1** (`E'/2 + (ν−Cy)z² ≤ by ⟹ E'/2 + (ν/2)z² ≤ by`), scalar, threshold `ν/2` | wrong estimate and wrong threshold: eq:RH1 absorbs at `ν/4` and spends the other quarter on the Young step for `‖f‖₂‖Δu‖₂`, ending at `Cν^{-1}‖f‖₂²` rather than at `by`. The scalar step itself is `nlinarith`-sized. |
| `enstrophyIntegralBound` | `04-whole-space.tex:116` | `NSFormalization.Paper1.energy_add_dissipation_le_primitive_sq` (`ScalarEnergy.lean:156`) and `packet_energy_integral_bound` (`:197`), scalar — the same antitone-on-`Icc` pattern (`energy + ν∫dissipation ≤ primitive²`) | shape matches; the right-hand side differs (`‖∇a‖₂² + Cν^{-1}∫‖f‖₂²`, not a squared primitive), and the integrability conjunct has its own precedent in `PacketEnergy.packet_dissipation` (`:233`), cpt. |
| `sobolevTwoFourier` | `04-whole-space.tex:122-124` | **partial.** `NSFormalization.Source.AngularGradientIdentity.vectorAngularSobolev_succ` (`formalization/NSFormalization/Source/AngularGradientIdentity.lean:92`) is the exact weight identity `‖F‖²_{H^{s+1}} = ‖F‖²_{H^s} + ∑ᵢⱼ‖∂ᵢF_j‖²_{H^s}`, whole space — but **requires `HasCompactSupport F`** (through `angularSobolevSq_succ:81`). `critical_inhomogeneous_identity` (`:107`) is its `Y²+Z²` instance, which belongs to R44 | two mismatches: the compact support, and the norm object — `vectorAngularSobolevNorm` is a literal Fourier integral, whereas the contract's left side is D01's datum infimum `Data.sobolevENorm 2` (`Data.lean:189`). Applying the identity twice, plus the registered `hessianLaplacianIdentity` for `∑ᵢⱼ‖∂ᵢ∂ⱼu‖₂² = ‖Δu‖₂²` and one interpolation `∑ᵢ‖∂ᵢu‖₂² ≤ ‖u‖₂‖Δu‖₂`, is the route. |
| `h2TimeIntegral`, `h2TimeIntegralZeroDatum` | `04-whole-space.tex:125-131`; `research/section4/STATEMENTS.md:494-497`, `:604-606` | **gap.** No time-integrated `H²` bound in tree. The `ℝ≥0∞` lower-integral shape is D01's own (`Data.energyGradient`, `Data.lean:459`); the `L∞_tL²_x`/`L²_tL²_x` counterparts for the *correction* field are `NSFormalization.Section4.I02.Energy.energyEssSup_le` (`formalization/NSFormalization/Section4/I02/Energy.lean:103`) and `energyGradient_le` (`:140`), cpt | new. Assembly only: `l2Bound` + `enstrophyIntegralBound` + `sobolevTwoFourier` + `forceTimeRegularity`. |

### Objects reused unchanged, with no mismatch

* `Data.ClassicalSolutionR`, `initialClassR`, `MemForceR`, `MemHInfty`,
  `sobolevENorm` — the canonical D01 objects, quantified over verbatim.
* `Contracts.V1.gradientTensor`, `Contracts.V1.laplacian`, `Contracts.V1.lift`,
  `SmoothSquareIntegrableJets` — the registered A05 objects. Their agreement
  with the spacetime operators was **checked**, not assumed: with
  `slice u t = fun x => u (t,x)`,
  `gradientTensor (slice u t) x = Data.spatialGradient u t x`,
  `laplacian (slice u t) x = spatialLaplacian u t x` and
  `advection (lift (slice u t)) 0 x = advection u t x` are all `rfl`
  (scratch file, `lake env lean`, exit 0; deleted).
* `Contracts.V1.SmoothSquareIntegrableJets` is field-for-field
  `EulerLpTranslation.SmoothL2Field` (`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31-34`),
  so the whole `SmoothL2Field` library applies to the velocity slices once
  `velocityJets` is available. This is the single most important reuse fact for
  the implementation.
* `NSFormalization.Source.PacketEnergy.dissipation`-style quantity: the contract's
  `gradientSq` is the Frobenius `∫‖∇z‖²`, which equals
  `NavierStokesR3.CompactEnergy.dissipation` (`vendor/.../R3/CompactEnergy.lean:195`,
  `∑ᵢ∫‖∂ᵢu‖²`) pointwise; the bridge already exists as
  `NSFormalization.Section4.I02.Energy.eLpNorm_spatialGradient_sq`
  (`Section4/I02/Energy.lean:117`).

---

## 2. Which integration-by-parts and regularization steps are new

**(a) The compact-support barrier is the dominant finding.** Every whole-space
*forced energy* statement in tree — `CompactEnergy.energy_balance:202`,
`energy_rate_le:253`, `energy_hasDerivAt:302`, `hasDerivAt_energy_balance:323`,
`PacketEnergy.pde_energy_inequality:35`, `energy_balance_viscosity:53`,
`packet_energy:143`, `packet_dissipation:233` — assumes the velocity slice is
compactly supported, in one of two equivalent spellings. Four state it
literally as `HasCompactSupport (fun x => u (t,x))`
(`CompactEnergy.energy_balance:206`, `energy_rate_le:257`,
`PacketEnergy.pde_energy_inequality:39`, `energy_balance_viscosity:57`); the
other four use the two-hypothesis form `IsCompact K` together with
`∀ t ∈ Icc a b, tsupport (fun x => u (t,x)) ⊆ K`
(`CompactEnergy.energy_hasDerivAt:303-304`,
`hasDerivAt_energy_balance:325-328`, `PacketEnergy.packet_energy:145,149`,
`packet_dissipation:235,239`), which `CompactEnergy.slice_compact:279`
converts to the first. The distinction does not affect the conclusion. That hypothesis is correct for the
inserted packet (I01/I02/I03), which is compactly supported by construction, and
**false** for every field C01 talks about: `X_R = H^∞ ∩ L²_σ`
(`02-preliminaries.tex:12`) and the classical velocity are decaying, not
compactly supported, and `04-whole-space.tex:198` says explicitly that nothing
requires the whole-space velocity to be spatially compact. So none of those
eight theorems can be reused as stated, and cutting off with a spatial cutoff
would break the exact cancellations. The correct base is the support-free
`SmoothL2Field` layer, whose integration by parts
(`OrdinaryL2Integration.field_directional_ibp:33`, proved from
`integral_bilinear_fderiv_right_eq_neg_left_of_integrable` with no support) is
already used at scale by `OrdinaryViscousStability` and
`OrdinaryViscousUniqueness`. **This reorientation, not any single lemma, is the
main implementation decision.**

**(b) New integration-by-parts steps.** Three, all on `SmoothL2Field`:

1. `⟨∂_tu, −Δu⟩ = ½(‖∇u‖₂²)'`. In tree the two halves exist separately —
   the time half as `wordEnergy_hasDerivWithinAt` (`OrdinaryWordTime.lean:86`),
   the spatial half as `field_directional_ibp` — but never combined. This is the
   only genuinely new *differentiation-under-the-integral* step; the `L²` version
   of it is already packaged (`difference_energy_bound`,
   `OrdinaryViscousStability.lean:71`).
2. `⟨∇p, Δu⟩ = 0` for divergence-free `u`. In tree only the `L²` version
   `⟨∇p, u⟩ = 0` exists, as orthogonality of `gradientSpace` and
   `solenoidalSpace` (`MeanSolenoidalSpace.lean:50,58`) with `gradient_mem`
   (`OrdinaryPressureCancellation.lean:84`), or with compact support at
   `CompactEnergy.integral_pressure_energy_zero:176`. The `Δu` version needs
   `Δu ∈ solenoidalSpace`, i.e. that `Δ` commutes with `div` — routine, absent.
3. `⟨(u·∇)u, u⟩ = 0`. Exists only inside the *difference* pairing
   `differenceRhs_pairing` (`OrdinaryH3Energy.lean:34`), never as a standalone
   support-free lemma; `CompactEnergy.integral_transport_energy_zero:127` is the
   compact one. Specializing the former is adaptation, not new mathematics.

The nonlinear term of eq:RH1, `⟨(u·∇)u, Δu⟩`, is **not** integrated by parts at
all — the paper bounds it by Hölder. What is new there is the three-factor
Hölder inequality itself (no instance in tree) and the `L³` membership of the
velocity slice.

**(c) The regularized norm `(y²+ζ²)^{1/2}` and `ζ↓0`.** The device the paper
names at `04-whole-space.tex:100` and reuses for eq:RL2 at `:117` **already
exists** and is faithful: `NSFormalization.Paper1.sqrt_energy_le_primitive`
(`ScalarEnergy.lean:22`) regularizes by `√(E + δ²)`, proves the regularized
difference antitone, and lets `δ ↓ 0` through `le_of_forall_pos_le_add`. Its
docstring names the same manuscript role. Two adjustments are needed:

* **nonzero initial value.** It assumes `E 0 = 0` and `N 0 = 0`; eq:RL2 begins at
  `‖a‖₂`. Replacing both by `Real.sqrt (E 0) ≤ N 0` changes only the final two
  lines of that proof. This is the one *new regularization* item, and it is
  small.
* **no absorption hypothesis.** The packaged consumer `critical_norm_bound`
  (`ScalarEnergy.lean:123`) and `CriticalEnergyCertificate`
  (`CriticalEnergyCertificate.lean:16`) bake in `C*K ≤ ν/2`, which is
  eq:Rcritical1's bootstrap, not eq:RL2. eq:RL2 needs the bare
  `sqrt_energy_le_primitive` with the dissipation simply dropped
  (`critical_squared_derivative_bound`, `ScalarEnergy.lean:76`, is exactly that
  discard step). Do **not** route eq:RL2 through the certificate.

The paper's other two regularization/continuity devices — the continuity
bootstrap at `:103` (`continuous_bootstrap`, `ScalarEnergy.lean:85`, exists) and
the first-crossing argument of Proposition 4.4 — sit in R43 and R44, not C01.

**(d) Grönwall.** Not used by C01. `NavierStokesR3.ScalarEnergyBound.forced_gronwall`
(`vendor/.../R3/ScalarEnergyBound.lean:49`, `E' ≤ E + C`, `E 0 = 0` ⟹
`E ≤ C(e^t − 1)`) is the exact scalar shape of Proposition 4.4's
`Y(t)² ≤ C₃ν^{-1}e^{C₂νS}‖f‖²` — recorded here so R44 finds it, but it discharges
no C01 field. Likewise `linear_stability_within`
(`OrdinaryEulerL2Stability.lean:46`).

**(e) Torus material, for the record only.** `Paper1/PeriodicH2Uniform.lean`,
`Paper1/PeriodicCriticalRegularity.lean` and
`vendor/HeliCorgi/Formal/PeriodicClayEnergy.lean` are periodic; the last is an
explicit shear solution. None transfers: the whole point of Section 4's
separation of eq:RL2 from eq:RH1 is that `R³` has no spectral gap
(`04-whole-space.tex:4-5`), so the periodic low-frequency arguments are exactly
what must **not** be reused.

---

## 3. Bounded implementation split

Ten units. **S** ≈ a short proof over existing lemmas; **M** ≈ one new
assembly with real analytic content; **L** ≈ a genuinely open step.

| # | unit | size | discharges | depends on |
|---|---|---|---|---|
| U1 | **Datum ⟹ jet for velocity slices.** From `ClassicalSolutionR.sobolev` + `velocity_smooth`, produce `SmoothSquareIntegrableJets (slice u t)` and `MemHInfty (slice u t)` at every `t ∈ [0,T)` | **L** | `velocityJets` | D01 unit L2's **open** direction (`BoundedRepresentative.lean:71-74`); the converse is `Section4/D01/SmoothDatum.lean`. Nothing else in C01 can start before this. |
| U2 | **Force class to slices.** `MemForceR f` ⟹ `MemLp (slice f t) 2` and continuity of `t ↦ ‖f(t)‖₂` on `[0,∞)` (interval integrability on each `[0,t]` is then immediate and is not a separate obligation) | **M** | `forceTimeRegularity` | D01 `MemForceR` (`Data.lean:544`); same datum-to-physical transport as U1 but at fixed order `m = 0`, so it may fall out of U1's machinery. |
| U3 | **Evolution packaging.** Turn a `ClassicalSolutionR` on `[0,S] ⊂ [0,T)` into `Icc 0 S → SmoothL2Field Space` with `jetLp` continuity and the pointwise time-derivative hypothesis; put `u(t)` in `solenoidalSpace` and `∇p(t)` in `gradientSpace` | **M** | (infrastructure for U4, U7) | U1, U2; `MeanSolenoidalSpace.lean:50,58`, `OrdinaryPressureCancellation.lean:84`, `OrdinaryWordTime.lean:78`. This is the hypothesis package `OrdinaryViscousStability.difference_energy_bound:71` already consumes, so the shape is proven usable. |
| U4 | **`L²` energy identity and its Cauchy–Schwarz form.** `d/dt‖u‖₂² = 2⟨u,∂_tu⟩` at `s = 0`; transport and pressure cancellations; `laplacian_pairing` for the dissipation; `L²` Cauchy–Schwarz for `⟨u,f⟩` | **M** | `energyIdentity`, `energyDifferentialBound` | U3; `wordEnergy_hasDerivWithinAt:86`, `laplacian_pairing` (`OrdinaryViscousStability.lean:32`), `differenceRhs_pairing:34`, `field_inner` (`OrdinaryL2Integration.lean:26`). New IBP item 2(b)3 specialized. |
| U5 | **eq:RL2 by regularized division.** Generalize `sqrt_energy_le_primitive` (`ScalarEnergy.lean:22`) to `√(E 0) ≤ N 0`, then apply to U4 with the dissipation discarded | **M** | `l2Bound` | U2, U4. Scalar only; no PDE input beyond U4. |
| U6 | **Trilinear Hölder, absorption, and the `‖Δz‖₂²` conversion.** `MemLp z 3` by interpolation between the jet class (`L²`) and `smooth_memLp_six` (`SmoothSobolevL6.lean:133`); three-factor Hölder; then `gradientL6.gradientLSix`; plus the one-line `laplacianSqENorm` | **M** | `trilinearHolder`, `trilinearAbsorbed`, `laplacianSqENorm` | **`A05.gradient_l6` (registered)** only — the three fields are stated on `SmoothSquareIntegrableJets`, so U6 **does not depend on U1** and can be done first. Deliberately **not** A05's unregistered `CriticalEmbeddingAPI`: see "A05 dependency" below. |
| U7 | **Enstrophy identity.** `d/dt‖∇u‖₂²` from `wordEnergy_hasDerivWithinAt` at `s = 1` minus `s = 0`; one `field_directional_ibp` to reach `−⟨Δu,∂_tu⟩`; `⟨∇p,Δu⟩ = 0` (new, item 2(b)2) | **M** | `enstrophyIdentity` | U3; the two new IBP steps 2(b)1 and 2(b)2. |
| U8 | **eq:RH1 differential.** Apply `trilinearAbsorbed` to the velocity slice (jet form from U1), convert through `laplacianSqENorm`, absorb at threshold `ν/4`, Young `‖f‖₂‖Δu‖₂ ≤ (ν/4)‖Δu‖₂² + ν^{-1}‖f‖₂²` | **S** | `enstrophyDifferentialBound` | U1, U6, U7. Pure scalar arithmetic once the conversion is in hand; the analogue of `critical_energy_absorption` (`ScalarEnergy.lean:68`) at a different threshold. |
| U9 | **eq:RH1 integrated.** Antitone-on-`Icc` argument in the pattern of `energy_add_dissipation_le_primitive_sq` (`ScalarEnergy.lean:156`), plus interval integrability of `t ↦ ‖Δu(t)‖₂²` in the pattern of `packet_dissipation` (`PacketEnergy.lean:233`) | **M** | `enstrophyIntegralBound` | U2, U8. |
| U10 | **`H²` Fourier inequality and the assembly.** De-compactify `vectorAngularSobolev_succ` (`AngularGradientIdentity.lean:92`), identify its norm with `Data.sobolevENorm 2`, use the registered `hessianLaplacianIdentity` for `∑ᵢⱼ‖∂ᵢ∂ⱼu‖₂² = ‖Δu‖₂²` and one interpolation for `∑ᵢ‖∂ᵢu‖₂²`; then combine U5 and U9 over `(0,S)` | **L** | `sobolevTwoFourier`, `h2TimeIntegral`, `h2TimeIntegralZeroDatum` | U1, U5, U9; **`A05.gradient_l6`** (`hessianLaplacianIdentity`). |

Dependency order: **U6 is independent and can start immediately**; otherwise
U1 → {U2, U3} → {U4, U7} → {U5, U8} → U9 → U10, with U8 also waiting on U6.

### Dependency notes the DAG does not currently record

* **`A05.gradient_l6` (registered).** Consumed by U6 (`gradientLSix`) and U10
  (`hessianLaplacianIdentity`), both through the single structure field
  `gradientL6`, so no clause is restated and no constant is duplicated. Its
  hypothesis `SmoothSquareIntegrableJets` is the hypothesis the two trilinear
  fields now carry as well (review finding 1), and it is what U1 produces for
  velocity slices; the
  contract's own docstring (`GradientL6.lean:38-42`) already warns that a
  consumer holding `Data.MemHInfty` still needs that bridge, and C01 is the
  first consumer to actually take it on.
* **A05's unregistered critical embeddings
  (`research/A05/Spec.lean`, `CriticalEmbeddingAPI`).** C01 consumes **none** of
  them. This is a deliberate specification choice: the absorption hypothesis is
  written in `‖u(t)‖₃`, the factor Hölder actually produces, instead of in the
  manuscript's `y = ‖Λ^{1/2}u‖₂`. Converting `‖u‖₃ ≤ Cy` (R43,
  `04-whole-space.tex:93`) or `‖u‖₃ ≤ CY ≤ Cθν` (R44, `:171`) is
  `CriticalEmbeddingAPI.velocityCriticalL3`, and it belongs to the consumers,
  exactly as `research/section4/STATEMENTS.md:494` and `:604` book it. The
  practical consequence is that **C01 does not have to wait for A05's
  `Λ`-relation, `Ḣ^{1/2}` or `Ḣ^{3/2}` clauses to be registered**; only the
  already-registered gradient-`L⁶` clause gates it. The `L³` membership U6 needs
  is elementary interpolation, not `criticalRepresentative`.
* **A02.** `DEPENDENCY_GRAPH.md:60` gives `A02 → C01`, but **no field of
  `EnergyAbsorptionAPI` names `IsMaximalSolution`, `maximalLifespanR`,
  uniqueness or the restart lemma**: every clause is about a
  `ClassicalSolutionR` on a fixed horizon `T`, with `S ≤ T`. A02's solution
  notion enters only when R43 and R44 apply these estimates *to the maximal
  solution* and combine them with A04. So the edge is real at the theorem level
  and vacuous at the specification level; C01 can be implemented against D01
  alone. Recorded so the graph is not read as a blocker.
* **D01.** Beyond the canonical objects, C01 leans on the L-numbered units
  `Data.lean` books: **unit L2** (`Data.lean:487-491`, jet ⟺ datum) is U1 and is
  the gate; unit L3 (`:502`, `IsSolenoidal` vs the closed `L²` subspace) is what
  U3 needs to place `u(t)` in `solenoidalSpace`; unit L9 (`:623`, eq:Rpressure
  from `momentum` + `∇p ∈ L²`) is what U3/U7 need for the pressure cancellations.
  None of the three is proved today.

### Hardest unit

**U1**, and it is not C01's own mathematics: it is the open datum ⟹ jet
direction of D01 unit L2. Nothing in the contract — not one Bochner integral,
not one application of the registered `gradientLSix` — can be discharged without
it, and `research/D01/REVIEW_L2.md` confirms lane 020 closed only the converse.
If U1 is deferred, the honest fallback is to add
`SmoothSquareIntegrableJets (slice w.velocity t)` as a *hypothesis* to every
clause, which would push the obligation onto R43 and R44 unchanged; the contract
deliberately does not do that, so that the gap has one owner and one name.

Within C01's own scope the hardest is **U10**: the `H²` weight identity exists
only for compactly supported fields (`angularSobolevSq_succ`,
`AngularGradientIdentity.lean:81`) and only for the literal-Fourier norm
`vectorAngularSobolevNorm`, whereas the contract's left-hand side is D01's datum
infimum `Data.sobolevENorm 2`. Both mismatches have to be closed before the
`< ∞` that A04 consumes can be produced.
