# I02 — Local vector potential and smooth correction: source-to-target comparison

Draft specification: `research/I02/Spec.lean`, namespace `BlowupDensity.I02.Draft`,
structure `CorrectionAPI` (524 lines, typechecks clean, no `sorry`, no `axiom`,
no placeholder `Prop` field), plus the definitions `alpha`,
`scaledSpatialCutoff`, `scaledTemporalCutoff`, `scaledPacket` and the
existential form `correctionStatement`.

Target statements:

* Lemma 3.4, "A local divergence-free cutoff" (`lem:potential`),
  `paper/sections/03-torus.tex:176-216`, displays `eq:potential` (`:178-180`),
  `eq:cutoff` (`:183-187`), `eq:bgzero` (`:190-193`);
* Lemma 3.5, "Bounds for the background correction" (`lem:correction`),
  `paper/sections/03-torus.tex:218-285`, displays `eq:H` (`:220-224`),
  `eq:derivativebounds` (`:226-231`), `eq:wE` (`:234`), `eq:Hmixed` (`:235-237`);
* the reuse clause `paper/sections/04-whole-space.tex:23-29` and the first two
  paragraphs of Theorem 4.2's proof, `paper/sections/04-whole-space.tex:45-53`;
* the ledger's `R42` sub-claims consumed from `I02`,
  `research/section4/STATEMENTS.md:270-274`, and the two extra exports required
  by `research/section4/REVIEW.md:77-88` (divergence-freeness of `u_ε − v`, the
  compact pressure representative).

Explicitly out of scope (they belong to `I03`): `eq:HHs`
(`03-torus.tex:238-240`) and the whole-space Sobolev scaling
`eq:RpositiveScale`/`eq:RnegativeScale` (`04-whole-space.tex:63-78`).

Line numbers below were read in this worktree and are current as of commit
`4ba9f2b`.  Short names:

* `RP  = formalization/NSFormalization/Paper1/RadialPotential.lean`
* `LC  = formalization/NSFormalization/Paper1/LocalCutoff.lean`
* `TE  = formalization/NSFormalization/Paper1/TimeExtension.lean`
* `CP  = formalization/NSFormalization/Paper1/CorrectionProfile.lean`
* `CFP = formalization/NSFormalization/Paper1/CorrectionForceProfile.lean`
* `CE  = formalization/NSFormalization/Paper1/CorrectionEnergy.lean`
* `CMN = formalization/NSFormalization/Paper1/CorrectionMixedNorms.lean`
* `CVN = formalization/NSFormalization/Paper1/CorrectionVectorNorms.lean`
* `IE  = formalization/NSFormalization/Paper1/InsertionEnergy.lean`
* `INS = formalization/NSFormalization/Source/Insertion.lean`
* `LI  = formalization/NSFormalization/Source/LocalizedInsertion.lean`
* `PR  = formalization/NSFormalization/Source/PhysicalRemoval.lean`
* `IF  = formalization/NSFormalization/Source/InsertionFamily.lean`
* `PS  = formalization/NSFormalization/Source/PacketScaling.lean`
* `PSc = formalization/NSFormalization/Source/ParabolicScaling.lean`
* `SC  = vendor/NavierStokesAndEuler/NavierStokes/SpatialCurl.lean`
* `PST = vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean`

## 0. Domain audit: is the existing code torus or `ℝ³`?

`EXTERNAL_REUSE.md:37` files the reusable material under "Local
`Paper1/RadialPotential`, `LocalCutoff`, `CorrectionForceProfile`;
`Source/LocalApproximatingInsertion`", and `Paper1` is the *torus* paper.  The
directory name is not domain evidence, so every declaration cited below was
opened.  Result:

* `Space = EuclideanSpace ℝ (Fin 3)` (`PST:30`), `SpaceTime = ℝ × Space`
  (`PST:33`).  There is no quotient torus type anywhere in this chain.
* Every integral in `CE`, `CMN`, `IE` is `∫ x : Space, …` / `eLpNorm … volume`
  against Lebesgue measure on `ℝ³` (`CE:14-22`, `CMN:13`, `IE:26-32`,
  `vendor/.../R3/CompactEnergy.lean:190,195`).  Supports are `Metric.ball`
  (`PR:56-75`).
* The only periodicity in the chain is `UnitSpatialPeriodsOn` (`PST:47-50`),
  which appears in `Source/Insertion.lean`'s *unused* `CandidateProperties`
  (`INS` header comment) and in the `Paper1/Periodic*` files.  None of the
  declarations cited below mentions it; the torus transfer `lem:localization`
  lives in `Paper1/Periodic*` and is not on this path.

**Conclusion: the entire Euclidean content of Lemma 3.4 and of Lemma 3.5 (except
`eq:HHs`) is already proved for `ℝ³`, not only for the torus.**  What is missing
is (a) relaxing the *global-in-time* smoothness hypothesis on the reference to
the manuscript's `[0,T+δ]` regularity for the `ε`-family, (b) three small
assemblies (`E_T` norm, support measures, open-neighbourhood form of
`eq:bgzero`), and (c) packaging.  Section 3 below is precise about which.

Three definitional identifications were **machine-checked in this worktree**
(probe file `/tmp/i02probe.lean`, `lake env lean` exit 0), so the corresponding
`CorrectionAPI` fields are discharged by `rfl` / one `simp only`:

1. `RadialPotential.timePotential v x₀ (t,x) = ∫ ρ in 0..1, ρ • cross (v (t, x₀ + ρ•(x-x₀))) (x-x₀)` — `rfl`;
2. `physicalCorrection v x₀ T θ η ε z = -curl (fun y => (temporalCutoff η T ε z.1 * spatialCutoff θ x₀ ε y) • timePotential v x₀ (z.1,y)) z.2` — `simp only [physicalCorrection, localCorrection, spatialCurl]`;
3. `Source.correctionForce ν v w (t,x) = ∂_t w − ν Δw + Dv(w) + Dw(v) + (w·∇)w` — `rfl`;
   and `InsertionFamily.velocity U v x₀ T θ η ε z = v z + physicalCorrection … z + parabolicVelocity ε⁻¹ (T-ε²) x₀ (zeroPastField U) z` — `rfl`, so `scaledPacket` really is `U_ε`.

## 1. Field-by-field comparison

Column 3 names the existing declaration whose statement is the field (or the
declaration the field is one arithmetic step from); "gap" means nothing in the
tree states it.  Domains/hypotheses of the existing declaration are given
because the recurring mismatch is *global* vs *slab* smoothness of `v`.

| `CorrectionAPI` field (`Spec.lean:`) | Paper claim and location | Existing declaration (file:line), domain and hypotheses | Mismatch notes |
|---|---|---|---|
| `ν … margin_pos` (`:144-155`) | `ν, T > 0`, reference regular through `T+δ`, `04-whole-space.tex:32-33` | data only | The paper nests the margin ("regular through `T+δ` for some `δ>0`", risk note **O2** at `STATEMENTS.md:335-339`). The draft takes `δ` as given data, not re-existentialized. |
| `v, π, g`, `reference_smooth`, `reference_divergence_free`, `reference_equation` (`:159-181`) | "Fix a reference solution `(v,π,g)` smooth on `[0,T+δ]`", `03-torus.tex:164-165`; "smooth and divergence free in a spatial ball centered at `x₀`", `03-torus.tex:177` | `Source.residual` (`INS:21-23`) is the residual with explicit `ν`; no declaration packages a "reference" | Deliberate: no `D01` solution class, no `X_R`/`F_R`, no maximal solution. **Mismatch with every existing correction lemma**: they all require `hv : ContDiff ℝ ∞ v` *globally in spacetime* (`CP:141`, `PR:12,19,77`, `CFP:57`, `CE:42`, `CMN:123`, `LI:20`). The draft only assumes `ContDiffOn` on `Ioo 0 (T+δ) ×ˢ univ`. Bridge = split units 1–2. |
| `packet`, `carrier`, `carrier_compact`, `packet_support` (`:183-198`) | `supp U(·,σ) ⊆ K_*`, `01-introduction.tex:24-25`, `03-torus.tex:101-103` | `⟪I01:PacketAPI.velocity/carrier/carrier_compact/velocity_support⟫` (`research/I01/Spec.lean`); the same data appear as `CandidateProperties.support_compact`/`velocity_support` in `IF:103` | Restated as hypotheses rather than imported: `research/I01/Spec.lean` is not a module of the `NSFormalization` library, so it cannot be `import`ed from a research file. |
| `packet_divergence_free`, `packet_smooth`, `packetQuietTime`, `packet_quiet_pos`, `packet_quiet` (`:200-218`) | `∇·U = 0`, `U` smooth on `[0,1)×ℝ³`, `U = 0` on an initial interval — `01-introduction.tex:18-22`, `02-preliminaries.tex:152` | `⟪I01:PacketAPI.divergence_free/velocity_smooth/quietTime/quiet_pos/velocity_quiet⟫`; used in `IF:212-217` at the concrete value `τ = 3/8` | Needed **only** for `perturbation_divergence_free`; `zeroPastField_smoothOn` (`PS:373-377`) takes exactly `packet_smooth` + `packet_quiet`. |
| `x₀`, `r`, `radius_pos` (`:223-230`) | "fix any nonempty open ball `B ⊂ ℝ³`", `04-whole-space.tex:33`; `x₀ ∈ B`, `03-torus.tex:103` | `IF:196-200` uses exactly `x₀ : Space`, `r > 0`, `Metric.ball x₀ r` | Draft models `B` as `ball x₀ r` rather than an arbitrary ball plus `x₀ ∈ B`. This is clarification **C2** (`STATEMENTS.md:342-344`): any nonempty open ball contains a ball around the chosen centre, so nothing is lost, but the reduction is a deviation and is flagged in the field docstring. |
| `θ`, `theta_smooth`, `theta_compactSupport`, `plateau`, `plateau_open`, `carrier_subset_plateau`, `theta_one`, `θRadius`, `theta_support` (`:232-255`) | `θ ∈ C_c^∞(ℝ³)` equal to one on a neighbourhood of `K_*`, `03-torus.tex:181`; Urysohn construction `03-torus.tex:167-174`; "scaled support of `θ` strictly inside the coordinate ball", `03-torus.tex:212` | `LC.exists_spatial_cutoff` (`LC:14-27`): from `IsCompact K`, `0 < R`, `K ⊆ ball x₀ R`, produces `χ, O` with `ContDiff`, `HasCompactSupport`, `tsupport χ ⊆ ball x₀ R`, `IsOpen O`, `K ⊆ O`, `EqOn χ 1 O`. `ℝ³`, no extra hypotheses. Instantiated at `IF:233-235` | Convention difference: `exists_spatial_cutoff` centres the support ball at `x₀`; the draft (like `PR:56-63`) centres it at `0`, because `spatialCutoff θ x₀ ε x = θ(ε⁻¹•(x−x₀))` already carries the translation. `IF:224-232` supplies `tsupport θ ⊆ ball 0 R` via `hKallR`. Compatible. |
| `η`, `eta_smooth`, `eta_compactSupport`, `eta_one`, `eta_support` (`:258-268`) | `η ∈ C_c^∞((-2,2))` equal to one on `[-1,1]`, `03-torus.tex:181-182` | `LC.exists_temporal_cutoff T δ` (`LC:30-46`): `EqOn η 1 (Icc (T-δ) (T+δ))`, `tsupport η ⊆ Ioo (T-2δ) (T+2δ)`. At `T = 0, δ = 1` (`IF:236-238`) this is literally the paper's `η` | The concrete witness is a `ContDiffBump` with plateau radius `δ` and outer radius `3δ/2`, so its support is `closedBall 0 (3/2)`, strictly smaller than `(-2,2)`. Harmless (the field is an upper bound). |
| `ε₀`, `eps_pos`, `eps_le_one`, `eps_time`, `eps_space` (`:271-284`) | "for sufficiently small `ε`", `03-torus.tex:188`; `2ε² < min(T,δ)` and scaled `supp θ` inside the ball, `03-torus.tex:212`; `2ε² < T`, `x₀+εK_* ⊂ B`, `03-torus.tex:104-105` | `IF:239-244`: `ε₀ = min 1 (min (r/R) ((T-τ)/2))`, giving `ε*R < r` and `2ε² < T - τ` | The existing threshold uses `T - τ` (the packet quiet time) where the paper uses `min(T,δ)`; both are "sufficiently small". `ε₀ ≤ 1` matches the normalization under which all derivative constants are uniform (`CP:263`, `CFP:270` use `Ioc 0 1`). |
| `potential` (`:289`) | `A` of `eq:potential`, `03-torus.tex:178-180` | `RP.timePotential` (`RP:202-203`), `ℝ³`, no hypotheses to define | — |
| `potential_formula` (`:297-302`) | `A(x,t) = ∫₀¹ r v(x₀+ry,t) × y dr`, `03-torus.tex:179` | `RP.centeredPotential_eq_integral` (`RP:177-180`), and `timePotential` unfolds to it — **checked `rfl` in this worktree** | Exact match, including the cross product `RP.cross` (`RP:15-19`) and `y = x − x₀`. |
| `potential_smooth` (`:292-295`) | `A` smooth, implicit in `03-torus.tex:177-181` | `RP.timePotential_contDiff` (`RP:205-216`), hypothesis `hv : ContDiff ℝ ∞ v` **global** | Slab version missing; the parameter-integral lemma `Euler.CompactParameterIntegral.integral_contDiff` used at `RP:216` wants global `ContDiff`. Unit 1–3. |
| `potential_curl` (`:304-306`) | `∇ × A = v`, `03-torus.tex:181`, proved at `03-torus.tex:196-210` | `RP.curl_centeredPotential` (`RP:186-199`) for a spatial field, and `RP.spatialCurl_timePotential` (`RP:218-224`) for the spacetime field. `ℝ³`; hypotheses: `ContDiff ℝ ∞ v` and `∀ x, ∑ᵢ (Dv x eᵢ)ᵢ = 0` (**global**) | This is the *whole* mathematical content of the first half of Lemma 3.4 and it is fully proved, with the manuscript's own homotopy proof (`RP:103-175`: `curl_integrand`, `curl_potential_integral`, `radial_derivative`, FTC). Only the hypothesis shape differs: the slice version needs `SC.contDiff_spatialSlice` (`SC:147-150`) to go from the slab to `fun x => v (t,x)`. |
| `correction` (`:310`) | the family `ε ↦ w_ε` | `CP.physicalCorrection` (`CP:141-143`) `= localCorrection v x₀ (spatialCutoff θ x₀ ε) (temporalCutoff η T ε)`; `LC.localCorrection` (`LC:48-51`) | Exact. `spatialCutoff` (`CP:135-136`) is `θ(ε⁻¹•(x−x₀))` and `temporalCutoff` (`CP:138-139`) is `η((ε²)⁻¹(t−T))`: **the paper's `θ_ε, η_ε` verbatim** (`03-torus.tex:184-185`). |
| `correction_formula` (`:313-320`) | `w_ε = −∇×(η_ε θ_ε A)`, `03-torus.tex:186` | definitional — **checked in this worktree** by `simp only [physicalCorrection, localCorrection, spatialCurl]` | Exact. |
| `correction_smooth` (`:322`) | "`w_ε` is a smooth … field", `03-torus.tex:188` | `PR.physical_smooth` (`PR:12-17`), hypothesis `ContDiff ℝ ∞ v` **global**; also `CVN.physicalCorrection_smooth` (`CVN:14-20`) | Slab bridge only. |
| `correction_divergence_free` (`:325-326`) | "divergence-free", `03-torus.tex:188`; "its divergence vanishes because it is a curl", `:212` | `PR.physical_divergence` (`PR:19-23`), via `LC.localCorrection_divergence` (`LC:60-75`) and `SC.divergence_curl` | Slab bridge only. |
| `correction_compactSupport` (`:328`) | implicit in `03-torus.tex:188` | `PR.physical_compact` (`PR:47-54`); `CVN.physicalCorrection_compact` (`CVN:28-35`). Hypotheses: `ε ≠ 0`, `HasCompactSupport θ/η` only — **no smoothness of `v` needed** | Exact. |
| `correction_support` (`:333-336`) | "supported inside the coordinate ball and in `(T−2ε², T+2ε²)`", `03-torus.tex:188-189` | `PR.physical_support` (`PR:56-75`): `tsupport (physicalCorrection …) ⊆ Ioo (T−2ε²) (T+2ε²) ×ˢ ball x₀ (ε*R)`, hypotheses `0 < ε`, `HasCompactSupport θ/η`, `tsupport θ ⊆ ball 0 R`, `tsupport η ⊆ Ioo (-2) 2`. **Literally the draft's field** | Exact match, no `v` hypothesis at all. |
| `correction_support_ball` (`:338-341`) | "the velocity difference is supported inside `B`", `04-whole-space.tex:37-38` | `IF:128-131` (`hwloc`) derives exactly this from `physical_support` + `ε*R < r` + `Metric.ball_subset_ball`; slicewise via `LI.slice_support_projection` (`LI:155-159`) | One-line consequence. |
| `correction_vanishes_before` (`:343-346`) | `u_ε = v` for `t ≤ T − 2ε²`, `03-torus.tex:333-335`, `04-whole-space.tex:36` | `IF:173-176` (`hw0`) does exactly this from `hwloc` | One-line consequence of `correction_support`. |
| `correction_cancels` (`:348-352`), literal open-neighbourhood form of `eq:bgzero` | `v + w_ε = 0` on an open neighbourhood of `supp U_ε(t)`, `03-torus.tex:190-193` | `PR.physical_removes` (`PR:77-114`) gives it on `spaceMap ε x₀ '' O` for `t ∈ Icc (T−ε²) (T+ε²)`; `PS.delayed_full_support` (`PS:335-353`) puts `supp U_ε(t)` inside `scaledSupport ε⁻¹ x₀ K`; `IF:97-100` (`hscaledO`) connects them | **gap (small)**: nothing states that `spaceMap ε x₀ '' O` is open (it is, since `y ↦ x₀+ε•y` is a homeomorphism for `ε ≠ 0`) nor packages the two into the `∃ O` form. Split unit 5. |
| `correction_cancels_germ` (`:360-363`) | the germ form the cross-advection cancellation uses, `03-torus.tex:330`, `04-whole-space.tex:50` | `LI.background_removed_on_packet` (`LI:73-93`) composed with `PR.physical_removes`; the composition is written out at `IF:101-105` (`hcancel`) | Exact; the hypothesis shape is that of `INS.cross_advection_eq_zero` (`INS:53-68`). Requires `ContDiff ℝ ∞ v` **global** through `physical_removes`. |
| `correctionDerivConst`, `correctionDerivConst_nonneg`, `correction_derivative_bound` (`:367-380`) | `\|∂_t^j ∂_x^β w_ε\| ≤ C_{β,j} ε^{−2j−\|β\|}`, `03-torus.tex:227-228` | `CP.physical_mixed_derivative_bound` (`CP:291-322`): `∃ C ≥ 0, ∀ ε ∈ Ioc 0 1, ∀ p, ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) → ‖iteratedFDeriv ℝ (j+m) (physicalCorrection …) p (Fin.append (fun _ : Fin j => (1,0)) (fun i => (0, u i)))‖ ≤ C * (ε⁻¹)^(2j+m)`. **Identical shape.** Hypotheses: `ContDiff ℝ ∞ v` global, `θ,η` smooth with compact support | Two conventions to record: (i) the constant is `∃`-quantified there and *data* here (`choose`), which is what makes it manifestly `ε`-independent as `03-torus.tex:242` requires; (ii) the paper's multi-index `∂_x^β` becomes `m` directional derivatives along unit-ball vectors — the coordinate form follows by `u i = coordinateVector _`. |
| `forceCorrection` (`:382`) | `H_ε` | `INS.correctionForce ν v w` (`INS:92-96`) | Exact. |
| `force_formula` (`:387-395`) | `eq:H`, `03-torus.tex:220-223` | definitional — **checked `rfl` in this worktree** | Term order differs from the paper (`(w·∇)v` before `(v·∇)w`); sum identical. |
| `force_smooth` (`:398`) | "smooth across `T` and extends by zero", `03-torus.tex:225`; "globally smooth … including across `T`", `04-whole-space.tex:51` | `CVN.physicalForce_smooth` (`CVN:22-26`) via `LI.correctionForce_smooth` (`LI:20-30`), hypothesis `ContDiff ℝ ∞ v` **global** | Global `ContDiff` on all of `ℝ×ℝ³` *is* "smooth across `T`": there is no seam. Slab bridge only. |
| `force_compactSupport` (`:401`) | "spacetime compact", `03-torus.tex:225`, `04-whole-space.tex:51` | `CVN.physicalForce_compact` (`CVN:37-40`) via `LI.correctionForce_compact` (`LI:52-54`), which needs only `HasCompactSupport w` | Exact. |
| `force_support` (`:404-407`) | `supp H_ε ⊆ supp w_ε`, `03-torus.tex:225` | `LI.correctionForce_support` (`LI:45-50`) + `PR.physical_support` (`PR:56`) | Exact composition; `LI.correctionForce_eq_zero_outside` (`LI:33-43`) is the pointwise version. |
| `force_positive_time` (`:410-412`) | temporal support a compact subset of `(0,∞)`, `03-torus.tex:339`, `04-whole-space.tex:51` | `IF:118-127` (`hFloc`) does the analogous arithmetic for the packet force | Arithmetic from `force_support` and `eps_time` (`2ε² < T`). |
| `force_support_ball` (`:414-416`) | `g_ε − g ∈ C_c^∞(B×(0,∞))`, `04-whole-space.tex:38` | as `correction_support_ball` | One-line consequence. |
| `spatialVolumeConst`, `force_spatial_volume` (`:418-426`) | "its spatial support has volume `O(ε³)`", `03-torus.tex:225` | **gap**: no declaration measures the support. Ingredients: `force_support`, `LI.slice_support_projection` (`LI:155`), and Mathlib's `Measure.addHaar_ball` / `EuclideanSpace.volume_ball` | The `ε³` factor is proved *implicitly* elsewhere (`CE.energy_dilate_translate`, `CE:13-22`, extracts exactly `ε³` from a scaled integral), but never as a statement about `volume (supp H_ε)`. Split unit 7. |
| `force_time_length` (`:428-430`) | "its temporal support has length `O(ε²)`", `03-torus.tex:225` | **gap**, same as above; `Real.volume_Ioo` on `Ioo (T−2ε²) (T+2ε²)` gives `4ε²` | Split unit 7. |
| `forceDerivConst`, `forceDerivConst_nonneg`, `force_derivative_bound` (`:433-446`) | `\|∂_x^β H_ε\| ≤ C_β ε^{−2−\|β\|}`, `03-torus.tex:229-230` | `CFP.physicalForce_spatial_derivative_bound` (`CFP:270-296`): `∃ C ≥ 0, ∀ ε ∈ Ioc 0 1, ∀ p, ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) → ‖iteratedFDeriv ℝ m (correctionForce ν v (physicalCorrection …)) p (fun i => (0, u i))‖ ≤ C * (ε⁻¹)^(2+m)`. **Identical shape.** | Same two conventions as the `w_ε` bound. The underlying `ε⁻²`-amplitude representation is `CFP.physicalForce_eq_profile` (`CFP:185-205`), the exact analogue of `03-torus.tex:264-273`. |
| `energyConst`, `correction_energy_memLp`, `correction_energy_bound` (`:448-463`) | `‖w_ε‖_{E_T} ≤ Cε^{3/2}`, `03-torus.tex:234`, proved at `:275-281` | Both squared halves exist: `CE.physicalCorrection_uniform_energy` (`CE:54-71`) gives `∀ ε ∈ Ioc 0 1, ∀ t, ∫‖w_ε(t)‖² ≤ Cε³`; `IE.correction_gradientSquare_bound` (`IE:175-200`) gives `IntegrableOn (dissipation w_ε) (Ioo 0 T)` and `gradientSquare T w_ε ≤ Cε³`. `IE.energyNorm_le_of_squared_bounds` (`IE:107-122`) turns the pair into `MemLp … ∧ energyNorm T w_ε ≤ √A + √D` | **gap (assembly)**: nothing states `energyNorm T (physicalCorrection …) ≤ C ε^{3/2}`. Two steps remain: apply `energyNorm_le_of_squared_bounds`, then `√(Aε³) + √(Cε³) = (√A + √C)·ε^{3/2}`. `IE.energyNorm` (`IE:30-32`) is `‖velocityL2‖_{L^∞(Ioo 0 T)} + √(gradientSquare)`, the manuscript's `E_T`. Split unit 8. |
| `mixedConst`, `force_spatial_memLp`, `force_mixed_bound` (`:465-478`) | `‖H_ε‖_{L^q(0,∞;L^p)} ≤ C_{p,q} ε^{α(p,q)+1}`, `03-torus.tex:235-237` | `CMN.physical_force_mixed_bound` (`CMN:123-161`): `∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ε ∈ Ioc 0 1, mixedNorm p q (correctionForce ν v (physicalCorrection …)) ≤ ENNReal.ofReal (ε^(-2 + 3/p.toReal + 2/q.toReal)) * C`, for **all** `p q : ℝ≥0∞` including the two `∞` endpoints. `CMN.physical_force_spatial_memLp` (`CMN:164-186`) gives the slicewise `MemLp` | Three conventions: (i) `-2 + 3/p + 2/q = α(p,q)+1` — **checked by `ring` in this worktree**; (ii) the constant is `ℝ≥0∞`-valued and finite there, real-valued here (`ENNReal.ofReal_toReal`); (iii) **`CMN.mixedNorm` (`CMN:13-14`) integrates the time variable over all of `ℝ`, the paper over `(0,∞)`.** The two agree because of `force_positive_time`; the Lean form is the stronger one. |
| `corrected_background` (`:486-489`) | `∂_t b_ε + (b_ε·∇)b_ε − νΔb_ε + ∇π = g + H_ε` with `b_ε = v + w_ε`, `03-torus.tex:321-325`, reused at `04-whole-space.tex:50` | `INS.corrected_background` (`INS:97-115`): `residual ν (v+w) p t x = residual ν v p t x + correctionForce ν v w (t,x)`, hypotheses only pointwise differentiability/`ContDiff ℝ 2` of the slices | Exact modulo substituting `reference_equation`. **This field is the `I02` half of the "compact pressure representative"** (`REVIEW.md:77-88`): the pressure in it is the *unchanged* `π`, so the background correction contributes no pressure and `p_ε − π = P_ε` is forced. |
| `perturbation_divergence_free` (`:494-497`) | "each summand of the velocity is divergence free", `03-torus.tex:333`; consumed by Theorem 4.7, `04-whole-space.tex:306` | `LI.inserted_divergence` (`LI:132-151`) proves it for `v + w + U`; `PS.delayed_parabolic_divergence` (`PS:506-524`) gives `∇·U_ε = 0`; `PS.zeroPastField_smoothOn` (`PS:373-391`) gives the slice regularity of `U_ε` | The existing lemma covers `v+w+U`, the draft asks for `w+U` (i.e. `u_ε − v`). Same proof with `v := 0`, or one `ResidualCalculus.spatialDivergence_add`. Split unit 10. |
| `alpha` (`:85`), `scaledSpatialCutoff` (`:91`), `scaledTemporalCutoff` (`:98`), `scaledPacket` (`:108`) | `α(p,q)`, `θ_ε`, `η_ε`, `U_ε` — `03-torus.tex:131,184,185,112-113` | `CP.spatialCutoff`, `CP.temporalCutoff`, `PSc.parabolicVelocity` (`PSc:92-93`) + `PS.zeroPastField` (`PS:243-244`) | `scaledPacket U x₀ T ε` is **`rfl`-equal** to the third summand of `IF.velocity` (`IF:32-35`), checked in this worktree. Only its support is used here; its equation, energy and blowup are `I01`/`I03`. |

### Not in the draft, on purpose

* `eq:HHs` and every fractional/negative-order statement.  These are already
  largely proved on `ℝ³` too — `CFP`→`Paper1/CorrectionPositiveNorms.lean`
  (`scalarPhysicalForce_uniform_positive_time :107`) and
  `Paper1/CorrectionForceNorms.lean`
  (`scalarPhysicalForce_uniform_negative_time :169`) and
  `CVN` (`vectorPhysicalForce_uniform_positive_time :60`,
  `vectorPhysicalForce_all_negative_tendsto_zero :155`) — but they are `I03`'s
  contract, per `DEPENDENCY_GRAPH.md:247-252` and `STATEMENTS.md:259-274`.
* The full insertion family `IF.exists_insertion_family` (`IF:196-249`) and
  `Source/LocalApproximatingInsertion.lean:exists_local_approximating_insertion`
  (`:86-117`).  These already assemble `w_ε`, `U_ε` and the PDE, but they are
  `R42`'s target, and `EXTERNAL_REUSE.md:37` records that their lifespan claim
  goes through `SmoothLifespan.Flow` rather than the manuscript's maximal
  `H^∞` solution — a class bridge that is not `I02`'s business.

## 2. Recurring mismatches, in one place

1. **Global vs slab smoothness of the reference.**  Every `ε`-family
   declaration (`PR:12,19,77`, `CP:263,291`, `CFP:227,270`, `CE:42,54,169`,
   `CMN:123,164`, `CVN:14,22`, `IE:175`) assumes `hv : ContDiff ℝ ∞ v` on all of
   `ℝ×ℝ³`.  The manuscript only has `v` on `[0,T+δ]`.  `TE` already solves this
   *for the unscaled cutoff*: `TE.exists_global_reference_extension`
   (`TE:49-64`) and `TE.exists_local_background_removal_on` (`TE:68-95`).  It
   has **not** been done for `physicalCorrection`.  Units 1–2.
2. **`ε`-family bookkeeping.**  All existing bounds are stated on `Ioc (0:ℝ) 1`
   with one fixed `(θ, η)` and one `∃ C`.  The draft uses `Ioc (0:ℝ) ε₀` with
   `ε₀ ≤ 1` and constants as data.  This is exactly the "one common `ε`-family"
   requirement of `STATEMENTS.md:190-192, 253-257`; `choose` converts.
3. **Constants.**  `energyConst`, `mixedConst`, `correctionDerivConst`,
   `forceDerivConst`, `spatialVolumeConst` depend on `v` near `(x₀,T)`, on
   `θ, η`, on `ν` and on the derivative order — never on `ε`
   (`03-torus.tex:242`; `STATEMENTS.md:355-358`).  Making them structure fields
   rather than `∃`-bound inside each clause is what enforces that.
4. **Time-norm domain.**  `CMN.mixedNorm` integrates over `ℝ`; the paper's force
   norms run over `(0,∞)`.  Equal here because of `force_positive_time`; the
   Lean statement is the stronger one.  Same remark applies to
   `physicalCorrection_total_direction_energy` (`CE:169`), which integrates
   `t` over all of `ℝ` and therefore dominates `gradientSquare T`.
5. **Directional vs multi-index derivatives.**  The paper's `∂_x^β` is realized
   as an iterated Fréchet derivative evaluated on unit-ball spatial directions
   (and unit time directions).  This is the form of `CP:291-322` and
   `CFP:270-296`; the coordinate statement is the special case
   `u i = coordinateVector _`.
6. **Cutoff normalizations.**  `LC.exists_spatial_cutoff` centres `supp θ` at
   `x₀`; `PR.physical_support` wants it centred at `0`.  `LC.exists_temporal_cutoff`
   is stated with a free centre `T` and radius `δ`; the paper's `η` is the
   instance `T = 0, δ = 1` used at `IF:236`.

## 3. Bounded implementation split

Ten lemma-sized units.  Units 1–2 remove the global-smoothness mismatch, 3–9
discharge the API fields, 10 assembles and registers.  No unit reproves anything
already in the tree.

| # | Unit | Statement to prove | Builds on |
|---|---|---|---|
| 1 | `reference_window_extension` | From `reference_smooth`/`reference_divergence_free` on `Ioo 0 (T+δ) ×ˢ univ` and `0 < δ₁ < min T δ / 2`, produce `V : VelocityField` with `ContDiff ℝ ∞ V`, `∀ t x, spatialDivergence V t x = 0`, and `EqOn V v (Icc (T−δ₁) (T+δ₁) ×ˢ univ)`. | direct instantiation of `TE.exists_global_reference_extension` (`TE:49-64`) at centre `T`, radius `δ₁`, whose hypotheses are `ContDiffOn` and `hdiv` on `Ioo (T−2δ₁) (T+2δ₁) ×ˢ univ`, a subset of `Ioo 0 (T+δ) ×ˢ univ` by the choice of `δ₁`. |
| 2 | `correction_congr_of_window` | If `EqOn V v (Icc (T−δ₁) (T+δ₁) ×ˢ univ)` and `2ε² ≤ δ₁`, then (a) `physicalCorrection V x₀ T θ η ε = physicalCorrection v x₀ T θ η ε`, (b) `RadialPotential.timePotential V x₀ = timePotential v x₀` on that window, and (c) `correctionForce ν V w = correctionForce ν v w` whenever `tsupport w ⊆ Ioo (T−2ε²) (T+2ε²) ×ˢ univ`. | `CP.physicalCorrection`/`temporalCutoff` (`CP:138-143`) vanish off the window; `RP.timePotential` (`RP:202`) is time-slicewise; `LI.correctionForce_eq_zero_outside` (`LI:33-43`) kills the outside; `PS.residual_congr_local` (`PS:447-455`) is the pattern for the inside. |
| 3 | `potential_api` | `potential := timePotential V x₀` satisfies `potential_formula` (`rfl`), `potential_smooth`, `potential_curl`. | `RP.centeredPotential_eq_integral` (`RP:177`), `RP.timePotential_contDiff` (`RP:205`), `RP.spatialCurl_timePotential` (`RP:218-224`) / `RP.curl_centeredPotential` (`RP:186`), plus `SC.contDiff_spatialSlice` (`SC:147-150`) and unit 2(b) to return to `v`. |
| 4 | `cutoff_api` | Produce `θ, plateau, θRadius, η, ε₀` with `theta_*`, `eta_*`, `eps_*`. | `LC.exists_spatial_cutoff` (`LC:14-27`) with `R := θRadius` around `0`, `LC.exists_temporal_cutoff 0 1` (`LC:30-46`), and the `ε₀` recipe of `IF:239-244` intersected with `2ε² < min T δ` and `2ε² ≤ δ₁` of unit 1. |
| 5 | `lemma34_api` | `correction_formula`, `correction_smooth`, `correction_divergence_free`, `correction_compactSupport`, `correction_support`, `correction_support_ball`, `correction_vanishes_before`. | definitional unfolding (checked); `PR.physical_smooth` (`PR:12`), `PR.physical_divergence` (`PR:19`), `PR.physical_compact` (`PR:47`), `PR.physical_support` (`PR:56`), then `IF:128-131, 173-176` verbatim; all composed with units 1–2. |
| 6 | `bgzero_api` | `correction_cancels_germ` and `correction_cancels`.  The second needs `IsOpen (PR.spaceMap ε x₀ '' plateau)`. | `PR.physical_removes` (`PR:77-114`) + `LI.background_removed_on_packet` (`LI:73-93`), composed exactly as at `IF:97-105`; openness from `Homeomorph.isOpenMap` for `y ↦ x₀ + ε•y` (`ε ≠ 0`); `PS.delayed_full_support` (`PS:335-353`) for `supp U_ε(t) ⊆ scaledSupport`. |
| 7 | `support_measure_api` | `force_smooth`, `force_compactSupport`, `force_support`, `force_positive_time`, `force_support_ball`, `force_spatial_volume`, `force_time_length`. | `CVN.physicalForce_smooth` (`CVN:22`), `CVN.physicalForce_compact` (`CVN:37`), `LI.correctionForce_support` (`LI:45`) + unit 5; then `Real.volume_Ioo` for the `4ε²` duration and `Measure.addHaar_ball` (with `spatialVolumeConst := (volume (Metric.ball (0:Space) θRadius)).toReal`) for the `O(ε³)` volume, via `LI.slice_support_projection` (`LI:155`). |
| 8 | `energy_api` | `correction_energy_memLp` and `correction_energy_bound`. | `CE.physicalCorrection_uniform_energy` (`CE:54-71`), `IE.correction_gradientSquare_bound` (`IE:175-200`), `IE.energyNorm_le_of_squared_bounds` (`IE:107-122`); finish with `Real.sqrt (A*ε^3) = √A * ε^(3/2)` (`Real.sqrt_mul`, `Real.rpow_natCast`). The same three ingredients are already combined for the *packet plus correction* sum at `IE:327-366`, so the pure-correction case is strictly easier. |
| 9 | `derivative_and_mixed_api` | `correctionDerivConst(_nonneg)`, `correction_derivative_bound`, `forceDerivConst(_nonneg)`, `force_derivative_bound`, `mixedConst`, `force_spatial_memLp`, `force_mixed_bound`. | `choose` on `CP.physical_mixed_derivative_bound` (`CP:291-322`), `CFP.physicalForce_spatial_derivative_bound` (`CFP:270-296`), `CMN.physical_force_mixed_bound` (`CMN:123-161`), `CMN.physical_force_spatial_memLp` (`CMN:164-186`); `ENNReal.ofReal_toReal` for the constant, `ring` for `α(p,q)+1 = -2+3/p+2/q` (checked). |
| 10 | `correctionAPI` + contract registration | `corrected_background`, `perturbation_divergence_free`, then the term `CorrectionAPI` and hence `correctionStatement`; promote the reviewed record to `verification/Contracts/V1/Correction.lean`, add the typed `Bindings` entry and the `#print axioms` test. | `INS.corrected_background` (`INS:97-115`) + `reference_equation`; `LI.inserted_divergence` (`LI:132-151`) with `PS.delayed_parabolic_divergence` (`PS:506-524`) and `PS.zeroPastField_smoothOn` (`PS:373-391`); packaging pattern of `verification/Contracts/V1/Thresholds.lean` and `verification/contracts.json`. |

Optional follow-ups, **not** part of `I02` (recorded so they are not lost):

* **A.** A `ContDiffOn`-hypothesis version of `RP.timePotential_contDiff` and of
  the whole `PR`/`CP`/`CFP` chain, which would make units 1–2 unnecessary and
  would also simplify `I03`.  Larger than a lemma-sized unit.
* **B.** The coordinate-multi-index restatement of `eq:derivativebounds`
  (`∂^β` with `β : Fin 3 → ℕ`), if a downstream consumer wants it literally.
  Nothing in Section 4 does.
* **C.** `K_*`: the enlarged compact set of `03-torus.tex:101-102` containing
  `K` *and* the spatial projection of `supp F`.  `IF:218-234` builds it inline
  (`Kall`); `I01`'s comparison already lists it as a loose end.  `I02` takes it
  as the given `carrier`.
