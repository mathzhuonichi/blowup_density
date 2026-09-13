# I03 source-to-target comparison

Lane 015, task **I03** ("Same-family scaling and negative norms"), 2026-09-13.
Target: [`Spec.lean`](Spec.lean), `BlowupDensity.I03.Draft.ScalingAPI`.
Canonical norms: `verification/Contracts/V1/Data.lean`
(`BlowupDensity.Contracts.V1.Data`); exponent arithmetic:
`verification/Contracts/V1/Thresholds.lean`; packet:
`verification/Contracts/V1/Packet.lean`.

All `formalization/…` line numbers are as of this worktree.
Paper locations are `paper/sections/…`.

---

## 1. Field-by-field table

Abbreviations. `k = ε⁻¹`; `β(q,s) = ThresholdAPI.exponent q s = 2/q − 3/2 − s`;
"cycles" = Mathlib's `𝓕` (kernel `exp(−2πi x·ξ)`); "angular" = the manuscript's
`(2π)^{−3/2}∫exp(−ix·ξ)` transform, `NSFormalization.Source.angularFourier`
(`Source/FourierConvention.lean:23`); "datum" = the
`RealVectorSobolev s`-valued object that `Data.IsSobolevDatum`
(`Contracts/V1/Data.lean:160`) demands.

| Spec field | Paper location | Existing declaration (file:line), hypotheses, convention | Mismatch / gap |
|---|---|---|---|
| `scaledVelocity` (`def`) | eq:scaling, `03-torus.tex:112-113` | `NSFormalization.Source.parabolicVelocity` `Source/ParabolicScaling.lean:92` composed with `PacketScaling.zeroPastField` `Source/PacketScaling.lean:243`. **Verified `rfl`-equal** to my `def` (see §4). Also `rfl`-equal to the third summand of `InsertionFamily.velocity` `Source/InsertionFamily.lean:32-36` and to `research/I02/Spec.lean` `scaledPacket`. | none |
| `scaledPressure` (`def`) | eq:scaling, `03-torus.tex:114-115` | `Source.parabolicPressure` `ParabolicScaling.lean:95`; **verified `rfl`** | none |
| `scaledForce` (`def`) | eq:scaling, `03-torus.tex:116-117` | `Source.parabolicForce` `ParabolicScaling.lean:98`; **verified `rfl`**; also `rfl`-equal to the second summand of `InsertionFamily.force` `Source/InsertionFamily.lean:40-43` | none |
| `alpha` (`def`) | eq:packetFscale, `03-torus.tex:131` | `research/I02/Spec.lean` `alpha` (same body); `Paper3.forceExponent` `Paper3/Thresholds.lean:11` is the Sobolev sibling | duplicate of I02's `alpha`; R42 must identify them |
| `packet`, `ν`, `T`, `δ`, `x₀`, `r`, `carrierRadius`, `carrier_subset`, `force_carrier_subset` | `01-intro.tex:63-65`, `03-torus.tex:101-105`, `04-whole-space.tex:32-33` | `PacketAPI` (`Contracts/V1/Packet.lean:171`); the radius/ball bookkeeping is `InsertionFamily.exists_insertion_family` `Source/InsertionFamily.lean:196-244` (`R = B + 1`, `hKR`, `hfR`) | none; `carrierRadius` is `⟪I02:CorrectionAPI.θRadius⟫` and must be shared |
| `ε₀`, `eps_pos`, `eps_le_one`, `eps_time`, `eps_space` | `03-torus.tex:104-105, 212`; `04-whole-space.tex:33` | `exists_insertion_family` builds `ε₀ = min 1 (min (r/R) ((T−τ)/2))` `Source/InsertionFamily.lean:238` | source uses `Ioo (0,ε₀)`, I02 and I03 use `Ioc (0,ε₀)`; harmless, but the binding must convert |
| `correction`, `correction_smooth`, `correction_compactSupport` | `03-torus.tex:186-188` | concrete: `Paper1.CorrectionProfile.physicalCorrection`, smooth/compact via `CorrectionVectorNorms.physicalCorrection_smooth` `Paper1/CorrectionVectorNorms.lean:14` and `physicalCorrection_compact` `:28`; abstract: `⟪I02:CorrectionAPI.correction⟫` | I02 pins `w_ε` only by the curl formula, never by `physicalCorrection`; the I02↔source identification is an open binding obligation, not an I03 one |
| `forceCorrection`, `forceCorrection_smooth`, `forceCorrection_compactSupport` | eq:H, `03-torus.tex:220-225` | `Source.correctionForce ν v (physicalCorrection …)`; `Paper1/CorrectionVectorNorms.lean:22` (`physicalForce_smooth`), `:37` (`physicalForce_compact`); abstract: `⟪I02:CorrectionAPI.forceCorrection⟫` | same as above |
| `packetEnergyIdentity` `‖U_ε‖_{L^∞(0,T;L²)} = ε^{1/2}M` | eq:packetEscale first identity, `03-torus.tex:125-126` | **partial.** Exact slicewise identity `PacketScaling.l2Sq_parabolic` `Source/PacketScaling.lean:37` (`l2Sq (parabolicVelocity k t₀ x₀ u) t = k⁻¹ · l2Sq u (k²(t−t₀))`) and its square root `l2Norm_parabolic` `:100`. Uniform-in-time version is only an **inequality** with an arbitrary bound `N`: `uniform_l2Norm_parabolic` `:118`. Packet side: `Paper1.InsertionEnergy.packet_l2_bound` `Paper1/InsertionEnergy.lean:203` is again `≤ εE`. | the **equality** with the least upper bound `M` is missing; needs `PacketAPI.energy_isLUB` plus the `Ico t_ε T ↔ Ico 0 1` time bijection (`PacketScaling.reference_time_mem` `:107`). Norm object differs: `Data.energyEssSup` is an `ℝ≥0∞` `essSup` of `eLpNorm … 2`, source uses `velocityL2 = sqrt ∘ l2Sq` (`Paper1/InsertionEnergy.lean:20`) |
| `packetDissipationIdentity` `‖∇U_ε‖_{L²(0,T;L²)} = ε^{1/2}D` | eq:packetEscale second identity, `03-torus.tex:127-128` | **essentially present.** Exact: `PacketScaling.dissipation_parabolic` `:46`, `total_dissipation_parabolic` `:78`, and `Paper1.InsertionEnergy.packet_gradientSquare` `Paper1/InsertionEnergy.lean:228` (`gradientSquare T U_ε = ε · gradientSquare 1 u`, an equality) | only the `Data.energyGradient` ↔ `sqrt ∘ gradientSquare` bridge and `PacketAPI.dissipation_eq` remain |
| `correctionEnergyBound` `‖w_ε‖_{E_T} ≤ Cε^{3/2}` | eq:wE, `03-torus.tex:234` | `Paper1.InsertionEnergy.insertion_energy_bound` `Paper1/InsertionEnergy.lean:327` contains the correction half (`physicalCorrection_uniform_energy`, `correction_gradientSquare_bound` `:175`); `⟪I02:CorrectionAPI.correction_energy_bound⟫` states it in the `energyNorm` (real-valued) convention | I02 uses `Paper1.InsertionEnergy.energyNorm : ℝ` (`:30`), the contract uses `Data.energyENorm : ℝ≥0∞` (`Data.lean:468`); the two agree on finite values but the bridge is not written |
| `perturbationEnergyBound` (eq:REclose) | `04-whole-space.tex:39-41` | **shape mismatch.** `insertion_energy_bound` `Paper1/InsertionEnergy.lean:327` proves `energyNorm T (perturbation …) ≤ √(2(Aε³+Bε)) + √(2(Cε³+Dε))` with four opaque constants, and `insertion_energy_tendsto_zero` `:372` proves the limit | the paper's exact shape `(M+D)ε^{1/2} + Cε^{3/2}` (with **the** Lemma 2.2 constants) is not proved; the source constants `B = 2E`, `D = gradientSquare 1 u` are not `M`, `D` |
| `packetMixedScaling` (eq:packetFscale) | `03-torus.tex:129-131, 148-149` | **inequality only.** `Source.MixedForceScaling.compact_force_mixed_bound` `Source/MixedForceScaling.lean:62`: `mixedNorm p q (parabolicForce ε⁻¹ t₀ x₀ F) ≤ ofReal (ε^{−3+3/p+2/q}) · C` with `C` from a support indicator, all `p,q ∈ ℝ≥0∞`, all `ε>0`, all centres. Exact ingredients: `spatial_force_norm_real` `:12` and `TimeNormScaling.eLpNorm_parabolic_time` `Source/TimeNormScaling.lean:19` (both **equalities**) | the paper's **equality** `= ε^{α}‖F‖` is not assembled. Norm object: `Paper1.CorrectionMixedNorms.mixedNorm` `Paper1/CorrectionMixedNorms.lean:13` is `eLpNorm (t ↦ (eLpNorm (F(t,·)) p).toReal) q volume` over **all of ℝ**; `Data.mixedLebesgueENorm` `Data.lean:251` is an infimum over `Lp`-valued paths over `(0,∞)` |
| `packetPositiveScaling` (eq:RpositiveScale line 1) | `04-whole-space.tex:64-66` | **present, stronger.** `TimeNormScaling.force_eLpNorm_positive_epsilon` `Source/TimeNormScaling.lean:117`: for `0 ≤ s`, `0 < ε ≤ 1`, any `q : ℝ≥0∞`, `eLpNorm (fourierSobolevNorm s ∘ parabolicComplexForce ε⁻¹ t₀ f) q ≤ ofReal (ε^{2/q−3/2−s}) · eLpNorm (fourierSobolevNorm s ∘ f) q`. Single-term, hence stronger than the paper's two-term bound for `ε ≤ 1`. Vector lift: `VectorForceNorms.eLpNorm_vector_le_sum` `Source/VectorForceNorms.lean:47`, `coordinate_norm_parabolicForce` `:79` | cycles convention; time norm on all of `ℝ`; scalar/complex components, not the `Data` datum norm |
| `correctionPositiveScaling` (eq:RpositiveScale line 2, and eq:HHs) | `04-whole-space.tex:67-69`, `03-torus.tex:238-240` | **present, exact exponent.** `CorrectionVectorNorms.vectorPhysicalForce_uniform_positive_time` `Paper1/CorrectionVectorNorms.lean:60`: `0 ≤ s ≤ 1`, `1 ≤ q`, `ε ∈ Ioc 0 1`, bound `ofReal (ε^{2/q−1/2−s}) · C` — that exponent is exactly `β(q,s)+1`. Scalar: `CorrectionPositiveNorms.scalarPhysicalForce_uniform_positive_time` `Paper1/CorrectionPositiveNorms.lean:107` | cycles convention (`vectorFourierSobolevNorm`), time on `ℝ` |
| `packetNegativeHomogeneous` `‖F_ε‖_{L^q_tḢ^s} ≤ Cε^{β}` | `04-whole-space.tex:70-76`, and at `q=2,s=−1` `:264-272` | **absent.** The homogeneous norm is only ever used on the *profile*, never on the scaled field: `FourierScaling.fourierSobolevSq_concentrated_le_negative` `Source/FourierScaling.lean:134` bounds the *inhomogeneous* energy of `F_ε` by `k^{3+2s}` times the profile's homogeneous energy | genuine gap. The missing piece is the exact homogeneous analogue of `fourierSobolevSq_concentrated` `Source/FourierScaling.lean:51`, then its `L^q_t` and vector/angular/datum lifts. **This is what Proposition 4.6's `L²_tḢ^{-1}` clause needs.** |
| `packetNegativeScaling` (eq:RnegativeScale, packet half) | `04-whole-space.tex:73-75` | **present.** `TimeNormScaling.force_eLpNorm_negative_epsilon` `Source/TimeNormScaling.lean:133`: `s ≤ 0`, any `ε>0`, any `q`, bound `ofReal (ε^{2/q−3/2−s}) · eLpNorm (homogeneousFourierNorm s ∘ f) q`. Finiteness of the right side on `−3/2 < s ≤ 0`: `Paper3.HomogeneousTime.uniform_homogeneousFourier_time` `Paper3/HomogeneousTime.lean:82`, `memLp_homogeneousFourier_time` `:108`, both from `homogeneous_energy_le_bound_add_L2` `:14` — the paper's own `|ξ|<1` / `|ξ|≥1` split | cycles convention, time on `ℝ`, scalar components |
| `correctionNegativeHomogeneous` | `04-whole-space.tex:74-75`, `:271` | **absent**, same reason as the packet homogeneous field | genuine gap |
| `correctionNegativeScaling` (eq:RnegativeScale, correction half) | `04-whole-space.tex:74-75` | **present.** `CorrectionVectorNorms.vectorPhysicalForce_uniform_negative_time` `Paper1/CorrectionVectorNorms.lean:83`: `−3/2 < s ≤ 0`, `1 ≤ q`, `ε ∈ Ioc 0 1`, bound `ofReal (ε^{2/q−1/2−s}) · C`, i.e. `β(q,s)+1`. Profile uniformity: `CorrectionForceNorms.scalarProfile_uniform_homogeneous` `Paper1/CorrectionForceNorms.lean:78` and `_time` `:100`; amplitude bookkeeping `scalarPhysicalForce_eq` `:148` | cycles convention, time on `ℝ` |
| `forceDifference`, `forceDifference_formula` | `04-whole-space.tex:48` | `InsertionFamily.force` `Source/InsertionFamily.lean:40-43`; **verified `rfl`** to be `correctionForce ν v (physicalCorrection …) + scaledForce f x₀ T ε` | none |
| `forceLowOrderBound` (intermediate index) | `04-whole-space.tex:78` | **present in two variants.** Arithmetic: `Paper3.negative_intermediate_index` `Paper3/Thresholds.lean:28` (`s < −1/2 → ∃ r, −3/2 < r < −1/2 ∧ s < r`), already a `ThresholdAPI.negativeIndex` field. Monotonicity: `CompactForceConvergence.fourierSobolevNorm_mono_of_compact` `Source/CompactForceConvergence.lean:36`, `scalar_force_eLpNorm_mono` `:44`. Assembled for the packet force at `q=2` in `compact_scalar_force_L2_tendsto` `:98` and for the correction in `CorrectionVectorNorms.scalarPhysicalForce_all_negative_tendsto_zero` `Paper1/CorrectionVectorNorms.lean:134` | the correction version lowers to the **fixed** index `r = −1`, not to an existential `r`; my field's shape (one `r` serving both `F_ε` and `H_ε`) must be reconciled, or split into two witnesses |
| `forceConvergence` | `04-whole-space.tex:42-43` | **present for the full range, in the angular convention.** `InsertionFamily.force_angular_L1_tendsto_zero` `Source/InsertionForceConvergence.lean:66` (`s < 1/2`) and `force_angular_L2_tendsto_zero` `:78` (`s < −1/2`), both for the **whole** `H_ε + F_ε` and for the **one** `ε`-family, via `AngularForceNorms.angular_family_tendsto_zero` `Source/AngularForceNorms.lean:54`. Bundled as `ForceApproximation` `Source/ForceApproximatingInsertion.lean:36` and produced together with the energy limit by `LocalApproximatingInsertion.exists_local_approximating_insertion` `Source/LocalApproximatingInsertion.lean:86` | measured by `vectorAngularSobolevNorm` `Source/AngularForceNorms.lean:16` (a slicewise Fourier integral over all of `ℝ` in time), not by `Data.forceSobolevENorm` |
| `scalingStatement` | — | the existential shape of `LocalApproximatingInsertion.exists_local_approximating_insertion` `:97` | packet is pinned by `HEq` because `PacketAPI` is viscosity-indexed |

---

## 2. Mismatch notes

### 2.1 Convention: the existing scaling estimates are **not** in `Data.lean`'s angular convention

Three distinct norm objects are in play.

1. **Cycles-slice** (source): `Source.fourierSobolevSq` `Source/FourierScaling.lean:47`,
   `fourierSobolevNorm` / `homogeneousFourierNorm` `Source/TimeNormScaling.lean:65,68`,
   `vectorFourierSobolevNorm` `Source/VectorForceNorms.lean:21`.  These use Mathlib's
   `𝓕` and are the convention of **every** scaling estimate listed above
   (`FourierScaling`, `TimeNormScaling`, `Paper3/HomogeneousTime`,
   `Paper1/Correction{Positive,Force,Vector}Norms`, `MixedForceScaling`).
2. **Angular-slice** (source): `Source.vectorAngularSobolevNorm`
   `Source/AngularForceNorms.lean:16`.  Related to (1) only by a **two-sided
   equivalence with the constant `frequencyUnit^{|s|} = (2π)^{|s|}`**,
   `vectorAngularSobolevNorm_equivalence` `:19`, `eLpNorm_angular_le` `:37` — an
   equivalence, *not* an isometry.
3. **Angular datum** (contract): `Data.forceSobolevENorm` `Data.lean:225`, an
   `ℝ≥0∞` infimum over strongly measurable `RealVectorSobolev s`-valued paths
   satisfying `Data.IsSobolevPath` `:174`, over `forceTimeMeasure =
   volume.restrict (Ioi 0)`.

Consequences.

* The bridge (1)→(3) exists in pieces and runs in the **`≤` direction only**:
  `Paper3.AngularRealVectorBochner.angularRealVectorSlice` `Paper3/AngularRealVectorBochner.lean:47`
  produces a datum path whose pairing, `angularRealVectorSlice_pairing` `:54`, is
  *literally* the shape of `Data.IsSobolevDatum` — `Data.lean:143` says so
  explicitly ("This is the pairing shape of `angularRealVectorSlice_pairing`").
  Strong measurability comes from `memLp_angularRealVectorSlice` `:64` (already on
  `positiveTimeMeasure = Data.forceTimeMeasure`), and the norm comparison from
  `cyclesToAngularRealVector_norm_le` `:24` with the same `(2π)^{|s|}`.  Since
  `forceSobolevENorm` is an infimum, one admissible path gives
  `Data.forceSobolevENorm q s F ≤ ofReal ((2π)^{|s|}) · eLpNorm (vectorFourierSobolevNorm s F) q volume`.
* That direction suffices for **every** upper-bound field and for
  `forceConvergence`; the `(2π)^{|s|}` is absorbed into the existential
  `positiveConst` / `negativeConst` / `correctionNegativeConst`.
* It does **not** suffice for the three equalities `packetEnergyIdentity`,
  `packetDissipationIdentity`, `packetMixedScaling`.  Those, however, carry no
  Sobolev weight (`L²` and `L^p`), so the angular/cycles discrepancy is absent
  there (`(2π)^0 = 1`); what they need instead is the `Data.energyEssSup` /
  `Data.energyGradient` / `Data.mixedLebesgueENorm` ↔ `l2Sq` / `dissipation` /
  `eLpNorm` bridges.
* `Data.forceHomogeneousENorm` `Data.lean:387` is realized through
  `Data.IsHomogeneousDatum` `:321` (`ĥ = |ξ|^{-s}G`), a **different** realization
  from `angularRealization`.  There is no source counterpart at all; see §2.4.

### 2.2 At fixed ν? — yes, no mismatch

Parabolic spatial concentration does not touch the viscosity:
`Source.parabolic_residual` `Source/ParabolicScaling.lean:103` and
`parabolic_equation` `:112` are stated for an arbitrary fixed `ν` and give a
common factor `k³` on every term, which is the paper's "no viscosity rescaling
occurs" (`03-torus.tex:141`).  The correction estimates carry `ν` as an explicit
argument throughout (`Source.correctionForce ν v w`,
`Paper1/CorrectionForceNorms.lean:144`).  `ScalingAPI.packet : PacketAPI ν` fixes
one packet at one viscosity, matching `01-intro.tex:63-65`.

### 2.3 Same ε-family as `CorrectionAPI`? — yes at source level, unpinned at contract level

At source level the family is literally one function of `ε`:
`InsertionFamily.velocity/pressure/force` `Source/InsertionFamily.lean:33-43`
share `u, p, f, θ, η, x₀, T` and vary only `ε`, and
`exists_local_approximating_insertion` `Source/LocalApproximatingInsertion.lean:86`
delivers one `ε₀` carrying `ForceApproximation`, `EnergyApproximation`,
`InsertionProperties` and `AdmissibleCompactForce` simultaneously.  I verified by
`rfl` (§4) that `InsertionFamily.force ν f v x₀ T θ η ε` is exactly
`correctionForce ν v (physicalCorrection v x₀ T θ η ε) + scaledForce f x₀ T ε`,
i.e. `H_ε + F_ε` with the same `ε` — the threading the manuscript asserts at
`04-whole-space.tex:43`.

At contract level, however:

* `research/I02/Spec.lean` `CorrectionAPI` pins `w_ε` only by the curl formula
  `correction_formula`; nothing there says `A.correction ε = physicalCorrection …`.
  So "I02's family = the source family" is an open binding obligation of I02, not
  of I03.
* `ScalingAPI.ε₀` and `CorrectionAPI.ε₀` are independent fields.  **R42 must
  either instantiate both from one source family or take the minimum**; the
  contract as written does not force `A.ε₀ = C.ε₀`.  Recommendation: give `R42`
  the two records plus the equations `S.correction = C.correction`,
  `S.forceCorrection = C.forceCorrection`, `S.ε₀ = C.ε₀`, `S.x₀ = C.x₀`,
  `S.T = C.T`, `S.r = C.r`, `S.carrierRadius = C.θRadius`.
* Interval convention: source uses `Ioo (0, ε₀)`, I02 and I03 use `Ioc (0, ε₀)`.

### 2.4 Time domain

Every source time norm is `eLpNorm … q volume` over **all of `ℝ`**
(`TimeNormScaling.lean` header: "Time is integrated over all of `ℝ`, so the
estimates include the portion of the force after the insertion time.
Restriction to positive time only decreases these norms").  `Data.*` force norms
use `forceTimeMeasure = volume.restrict (Ioi 0)`.  Source ≥ contract, so every
upper bound transfers; for `packetMixedScaling`'s *equality* one additionally
needs `PacketScaling.parabolicForce_positive_support`
`Source/PacketScaling.lean:552` together with `eps_time`, which is exactly the
paper's argument at `03-torus.tex:148`.

### 2.5 `E_T`

`Data.energyENorm` `Data.lean:468` is `ℝ≥0∞`-valued,
`energyEssSup + energyGradient`, with `energyGradient` built from
`Data.spatialGradient : WithLp 2 (Fin 3 → Space)` (Frobenius, `Data.lean:446`).
`Paper1.InsertionEnergy.energyNorm` `Paper1/InsertionEnergy.lean:30` is
`ℝ`-valued, `(eLpNorm (velocityL2 F) ⊤ (restrict (Ioo 0 T))).toReal +
√(gradientSquare T F)`, and `gradientSquare` `:26` integrates
`NavierStokesR3.CompactEnergy.dissipation`, which is the same Frobenius quantity
componentwise.  The objects agree on finite values; `REVIEW_B` issue 2 is exactly
why the contract keeps `ℝ≥0∞`.  Bridge not written.

### 2.6 Scope deliberately not covered by `ScalingAPI`

`research/section4/STATEMENTS.md:281-286` item 1 (the rescaled fields solve the
momentum equation at the same `ν`, are divergence free, vanish for `t ≤ t_ε`,
and blow up as `t ↑ T`) is **not** a field of `ScalingAPI`.  It is fully proved
in source — `parabolic_equation` `Source/ParabolicScaling.lean:112`,
`PacketScaling.delayed_parabolic_equation` `:489`,
`delayed_parabolic_divergence` `:506`, `speed_unbounded_parabolic` `:147`,
`zeroPast_dilate_early` `:300` — and is pure transport of `PacketAPI` through
`eq:scaling`.  Recommendation: expose it either as a small separate `I03`
addendum record or directly in `R42`; do not leave it unowned.

---

## 3. Exponents and ranges: existing vs. paper

| Statement | Paper range | Source range | Verdict |
|---|---|---|---|
| eq:RpositiveScale, packet: `‖F_ε‖_{L^q_tH^s} ≲ ε^{β(q,s)}` | `0 ≤ s ≤ 1`, `q ∈ {1,2}` | `force_eLpNorm_positive_epsilon` `TimeNormScaling.lean:117`: **all** `s ≥ 0`, **all** `q : ℝ≥0∞` (through `q.toReal`, `q = ⊤` included), `0 < ε ≤ 1`. Time-`L^q` finiteness of the profile needs `s ≤ 1` (`Paper3.memLp_fourierSobolev_le_one_time`, used at `CompactForceConvergence.lean:94`) | source ⊇ paper. Source proves the **single-term** `Cε^{β(q,s)}`, which for `ε ≤ 1, s ≥ 0` implies the paper's two-term `C(ε^{β(q,0)}+ε^{β(q,s)})` |
| eq:RpositiveScale, correction: `‖H_ε‖ ≲ ε^{β(q,s)+1}` | `0 ≤ s ≤ 1`, `q ∈ {1,2}` | `vectorPhysicalForce_uniform_positive_time` `CorrectionVectorNorms.lean:60`: `0 ≤ s ≤ 1`, `1 ≤ q`, `ε ∈ Ioc 0 1`; exponent literally `2/q − 1/2 − s` | exact match |
| eq:RnegativeScale, packet, **inhomogeneous** | `−3/2 < s < 0`, `q ∈ {1,2}` | `force_eLpNorm_negative_epsilon` `TimeNormScaling.lean:133`: `s ≤ 0`, all `q`, all `ε > 0`; usable range fixed by profile finiteness `−3/2 < s ≤ 0` (`HomogeneousTime.lean:82,108`) | source ⊇ paper (adds `s = 0`) |
| eq:RnegativeScale, correction, **inhomogeneous** | `−3/2 < s < 0`, `q ∈ {1,2}` | `vectorPhysicalForce_uniform_negative_time` `CorrectionVectorNorms.lean:83`: `−3/2 < s ≤ 0`, `1 ≤ q`, `ε ∈ Ioc 0 1` | source ⊇ paper |
| eq:RnegativeScale, **homogeneous** `‖·‖_{L^q_tḢ^s}` of the *scaled* fields | `−3/2 < s < 0` (and `s = −1`, `q = 2` for prop:Renergy) | **nothing.** The homogeneous norm appears only on profiles (`homogeneousFourierNorm`, `HomogeneousTime.lean`) | **gap** |
| `s ≤ −3/2` by monotonicity, packet | `q = 2`, any `s ≤ −3/2` | `compact_scalar_force_L2_tendsto` `CompactForceConvergence.lean:98` / `compact_vector_force_L2_tendsto` `:123`: all `s < −1/2`, `s ≤ −3/2` included, via `negative_intermediate_index` | exact match |
| `s ≤ −3/2` by monotonicity, correction | same | `scalarPhysicalForce_all_negative_tendsto_zero` `CorrectionVectorNorms.lean:134` / vector `:155`: all `s ≤ 0` with `β(q,s)+1 > 0`, by lowering to the fixed `r = −1` | covers the paper; different witness |
| convergence, `q = 1` | `s < 1/2` | `force_angular_L1_tendsto_zero` `InsertionForceConvergence.lean:66`: `s < 1/2`, whole `H_ε+F_ε`, one family | exact match |
| convergence, `q = 2` | `s < −1/2` | `force_angular_L2_tendsto_zero` `:78`: `s < −1/2` | exact match |
| eq:packetEscale, `L^∞L²` | equality `= ε^{1/2}M` | slicewise equality `l2Sq_parabolic` `PacketScaling.lean:37`; uniform version only `≤ √(k⁻¹)N` `:118` | inequality only; **`M` (a LUB) not reached** |
| eq:packetEscale, `L²Ḣ¹` | equality `= ε^{1/2}D` | equality `total_dissipation_parabolic` `PacketScaling.lean:78`, `packet_gradientSquare` `InsertionEnergy.lean:228` | essentially present |
| eq:packetFscale | equality, `1 ≤ p,q ≤ ∞` | `compact_force_mixed_bound` `MixedForceScaling.lean:62`: inequality, all `p,q`, all `ε>0`; the two exact change-of-variable lemmas exist (`MixedForceScaling.lean:12`, `TimeNormScaling.lean:19`) | inequality only |
| eq:REclose | `(M+D)ε^{1/2} + Cε^{3/2}` | `insertion_energy_bound` `InsertionEnergy.lean:327`: `√(2(Aε³+Bε)) + √(2(Cε³+Dε))` | different shape, opaque constants |
| eq:HHs (`q = 1`, `0 ≤ s ≤ 1`) | `C(ε^{3/2}+ε^{3/2−s})` | the `q = 1` case of `vectorPhysicalForce_uniform_positive_time` `:60` | present |
| `β(q,s)` arithmetic and the intermediate index | `04-whole-space.tex:57-60, 78` | `Paper3/Thresholds.lean:11,13,17,21,28,38`, already registered as `ThresholdAPI` (`contracts.json` `R41.threshold_arithmetic`) | complete |

---

## 4. Machine-checked definitional bridges

Run in this worktree (`verification/`, `lake env lean /tmp/i03_defeq_check.lean`),
all by `rfl`, all succeeded:

* `scaledVelocity U x₀ T ε = parabolicVelocity ε⁻¹ (T−ε²) x₀ (zeroPastField U)`
* `scaledPressure P x₀ T ε = parabolicPressure ε⁻¹ (T−ε²) x₀ (zeroPastField P)`
* `scaledForce F x₀ T ε = parabolicForce ε⁻¹ (T−ε²) x₀ F`
* `InsertionFamily.velocity u v x₀ T θ η ε z = v z + physicalCorrection v x₀ T θ η ε z + scaledVelocity u x₀ T ε z`
* `InsertionFamily.force ν f v x₀ T θ η ε z = correctionForce ν v (physicalCorrection v x₀ T θ η ε) z + scaledForce f x₀ T ε z`

The last two are the family-threading claim of `04-whole-space.tex:43`, checked
rather than asserted.

---

## 5. Bounded implementation split

Ten units.  U1 and U2 are prerequisites for almost everything else; U7 is the
only genuinely new mathematics.

| # | Unit | Size | Inputs | Delivers |
|---|---|---|---|---|
| **U1** | **Inhomogeneous norm bridge.** For `F` smooth with compact support, `Data.forceSobolevENorm q s F ≤ ofReal ((2π)^{|s|}) · eLpNorm (Source.vectorFourierSobolevNorm s F) q volume`, and the corresponding `Tendsto` transfer. | M | `angularRealVectorSlice` + `_pairing` `AngularRealVectorBochner.lean:47,54`; `memLp_angularRealVectorSlice` `:64`; `cyclesToAngularRealVector_norm_le` `:24`; `norm_compactVectorFourierLp` `Source/ForceNormAddition.lean:31`; `eLpNorm_mono_measure` for `Ioi 0 ⊆ ℝ` | the single hypothesis every `Data`-valued Sobolev field below rests on |
| **U2** | **`E_T` bridge.** `Data.energyEssSup T z = eLpNorm (velocityL2 z) ⊤ (restrict (Ioo 0 T))` and `Data.energyGradient T z = ofReal (√(gradientSquare T z))` for slice-measurable `z`; hence `Data.energyENorm T z ≤ ofReal (energyNorm T z)` and the reverse on finite values. | S | `Data.lean:437,452,468`; `InsertionEnergy.lean:20,22,26,30`; `Data.spatialGradient` `Data.lean:446` vs `dissipation` | `correctionEnergyBound`, and the E_T identities |
| **U3** | `packetDissipationIdentity`. | S | `total_dissipation_parabolic` `PacketScaling.lean:78`, `packet_gradientSquare` `InsertionEnergy.lean:228`, `PacketAPI.dissipation_eq`, U2 | one field |
| **U4** | `packetEnergyIdentity`: upgrade `uniform_l2Norm_parabolic` to an `essSup` **equality** with the LUB `M`. | M | `l2Norm_parabolic` `PacketScaling.lean:100`, `reference_time_mem` `:107`, `zeroPast_dilate_early` `:300`, `PacketAPI.energy_isLUB`, U2 | one field; the only place `energy_isLUB` (rather than a bound) is consumed |
| **U5** | `perturbationEnergyBound` (eq:REclose) in the paper's shape. | S | U2–U4 + `correctionEnergyBound` + triangle inequality for `Data.energyENorm` | one field; replaces the opaque `A,B,C,D` shape of `insertion_energy_bound` |
| **U6** | `packetMixedScaling` as an **equality**, and the `Data.mixedLebesgueENorm` ↔ `mixedNorm` bridge on `(0,∞)`. | M | `spatial_force_norm_real` `MixedForceScaling.lean:12`, `eLpNorm_parabolic_time` `TimeNormScaling.lean:19`, `parabolicForce_positive_support` `PacketScaling.lean:552`, `eps_time` | one field |
| **U7** | **Homogeneous scaling of the scaled fields.** (a) exact identity `∫‖ξ‖^{2s}‖𝓕(concentratedForce k f)‖² = k^{3+2s}∫‖ξ‖^{2s}‖𝓕 f‖²`, mirroring `fourierSobolevSq_concentrated` `FourierScaling.lean:51`; (b) its `L^q_t` form, mirroring `force_eLpNorm_negative_epsilon`; (c) the vector/angular/`IsHomogeneousDatum` lift to `Data.forceHomogeneousENorm`. | L | `FourierScaling.lean:22,51`; `HomogeneousTime.lean:14,47,82,108`; `CorrectionForceNorms.lean:78,100`; `Data.IsHomogeneousDatum` `Data.lean:321`, `forceHomogeneousENorm` `:387` | `packetNegativeHomogeneous`, `correctionNegativeHomogeneous`; **and prop:Renergy's `L²_tḢ^{-1}` clause (R46)**. (c) is the new work: no source declaration produces an `IsHomogeneousDatum` witness |
| **U8** | `packetPositiveScaling`, `correctionPositiveScaling`. | S | `force_eLpNorm_positive_epsilon` `TimeNormScaling.lean:117`, `vectorPhysicalForce_uniform_positive_time` `CorrectionVectorNorms.lean:60`, `eLpNorm_vector_le_sum` `VectorForceNorms.lean:47`, `coordinate_norm_parabolicForce` `:79`, U1 | two fields |
| **U9** | `packetNegativeScaling`, `correctionNegativeScaling`. | S | `force_eLpNorm_negative_epsilon` `TimeNormScaling.lean:133`, `memLp_homogeneousFourier_time` `HomogeneousTime.lean:108`, `vectorPhysicalForce_uniform_negative_time` `CorrectionVectorNorms.lean:83`, U1 | two fields |
| **U10** | `forceLowOrderBound` and `forceConvergence`. | M | `ThresholdAPI.negativeIndex` (= `negative_intermediate_index` `Paper3/Thresholds.lean:28`), `scalar_force_eLpNorm_mono` `CompactForceConvergence.lean:44`, `vectorPhysicalForce_all_negative_tendsto_zero` `CorrectionVectorNorms.lean:155`, `force_angular_L1/L2_tendsto_zero` `InsertionForceConvergence.lean:66,78`, U1 | two fields; reconcile the existential `r` with the source's fixed `r = −1` for the correction |

Critical path: **U1 → U8/U9/U10** closes the two Sobolev displays and the
convergence clause; **U2 → U3/U4 → U5** closes the energy rates; **U7** is
independent and is the item that also unblocks R46.

---

## 6. Open questions for review

1. Should the equation/divergence/blowup transport of `eq:scaling`
   (`STATEMENTS.md:281-286` item 1) live in `ScalingAPI` or in `R42`?  It is
   fully proved in source and currently unowned by any contract (§2.6).
2. `ScalingAPI.ε₀` versus `CorrectionAPI.ε₀`: should `R42` receive an equation,
   or should `I03` take a `CorrectionAPI` as a field (making the threading
   structural rather than an obligation on `R42`)?  The latter costs `I03` a
   dependency on `research/I02/Spec.lean` becoming a registered module.
3. `packetMixedScaling` is stated as the paper's equality.  If the equality is
   judged not worth U6, the ledger item `STATEMENTS.md:284` (`eq:packetFscale`)
   must be weakened to the bound that `compact_force_mixed_bound` already proves.
4. `forceLowOrderBound` gives one intermediate index `r` for both `F_ε` and
   `H_ε`.  The source proves the correction case with the fixed `r = −1`; if a
   single shared witness is awkward, split the field in two.
