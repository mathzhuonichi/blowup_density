# A05 — source-to-target comparison for `research/A05/Spec.lean`

Task `collaboration/tasks/A05.md`; graph node `A05`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:195-201`). Target: Lemma B.1
(`lem:critical-embeddings`, `paper/sections/appendix-b-embeddings.tex:11-49`)
on `R³`, in the form Propositions 4.3 (`prop:Rcritical1`,
`04-whole-space.tex:82-133`) and 4.4 (`prop:Rcritical2`, `:136-174`) consume it.

All Lean paths are relative to the worktree root. Line numbers are of the
declaration keyword.

---

## 0. Every use of Lemma B.1 in Sections 4.3–4.4

| # | site | field it is applied to | exact norms | constant |
|---|---|---|---|---|
| 1 | `04-whole-space.tex:92` | velocity slice `u(t)`, real 3-vector, `H^∞ ∩ L²_σ` | `‖u‖₃ ≤ C‖u‖_{Ḣ^{1/2}} = Cy` | universal `C` |
| 2 | `04-whole-space.tex:93` | gradient tensor `∇u` (9 entries) **and** `Λu` (3-vector) | `‖∇u‖₃ + ‖Λu‖₃ ≤ C‖u‖_{Ḣ^{3/2}} = Cz` | one universal `C` for the sum |
| 3 | `04-whole-space.tex:112` | gradient tensor `∇u`; RHS the vector `Δu` | `‖∇u‖₆ ≤ C‖Δu‖₂` (`Ḣ¹→L⁶` case + Plancherel `‖D²u‖₂ = ‖Δu‖₂`) | universal `C`, absorbed into `C₁` at `:111` |
| 4 | `04-whole-space.tex:153` | `u`, `∇u`, `Ju` | `‖u‖₃ ≤ CY`, `‖∇u‖₃ ≤ CZ`, `‖Ju‖₃ ≤ C(Y²+Z²)^{1/2}` with `Y=‖u‖_{H^{1/2}}`, `Z=‖∇u‖_{H^{1/2}}` — **inhomogeneous** | one universal `C`, absorbed into `C₀` at `:159` |
| 5 | `04-whole-space.tex:171` | `u`, and `∇u` through the reused `eq:RH1` | `‖u‖₃ ≤ CY ≤ Cθν` | same `C` |
| 6 | `appendix-a-local-theory.tex:54` | out of A05's declared scope (Appendix A's `eq:embeddings`, owned by A01/A03) | — | — |

Constants: `appendix-b-embeddings.tex:108-110`, "All constants depend only on
the fixed exponents, domain, and norm conventions, not on the field or its
frequency support." In particular no constant may depend on `ν`, on `t`, on the
solution, or on frequency support; `research/section4/STATEMENTS.md:465` makes
`ν`-freedom of `c, C₀, C₁` load-bearing for Theorem 4.1's converse.

Sites 4–5 are the reason `Spec.lean` also carries `homogeneousLeSobolev` and
`dotThreeHalvesLeGradientSobolev`: Proposition 4.4 reads Lemma B.1's homogeneous
right-hand sides against inhomogeneous `Y, Z`
(`research/section4/STATEMENTS.md:600-603`).

---

## 1. Field-by-field comparison

`Spec.lean` field | paper location | existing declaration (or gap) and its exact hypotheses | mismatch notes
---|---|---|---
`C`, `C_pos`, `Cderiv`, `Csix`, `Cbessel` and their positivity | `appendix-b-embeddings.tex:17,19,31,32`; `04-whole-space.tex:152` | Numeric candidates exist: `NSFormalization.RieszPotentialLp.potentialConstant` (`formalization/NSFormalization/Source/RieszPotentialLp.lean:15`, `= 4π/a + √(4π/(3−2a))`), `NSFormalization.Source.RieszFourierProfilePower.constant` (`.../RieszFourierProfilePower.lean:10`, `= π^{3/2−a}Γ(a/2)/Γ((3−a)/2)`), the literal `512^{1/p_a}` inside `RieszPotentialLp`, and `eLpNormLESNormFDerivOfEqInnerConst` (Mathlib) for the `L⁶` clause | The in-tree constants are for the **cycles** normalization; see §2. Kept as opaque structure fields so R43/R44 never depend on their value, only on `ν`-freedom.
`sameRealDistribution` | `appendix-b-embeddings.tex:97-99` ("The Euclidean statements use the preceding realizations of the derivatives"); the task's "same real vector/tensor distribution" | `Paper3.angularFourierDistribution_injective` (`Paper3/AngularSobolevClass.lean:22`); `Paper3.angularRealization_injective` (`Paper3/AngularFourierDilation.lean:203`); `Paper3.angularCoordinateRealization_injective` (`Paper3/AngularSobolevCoordinates.lean:156`); `Paper3.sobolevRealization_injective` (`Paper3/SobolevHilbertModel.lean:89`) | All four are injectivity of a *datum → distribution* map. The clause needed is injectivity of *physical field → distribution*, i.e. that `Data.IsSliceDistribution` has at most one solution. That is `TemperedDistribution.ext` on Schwartz tests and is **not stated anywhere in tree**; small gap.
`homogeneousDatumUnique` | `appendix-b-embeddings.tex:65-70`; `02-preliminaries.tex:63-70` ("isometric bijection onto `L²` … no polynomial ambiguity") | `Paper3.existsUnique_sobolev_datum` (`Paper3/SobolevHilbertModel.lean:122`) is the exact inhomogeneous analogue, hypothesis `TemperedDistribution.MemSobolev s 2 u`. `research/D01/RECONCILIATION.md` unit **L7** already books this as partially covered by `Source.FractionalRealization.realization_toDistribution` (`Source/FractionalRealization.lean:78`) for `0 < a < 3/2` | Homogeneous version is a gap. `Paper3/HomogeneousRealization.lean:7` says outright that a full `L² → 𝓢'` homogeneous multiplier is intentionally absent; the uniqueness statement does **not** need the multiplier, only injectivity of `G ↦ (φ ↦ ∫ φ·|ξ|^{-s}G)`, which is Cauchy–Schwarz plus `L²` duality.
`homogeneousLeSobolev` | `01-introduction.tex:105`; `appendix-b-embeddings.tex:69-70`; required at `a ∈ {1/2,1}` by `research/section4/STATEMENTS.md:602` | `Source.BesselFractionalData.symbol` (`Source/BesselFractionalData.lean:12`, `= ‖ξ‖^a⟨ξ⟩^{-a}`), `symbol_norm_le_one` (`:15`, needs `0 ≤ a`), `datum` (`:45`, the contraction `SobolevHilbert a →L L²`), `datum_norm_le` (`:55`, `‖datum h‖ ≤ ‖h‖`), `datum_coeFn` (`:49`), `multiplier_datum` (`:86`, the singular-cancellation identity, needs `0 ≤ a < 3/2`) | This is **exactly** the required inequality, already proved — but on cycles-convention scalar `SobolevHilbert a` data, not on the manuscript's angular real-vector `Data.sobolevENorm` / `dotHomogeneousENorm` of a physical field. `Source/BesselFractionalData.lean:45` *is* `Λ^a` at the datum level. Adaptation only.
`dotThreeHalvesLeGradientSobolev` | `appendix-b-embeddings.tex:103` ("Plancherel and `∑_j|ξ_j|²=|ξ|²`"); `04-whole-space.tex:150-157` | `Source.AngularGradientIdentity.angular_partial_norm_sq` (`Source/AngularGradientIdentity.lean:45`), `angularSobolevSq_succ` (`:81`), `vectorAngularSobolev_succ` (`:92`), `critical_inhomogeneous_identity` (`:107`, literally `‖F‖²_{H^{3/2}} = ‖F‖²_{H^{1/2}} + ‖∇F‖²_{H^{1/2}}`) | Closest match in the whole tree. Hypotheses are **`ContDiff ℝ ∞ F` and `HasCompactSupport F`**, and the norm is `vectorAngularSobolevNorm`, a literal Fourier integral valid only on `L¹∩L²`. Removing compact support for a general `H^∞` field is the adaptation.
`criticalRepresentative` | `appendix-b-embeddings.tex:65-70` ("a unique `L^{p_a}` representative for every element of the completion") | `Source.FractionalRepresentative.representative_memLp` (`Source/FractionalRepresentative.lean:19`), `Source.FractionalRealization.realization` (`Source/FractionalRealization.lean:44`, target `Lp ℂ (ENNReal.ofReal (targetExponent a))`), `Paper1.SchwartzCriticalEmbedding.normalizedCriticalPotential_toLp` (`Paper1/SchwartzCriticalEmbedding.lean:151`) | Present and strong: `realization_toDistribution` (`:78`) proves the `L^{p_a}` element *is* the original distribution, with no assumed physical/Fourier identification. Scalar and cycles-convention. `targetExponent a = 6/(3−2a)` (`Source/RieszPotentialLp.lean:14`) is literally the paper's `p_a`.
`rieszPowerExists`, `rieszPowerNorm` | `04-whole-space.tex:91` (`y = ‖Λ^{1/2}u‖₂`, `z = ‖Λ^{3/2}u‖₂`); `appendix-b-embeddings.tex:8` | `Source.BesselFractionalData.datum` (`:45`) is `Λ^a` on data (contractive, `0 ≤ a`); `Paper3.sobolevRealization_zero` (`Paper3/SobolevHilbertModel.lean:130`) identifies the order-0 realization with the genuine `L²` inverse Fourier transform, no `L¹` hypothesis; `Paper3.angularRealization` (`Paper3/AngularFourierDilation.lean:176`) is the angular counterpart | **Gap** as a statement about *physical fields*. The pieces are all there; what is missing is the packaging "`w` is the physical field whose transform is `|ξ|^a v̂`, and `‖w‖₂ = ‖v‖_{Ḣ^a}`". `D01/RECONCILIATION.md:192-197` explicitly leaves `Λ` to A05.
`besselPowerExists`, `besselPowerNorm` | `02-preliminaries.tex:51`; `04-whole-space.tex:147-152` | `Paper3.sobolevOrderLowering` (`Paper3/SobolevOrderLowering.lean:26`, contraction `SobolevHilbert s → SobolevHilbert r` for `r ≤ s`), `sobolevOrderLowering_norm_le` (`:39`), `sobolevRealization_orderLowering` (`:78`, preserves the distribution), `existsUnique_sobolev_datum` (`Paper3/SobolevHilbertModel.lean:122`) | `J^a` is the *identity on data* with a shifted order label (`SobolevHilbert _s` ignores `s`), so `besselPowerNorm` is nearly definitional once the datum/physical bridge exists. Adaptation only.
`tensorMemLp` | `appendix-b-embeddings.tex:22-25` ("Componentwise application gives the same statements for vector and tensor fields") | `Source.VectorForceNorms.eLpNorm_vector_le_sum` (`Source/VectorForceNorms.lean:47`); `Paper3.RealVectorPositiveDensity.physicalVector` / `physicalVector_smooth` (`Paper3/RealVectorPositiveDensity.lean:18,24`); `Paper3.memLp_angularRealVectorSlice` (`Paper3/AngularRealVectorBochner.lean:64`) | Present for `Fin 3 → ℝ` assemblies; here the codomain is `WithLp 2 (Fin 3 → Space)` (the 3×3 tensor of `Data.spatialGradient`, `Contracts/V1/Data.lean:446`). Purely structural.
`embeddingPair` (`a ∈ {1/2,1}`) | `appendix-b-embeddings.tex:19` eq:critical-embedding-pair, first inequality; `04-whole-space.tex:112` names the `a=1` case | **`a = 1/2`, Schwartz, scalar, cycles:** `Paper1.SchwartzCriticalEmbedding.criticalFieldLp_norm_le_datum` (`Paper1/SchwartzCriticalEmbedding.lean:171`) — RHS `‖criticalDatum φ‖`, which is `‖ |ξ|^{1/2}𝓕φ‖₂`, i.e. genuinely **homogeneous**. **Complete data, all `0<a<3/2`, scalar, cycles:** `Source.FractionalRealization.realization_norm_le_datum` (`Source/FractionalRealization.lean:96`) with `realization_toDistribution` (`:78`) — RHS `‖datum a h‖`, again the homogeneous datum. Supporting: `Source.RieszPotentialOperator.potentialOperator_norm_le` (`Source/RieszPotentialOperator.lean:97`), `Source.RieszComplexPotential.eLpNorm_complexPotential_le` (`Source/RieszComplexPotential.lean:57`) | Four mismatches, all adaptation, none a new campaign: (i) **scalar `ℂ`**, not real `Fin 3`-vector; (ii) **cycles convention** (`𝓕`), not the manuscript's angular transform — a `(2π)^{-a}` constant, §2; (iii) the headline lemma `criticalFieldLp_norm_le_weighted` (`:195`) has the **inhomogeneous** `‖weightedFourierLp (1/2) φ‖` on the right, so the *homogeneous* form is `criticalFieldLp_norm_le_datum` (`:171`) / `realization_norm_le_datum` (`:96`), not the one the blueprint row names; (iv) LHS is `‖·.toLp p volume‖ : ℝ` at `p = ENNReal.ofReal (targetExponent a)`, not `eLpNorm · 3 volume : ℝ≥0∞`. `Paper1/SchwartzCriticalEmbedding.lean:8` states the route is "the genuine Riesz-potential route at order `a = 1/2`" — the `a = 1` instance is not written but `realization` covers it.
`velocityCriticalL3` | `appendix-b-embeddings.tex:29`; `04-whole-space.tex:93,171` | Same as `embeddingPair` at `a = 1/2` | Also needs `ENNReal.ofReal (targetExponent (1/2)) = (3 : ℝ≥0∞)`; kept as its own field so R43/R44 never rewrite it.
`derivativeCriticalL3` | `appendix-b-embeddings.tex:30-31`; `04-whole-space.tex:94` | `Paper3.sobolevDirectionalDerivative` (`Paper3/SobolevDirectionalDerivative.lean:54`, `SobolevHilbert s →L SobolevHilbert (s−1)`, symbol `2πi⟨ξ,a⟩⟨ξ⟩^{-1}`), `sobolevRealization_directionalDerivative` (`:120`, realizes the actual distributional `∂_a`), `sobolevDirectionalDerivative_norm_le` (`:67`); plus `Source.AngularGradientIdentity.angular_partial_norm_sq` (`Source/AngularGradientIdentity.lean:45`) for `∑_j|ξ_j|²=|ξ|²` | The derivative-on-data ↔ derivative-on-distribution bridge is complete and hypothesis-free. **Gap:** nothing applies the critical embedding *to a derivative*; and the `Λu` summand needs `rieszPowerExists`. The `2π` in `sobolevDirectionalSymbol` (`:10`) is another cycles-convention marker.
`gradientLSix` | `appendix-b-embeddings.tex:32`; `04-whole-space.tex:110-112` | `NavierStokesR3.RieszTestOperators.smooth_eLpNorm_six_le` (`vendor/NavierStokesAndEuler/NavierStokes/R3/SmoothSobolevL6.lean:72`): for `{E}` any real inner-product space, `ContDiff ℝ 1 f` and `MemLp f 2 volume` give `eLpNorm f 6 ≤ C · eLpNorm (fderiv ℝ f) 2` with **no support hypothesis** and `C = eLpNormLESNormFDerivOfEqInnerConst volume 2`. Also `smooth_memLp_six` (`:133`), `smooth_eLpNorm_six_toReal_le` (`:140`), and the Paper 1 wrapper `NSFormalization.Paper1.velocitySlice_smooth_eLpNorm_six_toReal_le` (`formalization/NSFormalization/Paper1/SmoothL6Adapter.lean:34`) | **The strongest match in the deliverable.** It is already `ℝ≥0∞`-valued, already generic in the codomain (so `E := WithLp 2 (Fin 3 → Space)` gives the tensor case directly), and **Fourier-free**, hence carries *no* normalization risk. Remaining work is only `‖fderiv (∇v)‖₂ = ‖D²v‖₂ = ‖Δv‖₂` (Plancherel; booked as a D01 lemma item in `research/D01/RECONCILIATION.md:184`) and `MemLp (gradientTensor v) 2` from `MemHInfty`. Note `Paper1/SmoothL6Adapter.lean:11` warns it is "deliberately not … the missing critical `H^{1/2}→L³` embedding" — that warning is about the `L³` clause, not this one.
`besselCriticalL3` | `04-whole-space.tex:152-155` | No declaration bounds `‖Ju‖₃`. Ingredients: `embeddingPair` at `a=1/2` applied to `Jv`, plus `Source.AngularGradientIdentity.critical_inhomogeneous_identity` (`Source/AngularGradientIdentity.lean:107`) for `‖u‖²_{H^{3/2}} = Y²+Z²` | **Gap.** Depends on `besselPowerExists`. `critical_inhomogeneous_identity` requires `HasCompactSupport`, which must be removed.

### Summary of the gap surface

* **Present and directly reusable, modulo packaging**: the whole Riesz→`L^{p_a}`
  chain for complete scalar data at every `0 < a < 3/2`
  (`Source/FractionalRealization.lean:44,78,96`), the `Λ^a`-on-data contraction
  (`Source/BesselFractionalData.lean:45,55`), the `J^a` order shift
  (`Paper3/SobolevOrderLowering.lean:26,78`), the distributional `∂_a` on data
  (`Paper3/SobolevDirectionalDerivative.lean:54,120`), the angular↔cycles
  dilation (`Paper3/AngularFourierDilation.lean:80,142,176`), and the
  support-free `L⁶` bound (`vendor/.../SmoothSobolevL6.lean:72`).
  `formalization/blueprint/EXTERNAL_REUSE.md:36` is right that the Riesz Fourier
  bridge is present, not absent.
* **Genuinely missing**: (a) every statement about a *physical real 3-vector
  field* rather than a scalar `L²` datum; (b) the angular-normalization
  transport of the embedding constant; (c) `Λ` and `J` as relations on physical
  fields; (d) the application of the embedding to derivatives; (e) uniqueness of
  `Data.IsSliceDistribution`.
* **Not needed**: no new maximal-function or Riesz-kernel work. The kernel
  theory (`Source/Riesz*.lean`, ~25 modules) is complete through
  `potentialOperator_norm_le`.

---

## 2. Normalization constants

### 2.1 The three conventions in play

| | transform | homogeneous norm |
|---|---|---|
| Manuscript (`01-introduction.tex:91,105`) | `v̂(ζ) = (2π)^{-3/2}∫e^{-ix·ζ}v(x)dx` (unitary, angular) | `‖v‖²_{Ḣ^a} = ∫|ζ|^{2a}\|v̂(ζ)\|²dζ` |
| Tao, `[taodispersive]` Appendix A, eq. (A.11) | unnormalized `∫e^{-ix·ξ}v` **plus** a compensating `(2π)^{-3/2}` inside the norm formula | same number as the manuscript |
| Mathlib / all in-tree `Riesz*`, `Sobolev*`, `Bessel*` modules | `𝓕v(ξ) = ∫e^{-2πix·ξ}v(x)dx` (unitary, cycles) | `∫\|ξ\|^{2a}\|𝓕v(ξ)\|²dξ` |

### 2.2 Tao (A.11) versus the paper's angular convention: **the constant does not change**

`01-introduction.tex:111-115` (footnote): "Tao uses the unnormalized Fourier
transform and includes a compensating factor `(2π)^{-3/2}` in the Fourier
formula for the Sobolev norm on `R³`; the resulting norm agrees with ours
wherever finite." `appendix-b-embeddings.tex:52-54` repeats it: "Tao's Fourier
convention includes the compensating Plancherel factor specified in
Section~\ref{sec:intro}, so this is exactly the norm used here."

Both statements are about the **norm**, and both are correct: Tao's
`(2π)^{-3/2}∫e^{-ix·ξ}v` is the manuscript's `v̂`. The `L^{p_a}` side is a
physical-space norm and is convention-free. Hence `C_a` of
`eq:critical-embedding-pair` may be taken to be Tao's constant verbatim. **The
paper's angular convention introduces no factor relative to its cited input.**

The same holds for the torus half (`appendix-b-embeddings.tex:74-77`), where the
paper is explicit that Taylor's angular coordinates give *equivalent, not
identical*, norms — but that half is out of A05's scope.

### 2.3 The paper versus the in-tree cycles convention: a factor `(2π)^{-a}`

With `ζ = 2πξ` and `angularFourier f ζ = (2π)^{-3/2}𝓕f((2π)^{-1}ζ)`
(`Source/FourierConvention.lean:23`, `frequencyUnit = 2π` at `:15`):

```
‖ |ζ|^a v̂_ang ‖²_{L²} = ∫ |ζ|^{2a} (2π)^{-3} |𝓕v(ζ/2π)|² dζ
                      = (2π)^{2a} ∫ |ξ|^{2a} |𝓕v(ξ)|² dξ        (ζ = 2πξ)
```

so

```
‖v‖_{Ḣ^a, manuscript} = (2π)^a · ‖ |ξ|^a 𝓕v ‖_{L², cycles}.
```

At `a = 0` the factor is `1`, the required consistency check (both transforms
are unitary); so `‖·‖₂`, `‖Δv‖₂` and `‖∇v‖₂` are unaffected, and the
`gradientLSix` clause has **no normalization content at all**.

Consequence for the constants. `Paper1/SchwartzCriticalEmbedding.lean:171`
proves, in the cycles convention,

```
‖φ‖_{L^{p_a}} ≤ κ_a · ‖ |ξ|^a 𝓕φ ‖₂ ,
κ_a = |c_a|^{-1} · potentialConstant a · 512^{1/p_a},
c_a = π^{3/2−a} Γ(a/2)/Γ((3−a)/2)            (Source/RieszFourierProfilePower.lean:10)
potentialConstant a = 4π/a + √(4π/(3−2a))    (Source/RieszPotentialLp.lean:15)
```

Transported to the manuscript's normalization this is

```
‖v‖_{L^{p_a}} ≤ ( κ_a · (2π)^{-a} ) · ‖v‖_{Ḣ^a, manuscript},
```

i.e. **the in-tree constant must be multiplied by `(2π)^{-a}`**: `(2π)^{-1/2} ≈
0.3989` at `a = 1/2`, `(2π)^{-1} ≈ 0.1592` at `a = 1`. The direction is
harmless (the manuscript's homogeneous norm is the larger of the two for `a>0`,
so the transported inequality is weaker than the cycles one and no sharpness is
claimed anywhere), but it must be applied, not ignored.

`Spec.lean` keeps the constants opaque, so this factor is discharged once, inside
the implementation of `embeddingPair`, and never surfaces in R43/R44.

### 2.4 Where the factor is discharged in tree

`Paper3.angularFrequencyDilation` (`Paper3/AngularFourierDilation.lean:80`) is
the `L²` **isometry** implementing `k ↦ (2π)^{-3/2}k(·/2π)`, and
`angularDistributionDilation_weight_cancel` (`:142`) is the identity that moves
a Bessel weight across it. `Source.angularSobolevSq_eq_frequency_weight`
(`Source/FourierConvention.lean:50`) is the same computation for the
inhomogeneous weight, in the form
`∫(1+|ξ|²)^s|f̂_ang|² = ∫(1+(2π)²|ξ|²)^s|𝓕f|²`. The homogeneous analogue —
`∫|ξ|^{2s}|f̂_ang|² = (2π)^{2s}∫|ξ|^{2s}|𝓕f|²` — is **not** in tree and is the
single new normalization lemma A05 owes (unit **U2** below); it is a change of
variables with no analysis.

Additional convention markers confirming that the datum layer is cycles-based,
and therefore all of it needs U2: `sobolevDirectionalSymbol`
(`Paper3/SobolevDirectionalDerivative.lean:10`) carries an explicit `2π`;
`RieszSingularMultiplier.symbol a ξ = ‖ξ‖^{-a}` in the `𝓕` variable
(`Source/RieszSingularMultiplier.lean:17` via `RieszFrequencyCutoffs`);
`Source/FractionalRealization.lean:11` states outright "The convention here is
cycles frequency; angular normalization is separate."

### 2.5 Two further constant hazards, recorded

* **`Data.homogeneousFourierENorm` is not usable here.** Its own docstring
  (`Contracts/V1/Data.lean:400-406`) forbids applying it to a general `H^∞`
  slice: `angularFourier` is a pointwise Bochner integral and totalizes to a
  junk `0` off `L¹`. Stating `‖u‖₃ ≤ C·homogeneousFourierENorm (1/2) u` would be
  a **false** obligation for an `H^∞` field that is not `L¹`. `Spec.lean`
  therefore introduces `dotHomogeneousENorm`, the datum-infimum form built from
  `Data.IsHomogeneousSliceDatum`, whose failure mode is `⊤`.
* **`s = 3/2` is inside `Data.IsHomogeneousDatum`'s stated collapse range.**
  `Contracts/V1/Data.lean:313-315` says that for `s ≥ 3/2` the `Integrable`
  clause "fails for every nonzero `G`". That is the *Cauchy–Schwarz sufficient
  bound* failing, not the clause: for a field with `v̂ ∈ L²` the integrand is
  `φ·(|ξ|^{-3/2}G) = φ·v̂ ∈ L¹`, so the clause holds. Every use of
  `dotHomogeneousENorm (3/2)` in `Spec.lean` is guarded by `MemHInfty`, where
  `v̂ ∈ L²` is automatic. No `Ḣ^{3/2}` **space** and no `Ḣ^{3/2} ↪ L^∞` is
  asserted, per `appendix-b-embeddings.tex:101-102`.

---

## 3. Bounded implementation split

Ten units. `S` ≈ transcription or a one-page calculation; `M` ≈ a self-contained
lemma with a real proof; `L` ≈ several lemmas. No unit requires new
maximal-function or Riesz-kernel theory.

| unit | size | statement | builds on |
|---|---|---|---|
| **U1** | M | Uniqueness of `Data.IsSliceDistribution`, and uniqueness of `Data.IsHomogeneousSliceDatum` on `−3/2 < s < 3/2`; hence `dotHomogeneousENorm` is attained. Closes `sameRealDistribution`, `homogeneousDatumUnique`. | `Paper3/AngularSobolevClass.lean:22`; `Paper3/AngularFourierDilation.lean:203`; `Paper3/SobolevHilbertModel.lean:89,122`; `research/D01/RECONCILIATION.md` unit L7 |
| **U2** | M | The homogeneous angular↔cycles identity `∫\|ζ\|^{2a}\|v̂_ang(ζ)\|²dζ = (2π)^{2a}∫\|ξ\|^{2a}\|𝓕v(ξ)\|²dξ`, at the datum level: `IsHomogeneousDatum a G u` ↔ `𝓕u = (2π)^{a}|ξ|^{-a}·(dilate G)`. **This is the only place the `(2π)^{-a}` constant appears.** | `Source/FourierConvention.lean:15,23,50`; `Paper3/AngularFourierDilation.lean:80,142,176` |
| **U3** | S | `homogeneousLeSobolev`: an `H^a` field (`0 ≤ a < 3/2`) has an order-`a` homogeneous datum and `‖v‖_{Ḣ^a} ≤ ‖v‖_{H^a}`. | `Source/BesselFractionalData.lean:12,15,45,49,55,86`; U1, U2 |
| **U4** | M | `IsRieszPower` is inhabited and single-valued on `0 < a ≤ 3/2` for `MemHInfty` fields with finite homogeneous norm, with `‖Λ^a v‖₂ = ‖v‖_{Ḣ^a}`. Closes `rieszPowerExists`, `rieszPowerNorm`. | `Source/BesselFractionalData.lean:45` (`Λ^a` on data); `Paper3/SobolevHilbertModel.lean:130` (order-0 realization is the honest `L²` inverse transform); U1, U2, U3 |
| **U5** | S | `IsBesselPower` likewise, with `‖J^a v‖₂ = ‖v‖_{H^a}`. Closes `besselPowerExists`, `besselPowerNorm`. | `Paper3/SobolevOrderLowering.lean:26,39,78`; `Paper3/SobolevHilbertModel.lean:122`; U1 |
| **U6** | M | Scalar Euclidean critical embedding on the **completion**, in homogeneous form, at both `a = 1/2` and `a = 1`, cycles convention: `‖v‖_{L^{p_a}} ≤ κ_a‖ \|ξ\|^a𝓕v‖₂` with the `L^{p_a}` element identified as the original distribution. | `Source/FractionalRealization.lean:44,78,96` (already all `0<a<3/2`); `Source/FractionalRepresentative.lean:15,19,25`; `Paper1/SchwartzCriticalEmbedding.lean:171` as the Schwartz template; `Source/RieszPotentialOperator.lean:97` |
| **U7** | M | Real-3-vector + angular + `ℝ≥0∞` packaging of U6: closes `embeddingPair`, `velocityCriticalL3`, `criticalRepresentative`, and `ENNReal.ofReal (targetExponent (1/2)) = 3`. | U2, U6; `Paper3/RealVectorPositiveDensity.lean:15,18,24`; `Paper3/AngularRealVectorBochner.lean:47,54,64`; `Source/VectorForceNorms.lean:47` |
| **U8** | M | Apply U7 at `a = 1/2` to each `∂_j v` and to `Λv`, assemble by `∑_j\|ξ_j\|² = \|ξ\|²`. Closes `derivativeCriticalL3`. | `Paper3/SobolevDirectionalDerivative.lean:54,67,120`; `Source/AngularGradientIdentity.lean:45,81,92`; U4, U7 |
| **U9** | S | `gradientLSix` and `tensorMemLp`: instantiate the vendor `L⁶` bound at `E := WithLp 2 (Fin 3 → Space)`, then `‖fderiv (∇v)‖₂ = ‖D²v‖₂ = ‖Δv‖₂`. **Fourier-free; independent of U1–U8.** | `vendor/NavierStokesAndEuler/NavierStokes/R3/SmoothSobolevL6.lean:72,133,140`; `formalization/NSFormalization/Paper1/SmoothL6Adapter.lean:34`; D01 lemma item `‖D²z‖₂ = ‖Δz‖₂` (`research/D01/RECONCILIATION.md:184`) |
| **U10** | M | `besselCriticalL3` and `dotThreeHalvesLeGradientSobolev`: U7 at `a = 1/2` applied to `Jv`, plus the weight inequalities `\|ξ\|^{2a} ≤ ⟨ξ⟩^{2a}` and `\|ξ\|³ ≤ ⟨ξ⟩\|ξ\|²`. | `Source/AngularGradientIdentity.lean:107` (with `HasCompactSupport` removed); U3, U5, U7 |

Critical path for **R43**: U1 → U2 → U3 → U4 → U6 → U7 → U8, with U9 in
parallel. Critical path for **R44**: additionally U5 → U10. U9 alone already
discharges site 3 of §0 and is the natural first PR.

---

## 4. Does `Λ` have to be an operator here?

**No — and it must not be, in two of the three senses. It must be a relation.**

1. **Not as a `𝓢' → 𝓢'` multiplier.** `Paper3/HomogeneousRealization.lean:7`
   records that a full `L² → 𝓢'` homogeneous multiplier is deliberately absent
   in tree because `‖ξ‖` is not `HasTemperateGrowth` at the origin in the
   required sense. `research/D01/RECONCILIATION.md:192-197` reaches the same
   conclusion from the manuscript side and hands `Λ`, `J` to A03/A05/R43/R44.
   `Spec.lean` builds no such multiplier.
2. **Not as a total operator on a completed space either**, at the order that
   matters most: `appendix-b-embeddings.tex:101` refuses `Ḣ^{3/2}` as a space,
   yet `04-whole-space.tex:91` writes `z = ‖Λ^{3/2}u‖₂`. So there is no domain
   on which `Λ^{3/2}` could be a total map in this contract.
3. **But the quantities alone are not enough.** Two consumed clauses —
   `‖Λu‖₃` (`04-whole-space.tex:94`) and `‖Ju‖₃` (`:153`) — are `L³` norms **of
   the transformed field**, not `L²`-Fourier quantities of `u`. `Data.lean`'s
   `homogeneousFourierENorm` / `sobolevENorm` cannot express them. Something
   naming `Λu` as a field is unavoidable, and A05 is where it belongs.

`Spec.lean` therefore defines `IsRieszPower a v w` ("`w = Λ^a v`") and
`IsBesselPower a v w` ("`w = J^a v`") as graph relations between physical
fields, expressed *only* through `Data.IsHomogeneousDatum` at orders `a` and `0`
(respectively `Data.IsSobolevDatum`), plus `AEStronglyMeasurable w`. They are
made single-valued and norm-preserving by `rieszPowerExists` /
`rieszPowerNorm` / `besselPowerExists` / `besselPowerNorm`, which is exactly and
only what Propositions 4.3 and 4.4 use.

Recorded for later: if some downstream unit does want an operator, the honest
one already exists at the **datum** level and is
`Source.BesselFractionalData.datum a : SobolevHilbert a →L[ℂ] L²`
(`Source/BesselFractionalData.lean:45`), whose symbol is `‖ξ‖^a⟨ξ⟩^{-a}` — i.e.
`Λ^a` as a contraction from the `H^a` datum to the `Ḣ^a` datum. Promoting that
to physical fields is precisely unit U4, and no promotion to distributions is
needed.

`J` needs even less: `SobolevHilbert _s` ignores its order label
(`Paper3/SobolevHilbertModel.lean:21`), so `J^a` is the identity on data with a
relabelled realization, which is `Paper3.sobolevRealization_orderLowering`
(`Paper3/SobolevOrderLowering.lean:78`) read backwards.

---

## 5. Residual risks for review

1. **`AEStronglyMeasurable` inside the relations.** `IsRieszPower` /
   `IsBesselPower` carry measurability of `w` as part of the relation. Without
   it `eLpNorm w 3 volume` is a lower Lebesgue integral and the `Λu`/`Ju`
   bounds could be satisfied by a nonmeasurable representative. It is free in
   every application (U4/U5 produce an `L²` field), but it is a deliberate
   strengthening of the definition and should be ratified.
2. **`MemHInfty` and not `initialClassR`.** Solenoidality is irrelevant to every
   clause, so it is not assumed. R43/R44 apply these to `u(t)`, which is
   `MemHInfty` by `ClassicalSolutionR.velocity_smooth` + `.sobolev`
   (`Contracts/V1/Data.lean:625,636`); deriving that slice fact is R43/R44's
   obligation, not A05's.
3. **One constant for the sum in `derivativeCriticalL3`.** The paper writes
   `‖∇v‖₃ + ‖Λv‖₃ ≤ C‖v‖_{Ḣ^{3/2}}` with a single `C`; `Spec.lean` follows it.
   Splitting into two constants would be equivalent but would not match
   `04-whole-space.tex:94`.
4. **`besselCriticalL3` collapses two steps into one constant** (embedding at
   `a=1/2` applied to `Jv`, then `‖Jv‖_{Ḣ^{1/2}} ≤ ‖v‖_{H^{3/2}}`). That is the
   only form Proposition 4.4 uses; if R44's review wants the intermediate, it
   is `homogeneousLeSobolev` at `a = 1/2` applied to `Jv`.
5. **`Data.lean`'s `dotHThreeHalvesENorm` / `dotHHalfENorm`
   (`Contracts/V1/Data.lean:415,420`) are *not* the quantities used here.**
   They are the literal-Fourier-integral form, correct for the compact rescaled
   profiles of `eq:RnegativeScale` but junk on a non-`L¹` `H^∞` slice. A binding
   should record that `dotHomogeneousENorm s z = homogeneousFourierENorm s z`
   holds on `L¹ ∩ L²` fields and that Section 4 uses the two at disjoint sites.
6. **The torus half of `eq:critical-embedding-pair` is out of scope**, as is
   Appendix A's `eq:embeddings` (`appendix-a-local-theory.tex:54`). If R43/R44
   review finds a whole-space use of either, A05's scope must be re-cut.
