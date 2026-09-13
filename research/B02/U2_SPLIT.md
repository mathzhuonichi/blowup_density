# B02 unit 2 `annularSchwartz` — sub-lemma split

Target (spec field `research/B02/Spec.lean:362-364`, single remaining hypothesis
of `Section4/B02/Cutoff.lean`'s `spatialApproxHomogeneous_of`):

```
∀ (s : ℝ) (δ R : ℝ), 0 < δ → δ < R → ∀ W : RealVectorSobolev s, IsAnnularDatum δ R W →
  ∃ ψ : Fin 3 → SchwartzMap Space ℝ, IsHomogeneousSliceDatum s (schwartzVector ψ) W
```

Rated **L** in `research/B02/COMPARISON.md:243`. New module:
`formalization/NSFormalization/Section4/B02/AnnularSchwartz.lean`.

## Definitions in play (all restated locally in `Annular`/`Cutoff`, do not import Data)

* `IsAnnularDatum δ R W` (`Annular.lean:67`): `∃ g : Fin 3 → Space → ℂ`,
  `∀ i, ContDiff ℝ ∞ (g i)`, `∀ i, tsupport (g i) ⊆ closedFrequencyAnnulus δ R`
  (`= {δ ≤ ‖ξ‖ ≤ R}`), `∀ i, ((W i : FourierData) : Space → ℂ) =ᵐ[volume] g i`.
* `IsHomogeneousSliceDatum s z G` (`Cutoff.lean:258`):
  `∃ U : VectorDistribution, IsSliceDistribution z U ∧ ∀ i, IsHomogeneousDatum s (G i) (U i)`.
* `IsSliceDistribution z U` (`Cutoff.lean:241`): `∀ i χ, U i χ = ∫ x, χ x * ((z x i : ℝ) : ℂ)`.
* `IsHomogeneousDatum s G u` (`Cutoff.lean:246`): `∀ φ`,
  `Integrable (fun ξ => φ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * G ξ))` **and**
  `angularFourierDistribution u φ = ∫ ξ, φ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * G ξ)`.
* `schwartzVector ψ x = WithLp.toLp 2 (fun i => ψ i x)`, so `schwartzVector ψ x i = ψ i x`.

## Route (per component `i`; assemble over `Fin 3`)

Manuscript `04-whole-space.tex:241` ("`ĥ_n = |ξ| G_n`, `h_n` Schwartz") and `:249`
("real parts").  Set `Gᵢ ξ := ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g i ξ` (byte-for-byte the
weight in `IsHomogeneousDatum`).  The realized field is `h = angularFourier⁻¹ Gᵢ`,
made real by taking real parts; its slice distribution is the datum's `U i`.

The angular convention machinery (all in `Paper3/AngularFourierDilation.lean`):
`angularFourier f ξ = frequencyUnit^(-3/2) • 𝓕 f (frequencyUnit⁻¹ • ξ)`
(`FourierConvention.lean:23`); `schwartzAngularDilation (𝓕 φ) ξ = angularFourier ↑φ ξ`
is `rfl` (`AFD:208`); `angularFourierDistribution ↑φ ψ = ∫ ξ, ψ ξ • angularFourier ↑φ ξ`
(`AFD:218`).  The Schwartz-level Fourier `𝓕`/`𝓕⁻` are Mathlib's `FourierTransform`
instances on `𝓢(V,E)` with `fourier_fourierInv_eq : 𝓕 (𝓕⁻ f) = f`
(`Mathlib/Analysis/Fourier/Notation.lean:217,222`, `@[simp]`).

| # | Sub-lemma (Lean-ready) | Size | Status | Blocker / inputs (file:line) |
|---|---|---|---|---|
| SL1 | `contDiff_rpow_mul_of_annulus {s δ R} (hδ : 0 < δ) {g} (hg : ContDiff ℝ ∞ g) (hsupp : tsupport g ⊆ closedFrequencyAnnulus δ R) : ContDiff ℝ ∞ (fun ξ => ((‖ξ‖^(-s):ℝ):ℂ) * g ξ) ∧ HasCompactSupport (…)` | **S** | **DONE** (this run) | `contDiff_iff_contDiffAt`; at `ξ₀ = 0`: `0 ∉ tsupport g` (since `‖0‖ = 0 < δ`), so `= 0` on `(tsupport g)ᶜ ∈ 𝓝 0`, `contDiffAt_const.congr_of_eventuallyEq` + `image_eq_zero_of_notMem_tsupport`; at `ξ₀ ≠ 0`: `contDiffAt_norm ℝ hξ` (InnerProductSpace/Calculus), `ContDiffAt.rpow_const_of_ne` (Pow/Deriv:624), `Complex.ofRealCLM.contDiff.comp_contDiffAt`, `ContDiffAt.mul`. Compact support: `HasCompactSupport.mul_left` (Support:483) + `tsupport g ⊆ closedBall 0 R` compact. |
| SL2 | `exists_schwartz_angularFourier_eq {f} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : ∃ φ : SchwartzMap Space ℂ, ∀ ξ, angularFourier ↑φ ξ = f ξ` | **S** | **DONE** (this run) | witness `φ := 𝓕⁻ (schwartzAngularDilationInv (ofCompactSupport f hf hc))`; `← schwartzAngularDilation_fourier_apply` (AFD:208), `fourier_fourierInv_eq` (Notation:217), helper `schwartzAngularDilation_dilationInv` (right inverse, copy of `AFD:58-64`), `ofCompactSupport` (`CompactSchwartz.lean:37`). |
| SL3 | `angularFourier_conj (φ : SchwartzMap Space ℂ) (ξ) : angularFourier (fun x => conj (φ x)) ξ = conj (angularFourier ↑φ (-ξ))` **and** the a.e. reality `g_conj_refl : (fun ξ => g i (-ξ)) =ᵐ[volume] (fun ξ => conj (g i ξ))`, combining to `angularFourier ↑(SchwartzMap.postcompCLM Complex.ofRealCLM (ψ i)) =ᵐ[volume] Gᵢ` where `ψ i := SchwartzMap.postcompCLM Complex.reCLM φᵢ` (real Schwartz — **the same object SL4a/SL4c use**, no `realPartSchwartz` in the conclusion) | **M** | TODO | `fourier_conjugate` (`RealSobolev.lean:61`) for the pointwise conj-reflection; `realSymmetry_ae` + `mem_realSubspace_iff` (`RealSobolev.lean:28,123`) + `(W i).property` + `((W i : FourierData) : Space → ℂ) =ᵐ g i` for `g_conj_refl` — **exact pattern in `Annular.lean:200-207`** (`hSym`). **Bridge to the ½(id+conj) decomposition** used for the linearity step: `postcompCLM ofRealCLM (postcompCLM reCLM φ) = realPartSchwartz φ` by `SchwartzMap.ext` + `SchwartzMap.postcompCLM_apply` (`Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:1052`) + `Complex.reCLM_apply`/`Complex.ofRealCLM_apply` + `realPartSchwartz_apply` (`RealSobolev.lean:87`). Real scalar `frequencyUnit^(-3/2) • conj z = conj (… • z)` via `map_smul`/`Complex.conj_ofReal`; `‖-ξ‖ = ‖ξ‖`, `‖ξ‖^(-s)` real ⇒ `Gᵢ(-ξ) =ᵐ conj (Gᵢ ξ)`. **Scope trap (a):** the module has no `open scoped ComplexConjugate` (`open` does **not** propagate through `import`, so `Annular.lean:56`'s open does not carry over) — add it or `conj` is an unknown identifier. **Scope trap (b):** `angularFourier` is a bare function, not a bundled map; route its additivity/homogeneity through the Schwartz CLM via `schwartzAngularDilation_fourier_apply` (`AFD:208`, `rfl`), or through `FourierTransform.fourier_add`/`fourier_smul` which — like `fourier_fourierInv_eq` — are `export`ed into `namespace FourierTransform` (`Notation.lean:97-98`) and are **not** reachable via `open scoped FourierTransform`. Only a.e. is needed (integral equality in SL4c); do **not** upgrade to reality of `φ i` (that needs an a.e.→everywhere + Fourier-uniqueness sub-project). |
| SL4a | `slice`: with `ψ i := SchwartzMap.postcompCLM Complex.reCLM φᵢ` (real Schwartz) and `U i := ((SchwartzMap.postcompCLM Complex.ofRealCLM (ψ i)) : 𝓢'(Space,ℂ))`, `IsSliceDistribution (schwartzVector ψ) U` | **S (trivial)** | TODO | the coercion lemma is `SchwartzMap.coe_apply` (`Mathlib/Analysis/Distribution/TemperedDistribution.lean:143`): `(f : 𝓢') g = ∫ x, g x • ↑f x`, already used at `AFD:221`. `U i` elaborates to `SchwartzMap.toTemperedDistributionCLM Space ℂ volume (postcompCLM ofRealCLM (ψ i))` = `coe_apply`'s LHS head, so it applies with no massaging; then `schwartzVector_apply` (`Cutoff.lean:62`) + `smul_eq_mul` on ℂ + `↑(postcompCLM ofRealCLM (ψ i)) x = ((ψ i x : ℝ):ℂ)`. |
| SL4b | `integ`: `∀ i φ, Integrable (fun ξ => φ ξ * (((‖ξ‖^(-s):ℝ):ℂ) * ((W i : FourierData) : Space → ℂ) ξ))` | **S** | TODO | integrand `=ᵐ φ ξ * Gᵢ ξ` (via `((W i : FourierData) : Space → ℂ) =ᵐ g i`); `Gᵢ` smooth compact support ⇒ bounded, `φ` Schwartz integrable ⇒ `Integrable.mul_bdd` (pattern: `Cutoff.lean:284` `integrable_schwartzVector`). `Integrable.congr` on the a.e. equal integrand. |
| SL4c | `pairing`: `∀ i φ, angularFourierDistribution (U i) φ = ∫ ξ, φ ξ * (((‖ξ‖^(-s):ℝ):ℂ) * ((W i : FourierData) : Space → ℂ) ξ)` | **M** | TODO | `angularFourierDistribution_schwartz_apply` (`AFD:218`) gives LHS `= ∫ ξ, φ ξ • angularFourier ↑(postcompCLM ofRealCLM (ψ i)) ξ`; `•=*`; SL3's a.e. `angularFourier ↑(postcompCLM ofRealCLM (ψ i)) =ᵐ Gᵢ`, and `Gᵢ =ᵐ ((‖ξ‖^(-s):ℝ):ℂ) * ((W i : FourierData) : Space → ℂ) ξ`; `integral_congr_ae` on the two integrands. Needs SL4b's integrability to justify the integrals agree. |
| SL4 | `annularSchwartz` assembly: choose `φᵢ` (SL2 with `f := Gᵢ` from SL1), `ψ i` real (SL3), `U i` (SL4a), package `⟨U, SL4a, fun i => ⟨SL4b i, SL4c i⟩⟩` | **M** | TODO | choose over `Fin 3` (destruct `IsAnnularDatum`'s `g, hg, hsupp, hae`); `Gᵢ := ((‖ξ‖^(-s):ℝ):ℂ) * g i ξ`. Conformance: register in `research/B02/axioms_u2.lean` that this term inhabits the spec field type. |

Critical path: SL1 → SL2 → SL3 → SL4c → SL4 (SL4a, SL4b independent, feed SL4).
**`s` range irrelevant** (manuscript's `-3/2 < s ≤ 0` is for the low/high split,
units 6/7): here `δ > 0` makes `‖ξ‖^(-s)` smooth on `tsupport g` for *every* real
`s`, so `annularSchwartz` is stated and proved with no constraint on `s` — matching
`Spec.lean:362` (unquantified `s`) and the docstring `Spec.lean:359`.

## This run

SL1 and SL2 proved in full (`AnnularSchwartz.lean`), `#print axioms` = the three
standard axioms.  Remaining L work: SL3 (reality, M), SL4a (trivial), SL4b (S),
SL4c (M), assembly SL4 (M).
