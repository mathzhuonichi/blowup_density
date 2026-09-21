# B02 unit 2 (`annularSchwartz`) — SL3 / SL4a / SL4b attempts (lane 084)

Module: `formalization/NSFormalization/Section4/B02/AnnularReal.lean`
Conformance: `research/B02/axioms_u2_sl3.lean`
Split table: `research/B02/U2_SPLIT.md`

## What was proved (this run)

* **SL3** `angularFourier_realPart_ae` — for `W : RealVectorSobolev s`, `i`, a
  representative `g` of the `i`-th Fourier component
  (`((W i : FourierData) : Space → ℂ) =ᵐ g`), and a Schwartz `φ` realizing the
  homogeneous weight (`∀ ξ, angularFourier ↑φ ξ = ((‖ξ‖^(-s):ℝ):ℂ) * g ξ`), the
  complexified real part `postcompCLM ofRealCLM (postcompCLM reCLM φ)` has angular
  Fourier transform `=ᵐ[volume] fun ξ => ((‖ξ‖^(-s):ℝ):ℂ) * g ξ`.  A.e. only.
* **SL4a** `isSliceDistribution_schwartzVector` — for a real Schwartz vector `ψ`,
  the family `U i := ↑(postcompCLM ofRealCLM (ψ i)) : 𝓢'(Space,ℂ)` is the slice
  distribution of `schwartzVector ψ`.
* **SL4b** `integrable_weight_annular` — the homogeneous pairing
  `ξ ↦ φ ξ * (((‖ξ‖^(-s):ℝ):ℂ) * (W i) ξ)` is integrable.
* **SL4c** `angularFourierDistribution_realPart_pairing` — the distributional
  pairing of the complexified real part with a Schwartz test equals the weighted
  physical integral against `(W i)`.
* **SL4** `annularSchwartz` — the spec field itself (`Spec.lean:362-364`,
  byte-identical), assembled from SL1/SL2/SL3/SL4a/SL4b/SL4c.
* `spatialApproxHomogeneous` — the unconditional stage-4 diagonal density,
  `spatialApproxHomogeneous_of_units annularSchwartz` (`LebesgueDatum.lean`).
* Supporting: `angularFourier_conj`, `angularFourier_schwartz_add`,
  `angularFourier_schwartz_smul`, `postcompReCLM_ofReal_eq`,
  `angularFourier_realPart_apply`.

`#print axioms` on all eleven = `[propext, Classical.choice, Quot.sound]`.

## Route as executed

* **Conjugation of the transform** (`angularFourier_conj f ξ`): `unfold angularFourier`,
  then `fourier_conjugate` (`RealSobolev.lean:61`) on the inner `𝓕`, `smul_neg`
  to reconcile `frequencyUnit⁻¹ • (-ξ)` with `-(frequencyUnit⁻¹ • ξ)`, and
  `Complex.real_smul` + `map_mul` + `Complex.conj_ofReal` to pass the **real**
  dilation amplitude `frequencyUnit^(-3/2)` through `conj`.  Stated for a bare
  `f : Space → ℂ` (reusable), applied at `f := ↑φ`.
* **Linearity of the transform on Schwartz data** (`angularFourier_schwartz_add`,
  `_smul`): routed through the Schwartz-level CLM, not the bare integral.  Rewrite
  `angularFourier ↑a ζ = schwartzAngularDilation (𝓕 a) ζ` (`← schwartzAngularDilation_fourier_apply`,
  `AFD:208`, `rfl`), unfold `schwartzAngularDilation_apply` (`AFD:24`) to
  `frequencyUnit^(-3/2) • (𝓕 a)(pt)`, then `FourierTransform.fourier_add` /
  `FourierTransform.fourier_smul` (the SchwartzMap `FourierAdd`/`FourierSMul`
  instances, `Mathlib/.../SchwartzSpace/Fourier.lean:89,92`) and `add_apply` /
  `smul_apply` (the `Is{Add,SMul}Apply` simp lemmas).  For `_smul` the last step
  is `smul_comm` on two commuting scalars `frequencyUnit^(-3/2)` and `r` — this is
  why the **`ℝ`-homogeneity never touches the ℂ-linear map's `map_smul`**.
* **½(id+conj) bridge** (`postcompReCLM_ofReal_eq`): `postcompCLM ofRealCLM
  (postcompCLM reCLM φ) = (1/2:ℝ) • (φ + conjugateSchwartz φ)` by `SchwartzMap.ext`,
  `SchwartzMap.postcompCLM_apply` (×2), `Complex.reCLM_apply`,
  `Complex.ofRealCLM_apply`, then `exact (realPartSchwartz_apply φ x).symm`
  (`RealSobolev.lean:87`); the RHS `(1/2)•(φ x + conj (φ x))` is **defeq** to
  `realPartSchwartz φ x`, so `exact` closes it up to defeq with no `Complex.ext`.
* **Pointwise real-part identity** (`angularFourier_realPart_apply`): chain the
  bridge with the two linearity lemmas and `angularFourier_conj`, plus the funext
  `↑(conjugateSchwartz φ) = fun x => conj (φ x)` (`conjugateSchwartz_apply`).
  Result: `angularFourier ↑(re-part φ) ξ = ½(angularFourier ↑φ ξ +
  conj (angularFourier ↑φ (-ξ)))`, everywhere.
* **Reality of the datum** (inside SL3): `(W i).property` + `mem_realSubspace_iff`
  (`RealSobolev.lean:123`) + `realSymmetry_ae` (`:28`) give the a.e. conjugate
  reflection of `(W i)`; combined with `hae` and its `neg`-pushforward
  (`measurePreserving_neg …).quasiMeasurePreserving.ae`) this is the a.e.
  `conj (g (-ξ)) = g ξ`.  **Exact pattern of `Annular.lean:200-207`.**  Lift to the
  weighted transform with `map_mul`, `Complex.conj_ofReal` (real weight),
  `norm_neg`.  Finally combine `angularFourier_realPart_apply` with the a.e.
  Hermitian symmetry: `½(z + z) = z` via `Complex.real_smul; push_cast; ring`.
* **SL4a**: `IsSliceDistribution` unfolds to a pairing equation; `SchwartzMap.coe_apply`
  (`TemperedDistribution.lean:143`) turns the distribution action into
  `∫ x, χ x • ↑(postcompCLM ofRealCLM (ψ i)) x`, then `simp only`
  [`SchwartzMap.postcompCLM_apply`, `Complex.ofRealCLM_apply`, `smul_eq_mul`,
  `schwartzVector_apply`] closes both integrands to `χ x * ((ψ i x : ℝ):ℂ)`.  The
  product order came out `χ x * …` on both sides — **no `mul_comm` needed** (the
  scope trap the brief flagged did not bite because `coe_apply` puts the test `χ`
  first, matching `IsSliceDistribution`).
* **SL4b**: `contDiff_rpow_mul_of_annulus` (SL1) gives `Gᵢ` smooth with compact
  support; `φ.continuous.mul Gᵢ.continuous` is continuous and `hGcs.mul_left` is
  compactly supported, so `Continuous.integrable_of_hasCompactSupport` gives
  `Integrable (fun ξ => φ ξ * Gᵢ ξ)`; then `Integrable.congr` with `hae`
  (a.e. `(W i) ξ = g ξ`) transports to the datum integrand.  Did **not** need the
  `Integrable.mul_bdd` route the brief suggested — the continuous-compact-support
  route is shorter and avoids producing a bound constant.

## Failures / friction along the way

1. **Scope trap (a) confirmed real.**  `conj` is unknown without
   `open scoped ComplexConjugate` (the `open` in `Annular.lean:56` does not
   propagate through `import`).  Added it to the module header.
2. **`FourierTransform.fourier_add`/`fourier_smul` must be qualified** — like
   `fourier_fourierInv_eq`, they are `export`ed into `namespace FourierTransform`
   and are *not* brought in by `open scoped FourierTransform` (which opens only the
   `𝓕`/`𝓕⁻` notation).  Used the fully-qualified names inside `simp only`.
3. **`ℝ`-homogeneity of `schwartzAngularDilation`.**  Initial plan was to push the
   `(1/2:ℝ)` through the ℂ-linear CLM `schwartzAngularDilation` via `map_smul`,
   which fails for an ℝ scalar (needs `map_smul_of_tower`).  Avoided entirely by
   unfolding `schwartzAngularDilation_apply` first and finishing the real-scalar
   commutation with `smul_comm` on two `ℝ`-scalars — no tower lemma required.
4. **`postcompReCLM_ofReal_eq` final step.**  The `Complex.ext <;> simp[…] <;> ring`
   copy of `realPartSchwartz_apply` compiled but emitted unused-simp-argument and
   `<;>`-seq-focus linter warnings.  Replaced with `exact (realPartSchwartz_apply
   φ x).symm`, which closes the goal up to defeq (`(1/2)•(φ x + conj (φ x))` is
   defeq `realPartSchwartz φ x`) and is warning-free.

## Exact statements SL4c / the SL4 assembly will consume

With `φᵢ` from SL2 (`exists_schwartz_angularFourier_eq` on `Gᵢ := SL1 output`),
`ψ i := SchwartzMap.postcompCLM Complex.reCLM φᵢ`, and
`U i := ((SchwartzMap.postcompCLM Complex.ofRealCLM (ψ i) : SchwartzMap Space ℂ) :
𝓢'(Space,ℂ))` (note `postcompCLM ofRealCLM (ψ i)` **is** the SL3 subject,
`postcompCLM ofRealCLM (postcompCLM reCLM φᵢ)`):

* `angularFourier_realPart_ae W i hae hφ :`
  `angularFourier ↑(SchwartzMap.postcompCLM Complex.ofRealCLM
     (SchwartzMap.postcompCLM Complex.reCLM φ))
   =ᵐ[volume] fun ξ => ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ`
  with hypotheses `hae : ((W i : FourierData) : Space → ℂ) =ᵐ[volume] g` and
  `hφ : ∀ ξ, angularFourier ↑φ ξ = ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ`.
* `isSliceDistribution_schwartzVector ψ :`
  `IsSliceDistribution (schwartzVector ψ)
     (fun i => ((SchwartzMap.postcompCLM Complex.ofRealCLM (ψ i) : SchwartzMap Space ℂ)
       : 𝓢'(Space,ℂ)))`.
* `integrable_weight_annular hδ W i hg hsupp hae φ :`
  `Integrable (fun ξ => (φ : Space → ℂ) ξ *
     (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * ((W i : FourierData) : Space → ℂ) ξ)) volume`
  with `hδ : 0 < δ`, `hg : ContDiff ℝ ∞ g`,
  `hsupp : tsupport g ⊆ closedFrequencyAnnulus δ R`, `hae` as above.

SL4c: `angularFourierDistribution_schwartz_apply` (`AFD:218`) gives the pairing
`= ∫ ξ, φ ξ • angularFourier ↑(postcompCLM ofRealCLM (ψ i)) ξ`; rewrite `• = *`
(`smul_eq_mul`), then `integral_congr_ae` fed by `filter_upwards
[angularFourier_realPart_ae W i hae hφ, hae]` and `rw [smul_eq_mul, h1, h2]`.
**SL4c needs no integrability input** — `integral_congr_ae` only needs the a.e.
equality of the integrands (`MeasureTheory.integral_congr_ae`); SL4b feeds the
*other* (`Integrable …`) conjunct of `IsHomogeneousDatum`, not SL4c.  So
`IsHomogeneousDatum` for component `i` is `⟨integrable_weight_annular …,
angularFourierDistribution_realPart_pairing …⟩`, and the SL4 assembly
(`annularSchwartz`) packages `⟨fun i => postcompCLM reCLM (φ i), fun i => U i,
isSliceDistribution_schwartzVector _, fun i χ => ⟨…, …⟩⟩`.

**Update (same lane): SL4c + SL4 were then completed** (the reviewer verified the
route compiles).  Added to `AnnularReal.lean`:
`angularFourierDistribution_realPart_pairing` (SL4c, exactly the four tactic lines
above), `annularSchwartz` (the spec field, byte-identical to `Spec.lean:362-364`,
`_hδR : δ < R` kept unused), and `spatialApproxHomogeneous =
spatialApproxHomogeneous_of_units annularSchwartz` (the unconditional stage-4
diagonal, importing `Section4.B02.LebesgueDatum`).  All 11 declarations
`#print axioms` = the three standard axioms; the conformance `example` in
`axioms_u2_sl3.lean` shows `annularSchwartz` inhabits the spec field type verbatim.

## Commands run

From the worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, lake from `verification/`:

* `lake build NSFormalization.Section4.B02.AnnularReal` → `Build completed
  successfully (8817 jobs).`, `Built … AnnularReal`, no warnings from the module.
* `lake env lean ../formalization/NSFormalization/Section4/B02/AnnularReal.lean`
  → prints nothing, exit 0.
* `lake env lean ../research/B02/axioms_u2_sl3.lean` → all eight declarations
  `[propext, Classical.choice, Quot.sound]`.
* `grep -nE 'sorry|admit|native_decide|maxHeartbeats|axiom'` on the module → no match.
