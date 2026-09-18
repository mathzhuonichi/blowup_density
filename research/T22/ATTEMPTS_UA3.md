# T22 U-A3 — `cutoffMultiplier` analytic core: attempts, positives and residual

Lane 397 (Opus). Target: `BoundedDomainNormAPI.cutoffMultiplier` verbatim
(`Section3/T22/Domain.lean`, `research/T22/Spec.lean:140-144`).

## What closed (positive results, all axioms `[propext, Classical.choice, Quot.sound]`)

`formalization/NSFormalization/Section3/T22/CutoffMultiplier.lean`:

1. `besselW t ξ := (1 + ‖ξ‖²)^(t/2)` and `besselW_nonneg`, `besselW_peetre`
   (Peetre, lane 386, in `besselW` spelling).
2. **`eLpNorm_besselWeight_scalarConvolution_le`** — the analytic engine. For every
   real `s`, integrable weighted kernel `K` and input transform `g` with
   `besselW s • g ∈ L²`:
   `eLpNorm (besselW s • scalarConvolution K g) 2 ≤ ofReal (peetreConst s · ∫ (1+‖ζ‖²)^{|s|/2}‖K ζ‖) · eLpNorm (besselW s • g) 2`.
   Proof: pointwise Peetre domination inside the convolution integral →
   `‖besselW s ξ • (K∗g) ξ‖ ≤ peetreConst s · (K̃ ∗ g̃) ξ` with `K̃ = besselW |s|·‖K‖`,
   `g̃ = ‖besselW s • g‖`; then Young `L¹∗L²→L²`
   (`Source.YoungConvolution.memLp_convolution_one_two`).
3. `cutoffMultiplierConst s χ := peetreConst s · ∫ (1+‖ζ‖²)^{|s|/2}‖angularFourier χ_ℂ ζ‖`,
   `cutoffMultiplierConst_nonneg`.
4. **`eLpNorm_cutoff_multiplier_le`** — engine specialized to `K = angularFourier χ_ℂ`
   for smooth compact `χ` (lane 391 kernel mass), constant `cutoffMultiplierConst s χ`.

This is the genuinely new analysis the split (`T22_SPLIT.md`, risk #1) says T22 owes:
the general-`s` `Peetre × kernel-mass × Young` `H^s` multiplier estimate. It is the
`L²`-operator content of the field.

## Why the verbatim field is NOT closed (residual — datum-model plumbing, not analysis)

The field quantifies over **every** tempered datum `A : RealVectorSobolev s`, and the
datum layer states `IsCutoffDatum` through `angularRealization` (a
weighted-angular-Fourier `L²` model), not through concrete functions. Closing it needs,
on top of the engine above, the following residual lemmas. None is new analysis; each is
model plumbing, but each is nontrivial and no in-tree proof exists.

**R1 — general-`A` datum ↔ weighted convolution identity (the long pole).**
For `A : RealVectorSobolev s` and smooth compact `χ`, define the candidate output datum
`b i : Lp ℂ 2 volume := fun ξ => besselW s ξ • scalarConvolution (angularFourier (fun x => (χ x:ℂ))) (fun η => besselW (-s) η • ((A i : FourierData) η)) ξ`.
Required:
```
∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
  angularRealization s (b i) ψ =
    angularRealization s ((A i : FourierData))
      (SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ)) ψ)
```
i.e. that multiplication by `χ` in physical space is, in the angular weighted-Fourier
`L²` model, convolution by `angularFourier χ_ℂ` on the reweighted datum. This is the
angular Fourier **product↔convolution** identity at the tempered/`L²` level. Mathlib
supplies only the Schwartz-level **forward** direction `𝓕(f∗g)=𝓕f·𝓕g`
(`Real.fourier_mul_convolution_eq`, `Mathlib/Analysis/Fourier/Convolution.lean`); the
product→convolution direction, its lift to `Lp` data by density, and the passage through
`angularFrequencyDilation`/`angularCoordinateRealization` and the `frequencyUnit`
normalization are all absent. This is a multi-file campaign of its own.

**R2 — real-subspace preservation.** `b i ∈ realSubspace s`
(`Source/RealSobolev.lean`), i.e. `realSymmetry (b i) = b i`, from
`realSymmetry (A i) = A i` and the real-evenness of `angularFourier χ_ℂ` for real `χ`
(`angularFourier_conj`). Needed for `b i : RealSobolevHilbert s` to typecheck, hence for
the vector `B : RealVectorSobolev s`.

**R3 — datum-norm ↔ eLpNorm identification and vector assembly.** `‖B i‖ₑ = eLpNorm (b i) 2`
and `‖A i‖ₑ = eLpNorm (fun η => besselW s η • ((A i) η)) 2` (identifying the
`realSubspace`/`Lp` norm with the weighted-transform `eLpNorm` the engine bounds), plus
the `PiLp 2` Pythagorean assembly `‖B‖ₑ² = ∑ i ‖B i‖ₑ²` to turn the per-component engine
bound into `‖B‖ₑ ≤ ofReal C · ‖A‖ₑ`.

**R4 — uniform positive constant.** The field needs `0 < C` for **all** `χ` (including
`χ = 0`, where `cutoffMultiplierConst = 0`). Take `C := cutoffMultiplierConst s χ + 1`;
the engine bound survives by `ENNReal.ofReal_le_ofReal` monotonicity.

## Failed / rejected approaches

- **Reuse a Mathlib spatial-multiplier theorem.** `Mathlib/Analysis/Distribution/Sobolev.lean`
  has `MemSobolev.fourierMultiplierCLM_of_bounded` (bounded **Fourier** multipliers) and
  scalar `MemSobolev.smul`, but **no** spatial multiplication by a Schwartz/cutoff
  preserving `MemSobolev`. Confirms U-A3 is genuinely new (as `T22_SPLIT.md` states).
- **Prove the field only for a Schwartz field `A` (smooth-datum fallback).** The graph
  conjunct is then easy (`angularRealization_datum`), but the norm conjunct
  `angularSobolevNorm s (χφ) ≤ C · angularSobolevNorm s φ` still needs R1 at the Schwartz
  level (product→convolution, absent in Mathlib) plus the `frequencyUnit` bookkeeping.
  So the smooth-datum case does **not** avoid the long pole; it only removes the general-`A`
  construction. Not delivered to avoid a sorry.
- **`LocalizationBoundary` + T13 fractional-kernel `0<s<1` route.** Covers only `s∈(0,1)`;
  the field is all real `s`. Cross-check only, never a substitute (`T22_SPLIT.md`).
