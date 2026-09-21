# D01 · P2 sub-lemma SL4 (Fourier transverse form) — attempts and route

Lane 079.  Deliverable: **Lemma A** (the bounded unit) proved; **Lemma B** (the corollary
for `∂ₜu`) deferred — its `SmoothL2Field (∂ₜu(t,·))` wrapper is, under `MemForceR f`, equivalent
to P2's own target `SmoothSquareIntegrableJets (∇p(t,·))`, so Lemma B must be sequenced after
SL7's non-circular order-0 seed rather than produce those jets.  Precise gap recorded below.

New module: `formalization/NSFormalization/Section4/D01/Transverse.lean`
(namespace `NSFormalization.Section4.D01`).

## What was proved (fully, no `sorry`/`axiom`; standard 3 axioms)

Three public declarations, `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(`research/D01/axioms_transverse.lean`):

1. `angularFrequencyDilation_coeFn` — pointwise coefficient of the normalized `L²`
   frequency dilation: `(angularFrequencyDilation h) ξ =ᵐ c^{-3/2} • h(c⁻¹ • ξ)`,
   `c = frequencyUnit`.  (Not available in this worktree — lane 076 **is** merged (PR #78) but
   is not an ancestor of this branch; and lane 076's `angularDirectionalMid_coeFn` is the
   coefficient of the **middle multiplier `M_s`**, a *different* operator, so it would not have
   supplied this dilation coefficient anyway.  Proved here as this module's own helper — see
   route below.  It is a `Paper3`-level fact, to be promoted to `Paper3/AngularFourierDilation.lean`
   by a SIMP lane; lane 085 is copying it meanwhile.)
2. `transverse_symm_of_divergence_free` — the **cycles-convention** transverse form (the
   analytic heart): `∀ᵐ ξ, ∑ⱼ ξⱼ · (angularFrequencyDilation.symm (A j)) ξ = 0`.
3. `transverse_of_divergence_free` — **Lemma A, exactly as briefed** (angular convention):
   for `{Z : SmoothL2Field Space}`, `hdiv : ∀ x, ∑ j, partialDeriv j Z.field x j = 0`,
   `(m : ℕ)`, `{A : RealVectorSobolev ((m:ℝ)+1)}`, `hA : IsSobolevDatum ((m:ℝ)+1) Z.field A`:
   `∀ᵐ ξ, ∑ j, ((ξ j : ℝ) : ℂ) * ((A j : FourierData) ξ) = 0`.

## Route as executed (differs from the brief only in how the dilation is handled)

### Step 1 — the diagonal derivative datum is the zero distribution
For each `j`, `isSobolevDatum_partialDeriv j m hA` (DerivativeDatum.lean:245, used as a black
box) gives the order-`m` datum of `∂ⱼ Z.field`, whose `i`-component is
`angularDirectionalDerivativeReal (m+1) eⱼ (A i)`.  Its diagonal (`i = j`) realization is
`physicalDistribution ((componentField j Z).directionalField eⱼ)`, whose field is
`(partialDeriv j Z.field x j : ℂ)`.  Summing over `j` and using
`hdiv` (`∑ⱼ partialDeriv j Z.field x j = 0`) plus `integral_finsetSum`
(integrability from `schwartz_smul_field_integrable`), the diagonal sum realizes `0`; by
`angularRealization_injective` the `L²` element `∑ⱼ angularDirectionalDerivative (m+1) eⱼ (A j)`
is `0`.

### Step 2 — peel the outer angular equivalence
`angularDirectionalDerivative s a = cyclesToAngular (s-1) ∘ (sobolevDirectionalDerivative s a)
∘ (cyclesToAngular s).symm` **definitionally**.  So the Step-1 sum is
`cyclesToAngular (m+1-1) (∑ⱼ M (kⱼ))` with `M = sobolevDirectionalDerivative (m+1) eⱼ` and
`kⱼ = (cyclesToAngular (m+1)).symm (A j)`; `(cyclesToAngular …).injective` gives
`∑ⱼ M (kⱼ) = 0` in `L²`.

### Step 3 — the coefficient identity, and cancel the common nonzero factor
`sobolevDirectionalDerivative_coeFn`:  `M (kⱼ) ξ =ᵐ sobolevDirectionalSymbol eⱼ ξ · (kⱼ) ξ`,
with (via `EuclideanSpace.inner_single_right`, `coordinateVector j = single j 1`)

    sobolevDirectionalSymbol eⱼ ξ = 2πi · ((ξ j : ℂ) · sobolevBesselWeight (-1) ξ),
    sobolevBesselWeight (-1) ξ = ((1+‖ξ‖²)^{-1/2} : ℝ).

`kⱼ = (angularWeightEquiv (m+1)).symm (angularFrequencyDilation.symm (A j))` (defeq), and
`angularWeightEquiv_coeFn (-(m+1))`:  `(kⱼ) ξ =ᵐ angularWeightSymbol (-(m+1)) ξ ·
(angularFrequencyDilation.symm (A j)) ξ`, where

    angularWeightSymbol s ξ = sobolevBesselWeight s (c•ξ) · sobolevBesselWeight (-s) ξ.

Reading off the coeFn of `∑ⱼ M (kⱼ) = 0` (via `Lp.coeFn_add`, `Lp.coeFn_zero`,
`Fin.sum_univ_three`) gives a.e.

    ∑ⱼ [2πi · (1+‖ξ‖²)^{-1/2} · angularWeightSymbol(-(m+1))(ξ)] · (ξ j) · (symm(A j)) ξ = 0.

The bracket `C(ξ) := 2πi · (1+‖ξ‖²)^{-1/2} · angularWeightSymbol(-(m+1))(ξ)` is **the exact
common coefficient**, and it is nonzero for every `ξ` (product of `2πi ≠ 0`, a positive real
Bessel weight, and `angularWeightSymbol(-(m+1)) ξ = (positive)·(positive) ≠ 0`).  Factoring
`C(ξ)` out (`linear_combination`) and cancelling it (`mul_eq_zero`) yields
`transverse_symm_of_divergence_free`:  `∀ᵐ ξ, ∑ⱼ (ξ j) · (angularFrequencyDilation.symm (A j)) ξ = 0`.

### Step 4 — angular convention (the actual Lemma A)
The datum `A` lives in the **angular** convention: `angularRealization s` feeds `A` through
`angularFrequencyDilation.symm` before realizing, so `angularFrequencyDilation.symm (A j)` is
the cycles-side object and the brief's `Â_j(ξ) = (A j : FourierData) ξ` is one dilation away.
The bridge uses only the forward coeFn:

* `angularFrequencyDilation_coeFn (angularFrequencyDilation.symm (A j))` with
  `apply_symm_apply` gives `(A j) ξ =ᵐ c^{-3/2} • (symm(A j))(c⁻¹ • ξ)`;
* transporting `transverse_symm_…` by the quasi-measure-preserving map `ξ ↦ c⁻¹•ξ`
  (`hMP.quasiMeasurePreserving.ae`, `Measure.ae_smul_measure`) gives
  `∀ᵐ ξ, ∑ⱼ (c⁻¹ξ)ⱼ · (symm(A j))(c⁻¹ξ) = 0`, i.e. `c⁻¹ · ∑ⱼ ξⱼ · (symm(A j))(c⁻¹ξ) = 0`;
* combining (`linear_combination`, cancel `c⁻¹` then `c^{-3/2}` — both `≠ 0`) gives
  `∀ᵐ ξ, ∑ⱼ (ξ j) · (A j) ξ = 0`.

### The dilation coeFn (`angularFrequencyDilation_coeFn`), how it was proved
`angularFrequencyDilation` is defined as an isometric extension, so its coeFn is not
`simp`-accessible.  It was identified with an explicit change of variables:
`Dfwd := c^{-3/2} • Lp.compMeasurePreserving (c⁻¹ • ·) hMP ((Lp.memLp h).smul_measure … ).toLp`,
where `hMP : MeasurePreserving (c⁻¹•·) volume (κ • volume)`,
`κ = ENNReal.ofReal |(c⁻¹)^{finrank}|⁻¹` from `Measure.map_addHaar_smul` (`finrank ℝ Space = 3`).
`Dfwd` has coeFn `c^{-3/2} • h(c⁻¹•)` (`Lp.coeFn_compMeasurePreserving` + `Lp.coeFn_smul` +
`hMP.quasiMeasurePreserving.ae (MemLp.coeFn_toLp)`).  `Dfwd = angularFrequencyDilation h` by
matching tempered distributions: `angularFrequencyDilation_toDistribution` +
`angularDistributionDilation_apply` on the RHS, `Lp.toTemperedDistribution_apply` on both, and
`Measure.integral_comp_inv_smul` (Jacobian `c^3`, amplitude `c^{-3/2}`, giving `c^{3/2}`) to
match the pairing; then injectivity `Lp.ker_toTemperedDistributionCLM_eq_bot`.

## What did NOT work / was rejected

* **Reading the coefficient of `angularDirectionalDerivative` directly as the mid symbol**
  `W_m · σ_a · W_{-(m+1)}` (as the brief suggested).  The operator is
  `cyclesToAngular`-conjugated, i.e. dilation-conjugated:
  `angularDirectionalDerivative s a = D ∘ (mult by μ) ∘ D.symm` with `D = angularFrequencyDilation`.
  The two dilations **cancel on the input** (`D (mult_μ (D.symm h)) ξ = μ(c⁻¹ξ) · h ξ`, the
  amplitudes `c^{-3/2}·c^{3/2}=1` and `h(c·c⁻¹ξ)=h ξ`), so the true a.e. coefficient is the
  mid symbol at `c⁻¹ξ`, **not** at `ξ`.  This does not change the conclusion (still `∝ ξⱼ`
  times a nonzero common factor), but any attempt to compute it needs a pointwise handle on
  `angularFrequencyDilation`, which no merged lemma provided — hence the explicit
  `angularFrequencyDilation_coeFn` above.  Peeling the outer equivalence by **injectivity**
  (Step 2) avoided computing the full composite coeFn and kept the dilation confined to a
  single `angularFrequencyDilation.symm`, used only in Step 4.
* **Avoiding the dilation entirely** — impossible: the datum `A` is in the angular convention
  (`angularRealization` = `angularCoordinateRealization ∘ angularFrequencyDilation.symm`), and
  the brief's conclusion is stated on `(A j : FourierData) ξ` directly, so relating it to the
  peeled cycles object genuinely requires the dilation coefficient.
* `Lp.coeFn_sum` — does not exist in Mathlib (noted in `B01/Temporal.lean`); expanded finite
  sums with `Fin.sum_univ_three` + `Lp.coeFn_add` instead.
* `set X := …` before `rw [← componentField_directionalField]` left an un-β-reduced
  `(fun j => …) j`; replaced by `simp only [hXfield, smul_eq_mul]`.
* `integral_finset_sum` is deprecated → `integral_finsetSum`.

## Lemma B — status: NOT proved. What it actually needs.

Lemma B would be `transverse_of_divergence_free (Z := wrapper) hdiv m hA` with
`Z.field = fun x => deriv (fun r => u.velocity (r,x)) t`.

**`hdiv` is free.** `∑ⱼ partialDeriv j Z.field x j` is *definitionally*
`spatialDivergence (fun p => temporalDerivative u.velocity p.1 p.2) t x` (checked `rfl` by the
reviewer — both `∑ⱼ partialDeriv j v x j = spatialDivergence (lift v) 0 x` and the `∂ₜu` slice
form are `rfl`), so lane 074's
`DivergenceTime.spatialDivergence_temporalDerivative_eq_zero w ht x` discharges it directly —
**no bridge lemma, no `show`, zero defeq work** (the earlier draft's "needs a short `show`/defeq
check" was wrong).

**`hA` is not free.** `A04.TimeDerivative.timeDeriv_isSobolevDatum` at order `m+1` (needs
`2 ≤ m+1`) delivers the right conclusion, but requires a datum path `G` that is
`ContDiffOn ℝ ∞ G (Ico 0 T)`. `ClassicalSolutionR.sobolev` (`SolutionClass.lean:132`) supplies
only `ContinuousOn G`, so the smooth-Sobolev-path hypothesis must be carried in by the caller
(as A02's energy-field lemmas do). D2's conclusion matches Lemma A's `hA` verbatim; this input
does not.

**The wrapper `Z : SmoothL2Field Space` is the real obstruction, and it is P2's own target.**
`SmoothL2Field` with field `z` is exactly `SmoothSquareIntegrableJets z`
(`DatumToJets.lean:298 memHInfty_iff_smoothSquareIntegrableJets`,
`:374 exists_smoothL2Field_of_memHInfty`), and for `MemForceR f`
`SmoothSquareIntegrableJets (∂ₜu(t,·)) ↔ SmoothSquareIntegrableJets (∇p(t,·))` by
`Pressure.lean`'s `pressureGradient_slice_smoothL2_of` (`:317`) /
`temporalDerivative_slice_smoothL2_of` (`:336`).  So **Lemma B cannot be the step that
establishes P2's jets** — it must run *after* SL7's non-circular order-0 seed has produced them.
That, not a technical wrapper, is why Lemma B is deferred.

Of the two sub-items the wrapper needs, neither is hard:
* **(a) all-orders spatial smoothness of the time-derivative slice** — not merged anywhere, but
  S-sized (~25 lines, verified by the reviewer): restrict to the open sub-slab
  `Ioo 0 T ×ˢ univ`, rewrite the slice as `x ↦ fderiv ℝ v (t,x) (1,0)` via
  `DivergenceTime.deriv_time_slice` (`:77`), then `ContDiffAt.fderiv_right (m := ∞) (by simp)`
  composed with `x ↦ (t,x)` and `ContinuousLinearMap.apply ℝ Space (1,0)`.  Parallel to
  `D01.contDiff_slice` (`DatumToJets.lean:366`); lane 074's first-order exchange lemmas are not
  used (the all-orders statement does not go through them).
* **(b) square-integrability of every spatial jet** — via `memHInfty_jets` this needs a datum at
  *every* natural order, and D2 gives only `m ≥ 2`.  Orders 0 and 1 follow by **datum order
  lowering, which already exists at the `IsSobolevDatum` level** (the earlier draft wrongly said
  it did not): `A03.IsScalarSobolevDatum.lower` (`ScalarTameProduct.lean:114`) plus
  `A03.isSobolevDatum_iff` (`VectorTameProduct.lean:54`, `Iff.rfl`) give the vector form in one
  term (reviewer compiled it).  Not a gap.

## Commands run

* `cd verification && lake build NSFormalization.Section4.D01.Transverse` → `Built … (6.1s)`,
  `Build completed successfully`.  No warnings originate from this module (the warnings shown
  are all from pre-existing upstream dependency files).
* `cd verification && lake env lean ../formalization/NSFormalization/Section4/D01/Transverse.lean`
  → silent.
* `cd verification && lake env lean ../research/D01/axioms_transverse.lean` →
  all three public decls `depends on axioms: [propext, Classical.choice, Quot.sound]`.
