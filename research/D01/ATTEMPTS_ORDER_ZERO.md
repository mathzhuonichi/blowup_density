# SL7b-α — order-0 transverse Fourier identity (lane 094)

Module: `formalization/NSFormalization/Section4/D01/OrderZeroSymbol.lean`
Axiom audit: `research/D01/axioms_order_zero.lean` (all 20 public decls = `propext, Classical.choice, Quot.sound`).

## What is proved (Lemma A)

`orderZeroDatum_transverse_of_divergence_free (hz : MemLp z 2 volume) (hsmooth : ContDiff ℝ ∞ z)
   (hdiv : ∀ x, ∑ j, partialDeriv j z x j = 0) : ∀ᵐ ξ, ∑ j, (ξ j : ℂ) * ((orderZeroDatum hz j : FourierData) ξ) = 0`

i.e. the order-0 datum `OrderZeroDatum.orderZeroDatum hz` of a divergence-free smooth `L²` field is
transverse a.e., with the *same statement shape* as lane 079's `transverse_of_divergence_free`, but
seeded at order 0 from `MemLp 2` + smoothness only. **No integrability of the derivatives is used.**

## Why the 079/089 route does not work at order 0 (finding F5)

079/089 build the datum of `∂ⱼz` from the datum of `z` via `isSobolevDatum_partialDeriv`
(`DerivativeDatum.lean`), which needs `Z : SmoothL2Field` (all jets in `L²`) and `physicalDistribution_directionalField`
(`Source/PhysicalSobolevDistribution.lean`), whose proof calls
`integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable` with the hypothesis `Integrable (ψ • ∂ⱼz)`.
For a bare `MemLp` field `∂ⱼz ∉ L²`, and `ψ • ∂ⱼz` need **not** be integrable for Schwartz `ψ`
(negative example below), so that route is unavailable — the whole point of SL7b.

## Route as executed (positive)

1. **Analytic heart, `Cut.physical_pairing_zero`.** For every Schwartz `ψ`,
   `∑ⱼ ∫ (∂_{eⱼ}ψ) zⱼ = 0`. Proved by a cutoff limit: `χ_R(x) = χ(x/R)` with `χ = ContDiffBump ⟨1,2⟩`
   (Mathlib `Analysis.Calculus.BumpFunction`), test function `φ_R = χ_R·ψ` is **compactly supported**,
   so the per-direction IBP `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable` applies with all
   three integrability hypotheses discharged by compact support (`Cut.cs_pairing_zero`). Summing over
   `j` with `hdiv` kills the derivative side; Leibniz splits `∂(χ_R ψ)` into `A_R + B_R`.
   `B_R → ∑ⱼ∫(∂ⱼψ)zⱼ` by dominated convergence (`|χ_R|≤1`, `χ_R→1`), and
   `A_R → 0` because `‖∂(χ_R)‖ ≤ C/R` (`Cut.chi_deriv_bound`, chain rule + `‖fderiv χ‖` bounded on its
   compact support) times the fixed `L¹` mass `∫|ψ·zⱼ|` (`squeeze_zero_norm`,
   `tendsto_inv_atTop_zero`). Uniqueness of limits closes it.
2. **`tempered_div_zero`.** Hence `∑ⱼ ∂_{eⱼ}(componentLp hz j : 𝓢') = 0` as a tempered distribution
   (`TemperedDistribution.lineDerivOp_apply_apply` + `Lp.toTemperedDistribution_apply` + step 1).
3. **`fourier_transverse`.** Apply the distributional Fourier transform:
   `TemperedDistribution.fourier_lineDerivOp_eq` gives the symbol `2πi ξⱼ`;
   `MeasureTheory.Lp.fourier_toTemperedDistribution_eq` identifies `𝓕(zⱼ:𝓢')` with the `L²` transform
   `𝓕(componentLp hz j)`. Testing against Schwartz and cancelling `2πi` gives, for every Schwartz `ψ`,
   `∑ⱼ ∫ ξⱼ ψ(ξ) (𝓕 zⱼ)(ξ) = 0`. The **fundamental lemma of the calculus of variations**
   `MeasureTheory.ae_eq_zero_of_integral_contDiff_smul_eq_zero` (needs local integrability of
   `∑ⱼ ξⱼ 𝓕 zⱼ`, from `MemLp.locallyIntegrable` × `LocallyIntegrableOn.continuousOn_mul`) upgrades this
   to the a.e. identity `∑ⱼ ξⱼ (𝓕 zⱼ)(ξ) = 0`.
4. **Datum chain.** `orderZeroDatum hz j` = `cyclesToAngularReal 0 (realProjectionTo 0 (𝓕 (componentLp hz j)))`,
   so `angularFrequencyDilation.symm (orderZeroDatum hz j) =ᵐ 𝓕(componentLp hz j)` because the order-0
   angular weight symbol is `1` (`angularWeightSymbol_zero`) and `realProjection` fixes the
   conjugate-symmetric `𝓕` of a real function (`fourier_componentLp_mem`, `realProjection_eq_self`).
   Step 3 then gives the cycles form (`orderZeroDatum_transverse_symm`).
5. **Dilation transport (`transverse_of_transverse_symm`).** The normalized `L²` frequency dilation
   `angularFrequencyDilation` has a.e. coefficient `c^{-3/2} f(c⁻¹·)`
   (`Transverse.angularFrequencyDilation_coeFn`, lane 079).  The transport from the cycles form to
   the angular form is now a **standalone lemma** `transverse_of_transverse_symm {g : Fin 3 → FourierData}`
   (statement supplied by the lane-094 reviewer, F1), and `orderZeroDatum_transverse_of_divergence_free`
   is a one-line application of it to `orderZeroDatum_transverse_symm`.  Its proof body is lane 079's
   `transverse_of_divergence_free` §3 verbatim with `A j ↦ g j`.  **TODO (SIMP lane):** 079's
   `transverse_of_divergence_free` and 089's `longitudinal_of_curl_free` each carry their own copy of
   this transport (a third copy of the same κ/`hMP`/`hfwd` boilerplate); a SIMP lane should promote
   `transverse_of_transverse_symm` (and `angularFrequencyDilation_coeFn`) to
   `Paper3/AngularFourierDilation.lean` — as `Transverse.lean:60–64`'s docstring already plans — and
   rewrite both merged modules to consume it.  Those modules are frozen, so lane 094 does not edit
   them.

## Reused (not re-proved)
- `OrderZeroDatum.{orderZeroDatum, componentLp, componentLp_ae, fourier_componentLp_mem}` (SL7a, lane 090ish).
- `Transverse.angularFrequencyDilation_coeFn` (lane 079) — the a.e. dilation coefficient (this is
  what is reused; the transport *step* is now the module-local shared lemma `transverse_of_transverse_symm`,
  reviewer-supplied, not a re-proof of 079's transport).
- Mathlib: `ContDiffBump`, `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`,
  `TemperedDistribution.{lineDerivOp_apply_apply, fourier_lineDerivOp_eq, smulLeftCLM_apply_apply}`,
  `MeasureTheory.Lp.{fourier_toTemperedDistribution_eq, toTemperedDistribution_apply}`,
  `ae_eq_zero_of_integral_contDiff_smul_eq_zero`, `tendsto_integral_of_dominated_convergence`,
  `squeeze_zero_norm`, `LocallyIntegrable.integrable_smul_left_of_hasCompactSupport`.
- Paper3: `cyclesToAngular(Real)`, `angularWeightEquiv_coeFn`, `angularWeightSymbol`, `sobolevBesselWeight`.

## Negative examples / dead ends
- **Per-term IBP against a Schwartz test is not always available (F3, corrected).** The IBP lemma
  `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable` requires `Integrable (ψ • ∂ⱼz)` for the
  *given* `ψ`; it is enough that this fails for *some* Schwartz `ψ`.  Take a smooth `L²` field with
  `|∂₁z_j(x)| ~ |x|^{-3/2-ε} e^{x₁}` (e.g. `a·cos∘φ` with `a ~ |x|^{-3/2-ε} ∈ L²` and `|∇φ| ~ e^{|x|}`)
  and the Schwartz witness `ψ(x) ≈ e^{-|x|^{1/2}}` (smoothed): it and all its derivatives decay faster
  than every polynomial yet slower than any exponential, so `ψ|∂z| ~ |x|^{-3/2-ε} e^{x₁-|x|^{1/2}} → ∞`,
  not integrable.  (A Gaussian `ψ = e^{-|x|²}` *would* make it integrable — so the earlier claim "no
  Schwartz `φ` works" was too strong; "not every `φ` works, so `Integrable (ψ • ∂ⱼz)` cannot be
  discharged in general" is what holds and is what matters.)  Hence `physicalDistribution_directionalField`
  and `isSobolevDatum_partialDeriv` are unavailable at order 0, and the cutoff/`R→∞` argument is
  *necessary*, not a convenience.
- **No shortcut via density.** Mathlib has **no** lemma "C_c^∞ dense in Schwartz" and **no**
  "a tempered distribution vanishing on C_c^∞ is zero" (searched all of `Analysis/Distribution/`).
  So `tempered_div_zero` cannot be obtained by testing on C_c^∞ then extending by density; the IBP
  must be done against *all* Schwartz functions, which the cutoff argument achieves.
- **HeliCorgi's order-0 divergence bridge is NOT reusable for this direction.**
  `R3LerayComplexDivergenceBridge`/`R3ClassicalIncompressibility` only run *from* Fourier-side
  solenoidal membership (`u ∈ r3L2SolenoidalSubmodule`, itself *defined* as a.e. Fourier-transversality)
  *to* physical divergence-freeness. The physical→Fourier direction exists only at the *Schwartz*
  level (`R3SchwartzDivergence.r3Schwartz_rawDivergence_fourier_iff_classical`), i.e. for genuine
  Schwartz fields, not for a merely-`MemLp` smooth `z`. So no HeliCorgi lemma supplies Lemma A.
- Tactic note (F2, corrected — the reviewer re-ran the four pitfalls I first recorded and only one
  reproduces):
  * **Reproduces.** `(hasFDerivAt_id x).const_smul _` for `fun y => c • y` fails: `HasFDerivAt.const_smul`
    leaves the scalar *ring* a metavariable, so `HasFDerivAt (?c • id) (?c • ContinuousLinearMap.id ?R Space)`
    does not unify with the goal (a **metavariable/defeq** mismatch — *not* the `ContinuousSMul ℚ≥0`
    instance search I originally, wrongly, blamed).  Fix: give the scalar explicitly
    (`(hasFDerivAt_id x).const_smul (((n:ℝ)+1)⁻¹)`), or use `(c • ContinuousLinearMap.id ℝ E).hasFDerivAt`
    directly (what `chi_deriv_bound` does).
  * ~~`fderiv_mul` trips the same instance trap~~ — **does NOT reproduce**; `fderiv_mul hf hg` works
    directly and is shorter than the `show … from (hc_fd.mul hd_fd).fderiv` bridge used in `hterm`.
  * ~~`Tendsto.const_mul` trips the same trap~~ — **does NOT reproduce**; `(hcn0.const_mul C).mul_const M`
    + `simpa` (3 lines) works, shorter than the `Continuous.tendsto 0 ∘ …` route used in `hAlim`.
  * ~~`integral_finsetSum` needs an explicit `(f := …)` summand~~ — **does NOT reproduce**; it unifies
    without the hint in both the term and `rw … at` positions.
  The three "does-not-reproduce" workarounds are still in the proof (correct, just longer than needed) —
  a SIMP lane can shorten `hterm`/`hAlim`/`chi_deriv_bound` per the above; statements are unchanged.

## Lemma B (longitudinal / curl-free) — status and the review's factoring plan
Same technique, not implemented in this lane (Lemma A was the mandatory bounded unit).  The reviewer
prototyped the cheap route (`/tmp/rev094/lemB.lean`, compiles): replace the divergence sum
`∑ⱼ (∂ⱼψ)zⱼ` by the antisymmetric pair `(∂ₚψ)z_q − (∂_qψ)z_p` (using `hcurl : ∂ᵢzⱼ = ∂ⱼzᵢ`), giving
`ξᵢ Âⱼ = ξⱼ Âᵢ` a.e., with the corollary from lane 089's `Leray.lerayComplement_eq_self_of_longitudinal`.

**The factoring the reviewer recommends doing as the FIRST step of the Lemma-B lane (not an after-the-fact
SIMP):**
* Extract `cs_ibp` (the single-direction IBP `∫ φ • ∂_k(zc_j) = -∫ (∂_k φ) • zc_j`, currently inlined
  in `Cut.cs_pairing_zero`) and `fderiv_zc_eq'` (the two-index `fderiv (zc z j) x (cv k) = ↑(partialDeriv k z x j)`;
  the module currently proves only the `k = j` case at `fderiv_zc_eq`).
* Generalize the ~130-line cutoff machine `physical_pairing_zero` to a **constant weight-matrix** form
  `physical_weighted_pairing_zero (w : Fin 3 → Fin 3 → ℂ) (hw : ∀ x, ∑ j k, w j k * ↑(partialDeriv k z x j) = 0)
   (ψ) : ∑ j k, w j k * ∫ (∂_{cv k}ψ) • zc_j = 0`.  Divergence is `w = δ`; curl for `(p,q)` is
  `w q p = 1, w p q = -1`.  The cutoff/DCT/`C/R` machinery is index-independent (per-`j` DCT then sum,
  the weights are constants), so this is a mechanical generalization — same line count, written once.
* Also factor `fourier_transverse`'s inlined `hterm` (the single-component
  `𝓕(∂_k T_{z_j}) ψ = 2πi ∫ ξ_k ψ 𝓕z_j`) so Lemma B's Fourier step reuses it, and the shared
  `transverse_of_transverse_symm` (F1) for the dilation.
* Net: **Lemma B ≈ 30–40 lines** (`cs_antisym_pairing_zero` 7 lines + weight instance ~5 +
  `tempered_curl_zero`/`fourier_longitudinal` ~15 with `ae_all_iff` merging the 9 pairs + datum/dilation
  ~5).  Without the factoring it is ~150 lines (a second cutoff copy).

## SL7b remainder toward `(I−P) datum⁰(h) = datum⁰(∇p)` (P2 SL7(7b))
Lane 094 delivers the **transverse half** of the `eq:Rpressure` order-0 decomposition.  Remaining:
1. **Lemma B** (above) + 089's `lerayComplement_eq_self_of_longitudinal` ⟹ `(I−P) datum⁰(∇p) = datum⁰(∇p)`
   (curl-freeness of `∇p` from Clairaut / Mathlib second-derivative symmetry; `∇p` smooth from `ClassicalSolutionR`).
2. **`orderZeroDatum` additivity** `orderZeroDatum (h₁+h₂) = orderZeroDatum h₁ + orderZeroDatum h₂` —
   not in `OrderZeroDatum.lean`; cheapest via datum uniqueness (`angularRealization_injective` +
   `isSobolevDatum_orderZeroDatum`), ≈15 lines.
3. **`lerayComplement` linearity** — `LerayDatum.lean:118` `lerayComplementAmbientLM` (a `LinearMap`)
   already gives `lerayComplement_add` in a few lines.
4. **`MemLp 2` / `ContDiff ∞` of `∂ₜu(t,·)` and `∇p(t,·)`** (from `A02/SolutionClass` under `MemForceR f`,
   and `ClassicalSolutionR.pressure_gradient`) — the main remaining plumbing.
5. **`hdiv` slot already matches:** lane 074's `DivergenceTime.spatialDivergence_temporalDerivative_eq_zero u ht x`
   fills `∀ x, ∑ j, partialDeriv j (∂ₜu(t,·)) x j = 0` **by `rfl`** (reviewer-verified, `/tmp/rev094/sl7b.lean`).

So after 094, the SL7b critical path is **Lemma B → datum additivity + lerayComplement linearity →
`∂ₜu`/`∇p` `MemLp`**; only Lemma B contains new mathematics.
