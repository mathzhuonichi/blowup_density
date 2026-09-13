# D01 · P2 sub-lemma SL5 (Fourier longitudinal form) — attempts and route

Lane 089.  Deliverable: **Lemma A** (mandatory) proved; **Lemma B** and **Lemma C** proved too
(both S after A).  Module mirrors lane 079 (`Transverse.lean`) exactly, with the antisymmetric
curl pair `(∂ᵢ Z)_j − (∂ⱼ Z)_i` in place of the divergence sum `∑ⱼ (∂ⱼ Z)_j`.

New module: `formalization/NSFormalization/Section4/D01/Longitudinal.lean`
(imports `NSFormalization.Section4.D01.Transverse` and `NSFormalization.Section4.D01.LerayDatum`).

## What was proved (fully, no `sorry`/`axiom`; standard 3 axioms)

Five public declarations, `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(`research/D01/axioms_longitudinal.lean`):

1. `NSFormalization.Section4.D01.longitudinal_symm_of_curl_free` — the **cycles-convention**
   longitudinal form (the analytic heart):
   `∀ᵐ ξ, ∀ i j, ξᵢ · (angularFrequencyDilation.symm (A j)) ξ = ξⱼ · (angularFrequencyDilation.symm (A i)) ξ`.
2. `NSFormalization.Section4.D01.longitudinal_of_curl_free` — **Lemma A, exactly as briefed**
   (angular convention).  For `{Z : SmoothL2Field Space}`,
   `hcurl : ∀ i j x, partialDeriv i Z.field x j = partialDeriv j Z.field x i`, `(m : ℕ)`,
   `{A : RealVectorSobolev ((m:ℝ)+1)}`, `hA : IsSobolevDatum ((m:ℝ)+1) Z.field A`:
   `∀ᵐ ξ, ∀ i j, ((ξ i : ℝ):ℂ) * ((A j : FourierData) ξ) = ((ξ j : ℝ):ℂ) * ((A i : FourierData) ξ)`.
3. `NSFormalization.Section4.D01.Leray.mem_span_r3FreqVec_of_curl_free` — **Lemma B** (fibre fact):
   for `ξ ≠ 0` and `v : MNS2.R3C` with `∀ i j, ξᵢ vⱼ = ξⱼ vᵢ`,
   `v ∈ ℂ ∙ MNS2.r3FrequencyVectorComplex ξ`.
4. `NSFormalization.Section4.D01.Leray.lerayComplement_eq_self_of_longitudinal` — **Lemma C**
   (datum-level fixed point): for `(s : ℝ)`, `h : RealVectorSobolev s`, and the a.e. longitudinal
   hypothesis `∀ᵐ ξ, ∀ i j, ξᵢ (h j) ξ = ξⱼ (h i) ξ`:  `lerayComplement s h = h`.
5. `NSFormalization.Section4.D01.Leray.lerayComplement_eq_self_of_curl_free` — **the SL5
   deliverable, assembled**: `lerayComplement ((m:ℝ)+1) A = A` for a curl-free field's
   order-`(m+1)` datum (`= lerayComplement_eq_self_of_longitudinal … (longitudinal_of_curl_free …)`).

## Route (as executed)

Mirrors 079's two-theorem split (analytic heart in cycles convention, then dilation transport).

### `longitudinal_symm_of_curl_free` (steps 1–3), per pair `(i,j)`
* **Step 1 (`hsub0`).** `hreal_mixed a k` (a copy of 079's `hreal`, with the direction `a` and the
  component `k` decoupled) identifies `angularRealization m (angularDirectionalDerivative (m+1) eₐ (A k))`
  with `physicalDistribution ((componentField k Z).directionalField eₐ)` via
  `isSobolevDatum_partialDeriv a m hA` (`DerivativeDatum.lean:245`) at component `k`.  The scalar
  `(∂ᵢ Z)_j − (∂ⱼ Z)_i` is identically `0` by `hcurl`, so
  `angularDirectionalDerivative (m+1) eᵢ (A j) − angularDirectionalDerivative (m+1) eⱼ (A i) = 0`
  in `L²` by `angularRealization_injective m` (both physical distributions coincide,
  `physicalDistribution_apply` + `integral_congr_ae` + `hXfield i j`/`hXfield j i` + `hcurl i j`).
* **Step 2 (`hpeel`).** `angularDirectionalDerivative (m+1) a = cyclesToAngular m ∘ (M) ∘ (cyclesToAngular (m+1)).symm`
  definitionally, with `(cyclesToAngular s).symm = angularWeightEquiv (-s) ∘ angularFrequencyDilation.symm`
  (both reduce to `angularWeightMap (-s)`).  `(cyclesToAngular m).injective` + `map_sub` + `exact hsub0`
  peel the outer equivalence, giving
  `M_i (angularWeightEquiv (-(m+1)) (g j)) − M_j (angularWeightEquiv (-(m+1)) (g i)) = 0`
  with `g k = angularFrequencyDilation.symm (A k)`, `M_a = sobolevDirectionalDerivative (m+1) eₐ`.
* **Step 3 (cancel).** `sobolevDirectionalDerivative_coeFn` + `angularWeightEquiv_coeFn` give a.e.
  `σᵢ ξ · (W(ξ) · (g j) ξ) − σⱼ ξ · (W(ξ) · (g i) ξ) = 0`,
  where `σₐ ξ = 2πi · ξₐ · (1+‖ξ‖²)^{-1/2}` (via `EuclideanSpace.inner_single_right`) and
  `W = angularWeightSymbol (-(m+1))`.  The common factor `C = 2πi · (1+‖ξ‖²)^{-1/2} · W(ξ)` is
  nonzero, so `mul_eq_zero`/`sub_eq_zero` give the cycles-convention pair identity.  Combined over
  the finite `(i,j)` grid with `ae_all_iff.2` (twice).

### `longitudinal_of_curl_free` (step 4) — angular convention
Verbatim as 079's `transverse_of_divergence_free`, but the transported quantity is the pair
identity (per `(i,j)`, after two `ae_all_iff.2`) rather than the divergence sum:
`angularFrequencyDilation_coeFn` (079's helper, reused) gives `Â_k(ξ) = c^{-3/2} · (g k)(c⁻¹ξ)`;
transporting the cycles identity by the quasi-measure-preserving `ξ ↦ c⁻¹ξ`
(`hMP.quasiMeasurePreserving.ae` + `Measure.ae_smul_measure`) and cancelling `c⁻¹` then `c^{-3/2}`
(both `≠ 0`, `linear_combination`) yields `ξᵢ Â_j(ξ) = ξⱼ Â_i(ξ)` a.e.

### Lemma B — fibre linear algebra
`ξ ≠ 0 ⇒ ∃ k, ξ k ≠ 0`; then `v = (v k / ξ k) • ξ_ℂ` componentwise
(`Submodule.mem_span_singleton`, `PiLp.ext`, `PiLp.smul_apply`; per-coordinate `div_eq_iff` +
`linear_combination -hv k j`).  `(r3FrequencyVectorComplex ξ) j = (ξ j : ℂ)` is `rfl`.

### Lemma C — datum fixed point (mirror of `lerayComplement_eq_zero_of_transverse`)
`set b := assemble 2 volume (fun j => (h j : FourierData))`.  `coordinates_ae`/`coordinates_assemble`
give a.e. `(h j) ξ = (b ξ) j`; with the a.e. longitudinal hypothesis and the null set
`∀ᵐ ξ, ξ ≠ 0` (`by simp [ae_iff]`), Lemma B gives `∀ᵐ ξ, b ξ ∈ ℂ ∙ ξ_ℂ`, so
`lerayComplementL2_eq_self_of_longitudinal` (`LerayMultiplier.lean:257`) gives `lerayComplementL2 b = b`.
Then `PiLp.ext` + `Subtype.ext` + `lerayComplement_coe` + `coordinates_assemble` close
`lerayComplement s h = h`.

## What did NOT work / was fixed

* **One monolithic theorem timed out** at 200000 heartbeats (`whnf`/`elaborator`).  As in 079, split
  the analytic heart (`longitudinal_symm_of_curl_free`) from the dilation transport
  (`longitudinal_of_curl_free`); each then elaborates in ~5s.  No `maxHeartbeats` bump needed.
* **`rw [hXfield i j x, …]` at the pointwise integrand failed** — `integral_congr_ae
  (Filter.Eventually.of_forall (fun x => ?_))` leaves the goal as `(fun x => …) x = (fun x => …) x`
  (un-β-reduced), so `rw` did not find the pattern.  Fixed by `simp only [hXfield, smul_eq_mul,
  hcurl i j x]` (simp β-reduces), matching 079's `hreal` step.
* **`Lp.coeFn_sub` produces function subtraction `(⇑X − ⇑Y) ξ`, not `⇑X ξ − ⇑Y ξ`.**  Needed
  `rw [hsub, Pi.sub_apply, hd_i, hd_j, hw_j, hw_i]` (079 used the `Pi.add_apply` analogue for its
  triple sum).
* **`push_neg` is deprecated** in this toolchain.  Replaced the `∃ k, ξ k ≠ 0` extraction by
  `by_contra hcon; exact hξ (by ext k; simpa using not_exists.mp hcon k)`.

## Exact statements SL7b/SL8 will consume

* SL7b's fibre check `lerayComplementVectorL 0 (A⁰_h) = A⁰_{∇p}` and SL8's transport lemma
  `IsSobolevDatum s z A → IsSobolevDatum s ((I−P)z) (lerayComplement s A)` combine SL4's
  transversality (079) with SL5's longitudinality (this lane) fibre-wise.  For the pressure gradient
  (curl-free by Clairaut on the smooth pressure — `pressureGradient_curl_free`, still to be produced
  by the caller as `hcurl`), the direct consumer is
  `Leray.lerayComplement_eq_self_of_curl_free (Z := the `SmoothL2Field` wrapper of `∇p` obtained from the RESIDUAL side `f − ∇·(u⊗u) − ∂ₜu`, never from `∇p`'s own regularity — that is SL8's conclusion; review finding 4) hcurl m hA : lerayComplement ((m:ℝ)+1) A = A`,
  or, when the longitudinal a.e. condition is already in hand at an arbitrary order `s`,
  `Leray.lerayComplement_eq_self_of_longitudinal s A hlong : lerayComplement s A = A`.
* Lemma A `longitudinal_of_curl_free` supplies exactly the `hlong` hypothesis of Lemma C.
* The `hcurl` input (`∀ i j x, partialDeriv i Z.field x j = partialDeriv j Z.field x i`) is the
  right invariant for `∇p` (curl-freeness), **not** a datum for the pressure `p` (which
  `ClassicalSolutionR` never supplies) — see `research/D01/P2_SPLIT.md` SL5.

## Commands run

* `cd verification && lake build NSFormalization.Section4.D01.Longitudinal` →
  `Built … (5.5s)`, `Build completed successfully (9913 jobs)`.  No warnings from this module.
* `cd verification && lake env lean ../formalization/NSFormalization/Section4/D01/Longitudinal.lean`
  → silent (exit 0).
* `cd verification && lake env lean ../research/D01/axioms_longitudinal.lean` →
  all five public decls `depends on axioms: [propext, Classical.choice, Quot.sound]`.
* `make check` (worktree root) → `EXIT=0`.


## Review follow-up (lead, after REVIEW_LONGITUDINAL.md)

* The Clairaut step for `∇p` is 26 lines + a 6-line wrapper from `ClassicalSolutionR.pressure_smooth` via `D01.contDiff_slice_scalar` + `A05.dirDeriv_comm` (reviewer's probe); consumers must import `DatumToJets`.
* Order: `lerayComplement_eq_self_of_curl_free` is stuck at `(m:ℝ)+1 ≥ 1`; the order-0 seed (SL7b) must use the real-order `lerayComplement_eq_self_of_longitudinal s h hlong` at `s = 0`, or lower with lane 085's `lerayComplement_lowerVectorL`.
* Dropping `hcurl` would (with 079's SL4) force every divergence-free datum to be `0` — `hcurl` is load-bearing (reviewer probe).
* ~52 lines shared with `Transverse.lean` (`hreal_mixed` covers 079's `hreal`); SIMP item.
