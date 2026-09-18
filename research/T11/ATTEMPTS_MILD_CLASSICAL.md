# ATTEMPTS — 334-T11 / U9d2c (`Section3/T11/MildClassical.lean`)

Non-generated working notes for the lane that closed the U9d target.
No residual named input: the module contains no `def … : Prop`.

## 0. What the two open residuals really needed

Lanes 326/327 recorded the two open fields as

```lean
velocity_smooth : ContDiffOn ℝ ∞ (torusPhysicalVelocity u) (Ico (0:ℝ) T ×ˢ (univ : Set Space))
pressure_smooth : ContDiffOn ℝ ∞ (mildPressure g u)        (Ico (0:ℝ) T ×ˢ (univ : Set Space))
```

and both were blocked on "iterating the time derivative needs the mild equation
at Sobolev orders 5, 7, …".  That diagnosis is right, and lane 330's
`persistence_unconditional` supplies exactly those orders.  What was missing was
a way to convert *coefficientwise* differentiation into a statement about the
`PeriodicSobolev`-valued path, and then into joint smoothness of the Fourier
series on a half-open slab.

## 1. Route that failed: coefficientwise induction

The first plan was to differentiate the coefficient identity of lane 327
(`mild_physicalCoeff_hasDerivAt`) repeatedly.  The obstruction is the
nonlinearity: `∂_t^n Q̂(t,k)` requires termwise differentiation of the
convolution `∑'_l ĉ_j(t,l) ĉ_i(t,k-l)` in the summation variable `l`, i.e. a
locally uniform bound on the derivative series.  Mathlib's termwise
differentiation lemmas (`hasFDerivAt_tsum_of_isPreconnected`,
`contDiff_tsum`) are stated on **open** sets / globally, and the target window
`Ico 0 T` is half-open at `0`, where the derivative is one-sided.  Abandoned.

## 2. Route that worked: Banach-valued induction, two orders per derivative

Every time derivative is paid for with two Sobolev orders, and persistence
supplies every order, so the induction never runs out:

* `mildTowerDeriv ν m Pm w2 w3 t := νΔ(w₂ t) + (P_m t − Q_m t)` with
  * `νΔ` the bounded multiplier `−ν·4π²|k|²·W(k)⁻¹ : H^{m+2} →L H^m`
    (`mildLaplaceCLM`, built on lane 313's `torusMultiplierCLM`);
  * `P_m t = torusLerayCLM m (F_m t)`, `F_m` the order-`m` datum path of `g`;
  * `Q_m t` the order-`(m+3)` projected convolution of lane 328
    (`torusConvolutionCLM_real`) descended one order by `persistenceDown`.
* `mildTowerDeriv_coeff` identifies its coefficients with
  `W(k)^{m/2}·mildDerivCoeff C P u t i k`, i.e. with lane 327's derivative
  coefficients.
* The **integral identity** `v_m b = v_m 0 + ∫₀^b D` in `H^m` is proved by
  `torusDatum_ext` plus `torusCoeff_intervalIntegral` (lane 330) and the scalar
  FTC `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`, whose
  one-sided hypothesis `HasDerivWithinAt … (Ioi x) x` on `Ioo 0 b` is exactly
  what lane 327 gives.
* Differentiating the identity needs a *globally* continuous integrand, so `D`
  is clamped to a closed subwindow `Icc 0 b'` with `b' = (t+T)/2` before
  `intervalIntegral.integral_hasDerivAt_right` is applied; `Ico 0 b'` is a
  neighbourhood of `t` within `Ico 0 T`, so `HasDerivWithinAt.congr_of_eventuallyEq`
  transports the derivative back.
* `contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ico 0 T)` then closes the
  induction step.  The induction is on the smoothness order `j`, uniformly in
  the Sobolev order `m` (`mildTower_contDiffOn_nat`).

### 2.1 Force paths

The same shape proves that the order-`m` datum path of a smooth unit-periodic
space-time field is `C^∞` in time (`datumPath_contDiff`).  The scalar input is
differentiation under the **cube** integral
(`NSFormalization.Paper1.periodicFourierCoeff_eq_cube` turns
`periodicFourierCoeff` into `∫ y, … ∂cubeMeasure`, a finite measure on a compact
box, so `hasDerivAt_integral_of_dominated_loc_of_deriv_le` applies with a
constant dominating function obtained from
`IsCompact.exists_bound_of_continuousOn` on
`Icc (t−1) (t+1) ×ˢ toSpace '' Icc 0 1`).  Working with the quotient-torus
integral instead would have required joint continuity of
`(t,q) ↦ torusLift (h (t,·)) q`, which the tree does not have.

## 3. Joint smoothness on the slab

There is no `contDiffOn_tsum` in Mathlib.  The fix is to move the `x`-dependence
into a **functional-valued** series:

```lean
torusEvalSeriesCLM s i x : PeriodicSobolev s →L[ℝ] ℂ := ∑' k, χ_k(x) • torusPhysicalCoeffCLM s i k
```

The terms are `‖·‖ ≤ W(k)^{-s/2}` uniformly in `x`, so `contDiff_tsum` (global
in `x`, which is all of `Space`) gives `ContDiff ℝ n (torusEvalSeriesCLM s i)`
as soon as `2n + 6 ≤ s`; the derivative bounds reuse lane 320's
`assembly_character_derivative_bound` and `assembly_phase_norm_le`.  Then

`(t,x) ↦ torusEvalSeriesCLM s i x (v_s t)`

is the composition of the **bounded bilinear** evaluation
`isBoundedBilinearMap_apply` with `(ContDiff in x) ×ˢ (ContDiffOn in t)`, and
`ContDiffOn ℝ ∞ = ∀ n, ContDiffOn ℝ n` lets `s = 2n+6` depend on `n`.

## 4. The pressure

`Ω ∘ (projected convolution) = 0`, because the projected convection is
divergence free: the Leray-projected bilinear map of lane 328 carries **no**
information about the pressure.  The unprojected datum is therefore
unavoidable.  Lane 328 exports `torusConvectionDatumReal` and its norm bound but
keeps bilinearity `private`, so this lane re-proves the four bilinearity lemmas
(the only real input is summability of the convolution at a fixed frequency,
which follows from Cauchy–Schwarz after reindexing `l ↦ k − l`) and packages

```lean
torusConvUnprojCLM r q hr : PeriodicSobolev r →L[ℝ] PeriodicSobolev r →L[ℝ] PeriodicSobolev q
```

with `‖·‖ ≤ torusConvolutionConstant_real r`.  The Leray potential is the
bounded operator `pressurePotentialCLM` with symbol
`−2πik_j/(4π²|k|²)` (norm `≤ 1`, conjugate-symmetric), and
`sum_pressureSymbol_eq` identifies `∑_j σ_j(k)·Ŝ_j(k)` with lane 326's
`lerayPotentialCoeff S k` through `lerayPotentialCoeff_laplace_symbol`.

## 5. Compiler errors actually met, and their fixes

```text
Type mismatch … HasDerivAt … (h ∘ fun r => (r, x)) …            -- `simpa` rewrote the `Space` instance path; use bare `exact`
failed to synthesize SecondCountableTopologyEither ℝ ↥(PeriodicSobolev ↑m)
                                                               -- named local instance short-circuits the search
Tactic `rewrite` failed: Did not find … Paper1.periodicFourierCoeff ?f ?k
                                                               -- `periodicFourierCoeff` is an abbrev; use `exact … _ _`
(deterministic) timeout at `isDefEq` (200000)                   -- `set`-bound local definitions; `clear_value` fixes it
failed to synthesize MulAction ℝ ↥(PeriodicSobolev (↑m + 2))    -- hoist the step into a lemma with plain real indices
invalid 'calc' step, left-hand side is …                        -- `simp only [← mul_assoc]` had reassociated
Unknown constant `ContinuousLinearMap.tsum_apply`               -- use `(ContinuousLinearMap.apply ℝ ℂ A).map_tsum`
`if_neg` has been deprecated                                    -- replaced by a `pressureSymbol_of_ne` slice lemma
```

The one surviving `set_option maxHeartbeats 400000 in` is on
`mildTower_contDiffOn_nat`; it is needed only under `lake build` (the same file
elaborates inside the default budget under `lake env lean`).

## 6. What is *not* claimed

* No quantitative or uniform lifespan.  `exists_classical_of_picard` produces
  the Picard horizon of lane 313/317, which depends on `‖A‖` and the force
  supremum; it is **not** `PeriodicQuantitativeLocalInput'` (the U9e target),
  which asks for one `δ` uniform over an `H¹` ball.
* Nothing is proved about uniqueness of the produced classical solution beyond
  what lanes 315/313 already give on the coefficient side.
