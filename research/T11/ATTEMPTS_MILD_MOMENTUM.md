# ATTEMPTS — 327-T11 U9d2b (Duhamel time differentiation and the momentum equation)

Lane `327-T11-U9d2b-momentum`, module
`formalization/NSFormalization/Section3/T11/MildMomentum.lean` (1 700 lines,
74 named declarations, 2 explicitly named local instances).
No new `def … : Prop` packaging a goal or a field; no `sorry`/`admit`/`axiom`/
`native_decide`; no `set_option maxHeartbeats` needed anywhere.

## 0. Design decisions that made the unit tractable

1. **Differentiate the scalar ODE, not the Banach-valued Duhamel formula.**
   Applying the coefficient functional `torusCoeffCLM` to `hu.equation` turns the
   `PeriodicSobolev 3`-valued Picard identity into the *scalar* identity
   `û(t)(k) = σ(t,k)â(k) + ∫₀ᵗ σ(t−s,k)F̂(s)(k) ds − √W(k) ∫₀ᵗ σ(t−s,k)Q̂(s)(k) ds`
   (`mild_coeff_duhamel`), with `σ(r,k) = exp(−ν|2πk|² r)` an honest real
   exponential in *all* of `ℝ` (`torusHeatSymbol_eq_exp`).  The endpoint-safe
   smoothing differs from `√W σ` only at the single point `s = t`, so
   `intervalIntegral.integral_congr_ae` removes it.  Then
   `∫₀ᵗ σ(t−s)χ(s) ds = σ(t)∫₀ᵗ σ(−s)χ(s) ds` (semigroup law, valid at negative
   elapsed time because `σ` is an exponential), and the FTC at the right
   endpoint plus the product rule give the forced linear ODE
   `heat_duhamel_hasDerivAt`.  This never touches Bochner differentiation.
2. **`PersistenceInput` is reused for the force path.**  The locally uniform
   rapid decay needed for the derivative/sum interchange is required for the
   velocity, the force and the nonlinearity.  For the velocity and the force it
   is exactly `PersistenceInput T u` / `PersistenceInput T F` plus compactness
   (`IsCompact.exists_bound_of_continuousOn`): `persistence_uniform_decay`.  This
   avoids a `(1−Δ)^N`-iteration argument for the force, which was the original
   plan and would have cost ~150 further lines.
3. **The nonlinearity is bounded through the explicit convolution symbol.**
   `torusConvectionSymbol` *is* a convolution of physical coefficients
   (`torusPhysicalCoeff_convectionDatum`), so the decay estimate is pure algebra:
   `W(k) ≤ 2 W(l) W(k−l)` (`periodicFrequencyWeight_shift_le`), hence
   `W(l)^{-n}W(k−l)^{-n} ≤ 2ⁿ W(k)^{-n}`, hence a *gain* of one power in the
   convolution (`convolution_norm_bound`).  No Cauchy-product/`Summable.sigma`
   argument over `ℤ³ × ℤ³` is needed: `W(k−l)^{-2} ≤ 1` absorbs the second
   factor and the remaining `∑_l W(l)^{-2}` is the tree's
   `summable_inverse_periodicFrequencyWeight`.
4. **The periodic convolution theorem is proved by expanding `g`, not `f·g`.**
   `∫ f g ē_k = ∑'_m ĝ(m) ∫ f e_m ē_k = ∑'_m ĝ(m) f̂(k−m)`, with
   `integral_tsum_of_summable_integral_norm` doing the swap — the same skeleton
   as lane 326's `torusScalarSeries_coeff`.  This needs only absolute
   summability of `ĝ`, and it compiled on the first attempt.

## 1. Compiler errors actually hit, and the fixes

| # | Error text (abridged) | Cause / fix |
|---|---|---|
| 1 | `Did not find an occurrence of the pattern … ↑⟨t, ⋯⟩` (and `NNReal.coe_mk` / `simp only` not firing) | `hu.equation t ht` produces `torusForcedPicard … ⟨t, ht.1⟩` whose `ℝ≥0`-coercion `rw` cannot match (proof-irrelevant subterm, `implicit` transparency). Fix: a `rfl` lemma `torusForcedPicard_real` stated with a real `t` and `(ht0 : 0 ≤ t)`, then `rw` with it. |
| 2 | `Did not find … ↑((↑(C.analytic.linearEvolution …) (P s)).ofLp i) k` inside `intervalIntegral.integral_congr` | the congr goal is a beta-redex `(fun x ↦ …) s`. Fix: `show torusCoeffCLM 3 i k (…) = _` before `rw`. Same fix inside `filter_upwards`. |
| 3 | `convert hmul using 1` produced the instance goal `Complex.addCommGroup = instCommCStarAlgebraComplex…` | `convert` on `HasDerivAt` descends into the normed-field instances. Fix: never `convert` a `HasDerivAt`; prove the derivative equality separately and use `HasDerivAt.congr_deriv`. |
| 4 | `invalid ▸ notation … Real.rpow_natCast` | hand-rolled `√W = W^(1/2)`. Fix: `Real.sqrt_eq_rpow`. |
| 5 | `rewrite failed` on a nested `c * (d * z)` pattern | the goal's association differed. Fix: state the algebra as a closed generic lemma `hgen : ∀ c d e x y z w : ℂ, c*d = e → …` proved by `rw [← h]; ring`, then `exact hgen _ _ _ _ _ _ _ hsq`. |
| 6 | `failed to prove positivity/nonnegativity` (four times) | `positivity` cannot see `0 < periodicFrequencyWeight k` (an opaque `def`). Fix: build every such bound from `mildPressure_weight_pos` by hand (`pow_nonneg`, `inv_nonneg.mpr`, `mul_nonneg`). |
| 7 | `Unknown identifier div_le_div_iff` / `mul_inv_eq_div` | renamed/removed in this Mathlib. Fix: `← sub_nonneg` + an explicit `field_simp`-proved quotient identity + `div_nonneg`; and `← div_eq_mul_inv` + `le_div_iff₀`. |
| 8 | `typeclass instance problem is stuck NormedSpace ℝ ?m` on `hasDerivAt_tsum_of_isPreconnected` | the set `t`, the base point `y₀`, `𝕜` and `F` are all implicit and underdetermined. Fix: pass `(g := …) (g' := …) (t := Set.Ioo a b) (y₀ := t)` by name. |
| 9 | `invalid field fderiv … HasFDerivAtFilter.fderiv` | `HasDerivAt.fderiv` does not exist. Fix: `h.hasFDerivAt.fderiv` then `simp`. |
| 10 | `Application type mismatch: hpi : IsPeriodicSpatial … expected UnitPeriods` | the vendor lemmas are stated for `NavierStokes.PeriodicIntegration.UnitPeriods`, the T10 layer for `IsPeriodicSpatial`; identical bodies, different `def`s. Fix: an explicit coercion `have hup : UnitPeriods f := fun y l ↦ hpi y l`. |
| 11 | `Did not find … (⇑(EuclideanSpace.proj i) ∘ mildTimeDerivative C P u t)` | `hint _ (proj.contDiff.comp hf) …` left the function spelled as a composition, so the later `rw [periodicFourierCoeff_sub …]` could not match. Fix: give every integrability fact its own ascribed `have hcdN : ContDiff ℝ ∞ (fun y : Space ↦ …)` first, then `hint _ hcdN hpdN`. |
| 12 | `Integrable ((torusLift f) - torusLift h)` vs `Integrable (torusLift (fun y ↦ f y - h y))` | `Integrable.sub` returns the `Pi.sub` spelling. Fix: an ascribed `have hI34 : Integrable (torusLift (fun y ↦ …)) … := hI3.sub hI4` (defeq, accepted by `exact`). |
| 13 | `rewrite failed … periodicFourierCoeff f k - periodicFourierCoeff h k` | the source-coefficient identity had been stated *after* splitting, but the goal still had the unsplit coefficient. Fix: state `hsrc` on the **unsplit** function and prove it by `congr 1; funext; simp only [mildPressureSource, PiLp.sub_apply, Complex.ofReal_sub]` — no integrability hypothesis at all. |

## 2. Lemmas that turned out to already exist (checked before re-proving)

`grep -rn` over `Section3/`, `Section4/{A01,A02,A04,D01}`, `Paper1/Periodic*`,
`vendor/HeliCorgi/Formal/`:

* `torusHeat_add` / `heatSymbol_add` / `heatSymbol_zero`
  (`Paper1/PeriodicHeatMultiplier.lean`) — the semigroup law used to split
  `σ(t−s)`.
* `ContinuousLinearMap.intervalIntegral_comp_comm` (Mathlib) — the only way the
  coefficient functional gets inside the two Bochner interval integrals;
  `ClassicalAssembly.assembly_integral_solenoidal` uses the same trick.
* `MNS2.EndpointSafeTwoSpaceDuhamelContract.duhamelIntegrand_of_lt`
  (`vendor/HeliCorgi/Formal/EndpointSafeTwoSpaceDuhamel.lean:485`) — avoids
  unfolding `endpointSafePositiveOperator` by hand.
* `hasDerivAt_tsum_of_isPreconnected`, `contDiff_tsum`,
  `intervalIntegral.integral_hasDerivAt_right`,
  `ContinuousOn.stronglyMeasurableAtFilter`,
  `IsCompact.exists_bound_of_continuousOn` (Mathlib).
* `periodicFourierCoeff_fderiv`, `periodicFourierCoeff_laplacian`,
  `spatialPartial_complexify`, `summable_inverse_periodicFrequencyWeight`,
  `periodic_eq_tsum_mFourier` (`T10/FourierCalculus.lean`).
* `torusScalarSeries_{coeff,conj,contDiff,periodic,lift}`,
  `summable_weight_pow_mul_coeff`, `periodic_eq_of_coeff_eq`,
  `integrable_torusLift_of_continuous_periodic`, `spatialDivergence_eq_sum`,
  `pressureGradient_component`, `convectionDivergenceT_spatial_{contDiff,periodic}`,
  `mildPressure_gradient_coeff`, `lerayPotentialCoeff_leray_complement`,
  `mildPressureSourceCoeff_eq_force_sub_convection` (lane 326's
  `T11/MildPressure.lean`) — lane 326 supplied *everything* on the pressure side.
* `exists_periodicDatum_smooth` (`T11/CriterionBridge.lean`, lane 309) — needed
  to instantiate `lerayPotentialCoeff_leray_complement` at a datum of the source.
* `persistence_physical_spatial_smooth`, `persistence_weighted_summable`,
  `torusPhysicalCoeff_{eq,neg,summable}`, `torusPhysicalField_datum`,
  `NSFormalization.Section4.A01.navierStokesResidual_eq_iff_projected`.

**Confirmed absent and therefore proved here:** the periodic convolution theorem
`periodicFourierCoeff (f·g) k = ∑' l, ĝ(l) f̂(k−l)` (lane 326's
`ATTEMPTS_MILD_PRESSURE.md` §2 already recorded it as absent); the weight
submultiplicativity `W(k) ≤ 2W(l)W(k−l)`; the frequency-local Leray symbol
`lerayAt` on bare coefficient vectors; the component identities
`convectionDivergenceT_component` and `spatialLaplacian_component`.

## 3. What is NOT proved — exact residual statements

### 3.1 Joint `C^∞` of the velocity (`ClassicalSolutionT.velocity_smooth`)

```lean
ContDiffOn ℝ ∞ (torusPhysicalVelocity u) (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
```

**What is delivered instead:** the *first* time derivative exists everywhere on
`Ioo 0 T ×ˢ univ` and is identified as the Fourier series of the Duhamel
derivative (`torusPhysicalVelocity_hasDerivAt`,
`temporalDerivative_torusPhysicalVelocity'`), the spatial slices are `C^∞`
(lane 320) and the field is jointly continuous on `Icc 0 T ×ˢ univ` (lane 318).

**Obstacle (hypothesis-level, not effort-level).**  The brief's induction "the
derivative of a coefficient path is again a path of the same type" needs the
derivative path `t ↦ (d/dt û(t)(k))_k` to satisfy the *same* Duhamel identity one
Sobolev order lower, i.e. the mild equation at order `5, 7, …`.  What is in the
tree is `TorusForcedMildOn C A P T u`, an `H³ × H²` contract statement
(`LocalExistenceProbe.lean:246`), holding at the single order three;
`PersistenceInput` supplies *continuous* higher-order realizations but no
equation for them.  Concretely, the second time derivative would need
`d/dt (P(F − Q))^(t)(k)`, hence `d/dt Q̂(t)(k)`, hence differentiability of
`t ↦ u(t)` **in `PeriodicSobolev 3`** (not only coefficientwise), which is false
for the `H³`-valued path unless `u(t) ∈ H⁵`.  Closing this needs either a
higher-order forced mild statement (a new contract at order `m` for every `m`, a
genuine extension of lane 313's construction) or a parabolic smoothing estimate
`‖e^{νtΔ}‖_{H³→H^{3+2j}} ≲ t^{-j}` with the corresponding time-weighted norms —
neither is in the tree.

### 3.2 Joint `C^∞` of the pressure (lane 326's residual)

```lean
ContDiffOn ℝ ∞ (mildPressure g u) (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
```

Same obstacle, one step downstream: `p̂(t)(k)` is a fixed algebraic function of
`Ŝ(t)(k) = F̂(t)(k) − Q̂(t)(k)`, so `p` is as smooth in time as `Q̂`, i.e. as
`u`.  With §3.1 open this stays open.  *Partial gain of this lane:* the
ingredients lane 326 listed as missing for the weaker joint-continuity statement
(`ATTEMPTS_MILD_PRESSURE.md` §3.2, items 1–3) are now all present — the
convolution theorem (`periodicFourierCoeff_mul`), the locally uniform weighted
bound (`persistence_uniform_decay`, `persistence_nonlinear_decay`) and the
identification of the convection coefficients (`convectionDivergenceT_coeff`).
Assembling them into `ContinuousOn (mildPressure g u) (Ico 0 T ×ˢ univ)` was not
attempted here (it is not a field this lane was asked for).

### 3.3 Hypotheses of `momentum_of_pressure` that are *not* discharged here

`momentum_of_pressure` is stated conditionally on facts about the **data**, all
of which are proved elsewhere or are properties of the force, never of the
conclusion:

* `hPc : ContinuousOn P (Icc 0 T)` — continuity of the projected force path;
* `hF : PersistenceInput T F` — the force datum path has continuous realizations
  at every Sobolev order (the same predicate as for `u`, applied to `F`);
* `hFg : IsPeriodicSobolevPath 3 g F`, `hg`, `hgp` — `F` is the order-three datum
  path of the smooth periodic physical force `g`;
* `hdivfree` — proved by lane 320 (`persistence_mild_physical_divergence`).

None of these is a restatement of the momentum equation, and all are satisfied by
the affine-constant family (`mildMomentum_nonzero_instance` exhibits the mild
solution, the persistence input and the derivative formula on it).

## 4. Positive record — what the construction buys downstream

* `periodicFourierCoeff_mul` is stated for arbitrary continuous periodic `f` and
  `g` with summable data, so every future product/convolution computation on the
  torus (energy identities, higher nonlinearities, commutator estimates) can use
  it directly.
* `convolution_norm_bound` gives a *gain of one weight power* per convolution and
  is stated for arbitrary coefficient families, not for the velocity.
* `lerayAt` makes the Leray symbol usable on bare `Fin 3 → ℂ` vectors, so
  projection commutes with the weight changes by `lerayAt_const_mul`; this is
  what makes `P̂F̂ − P̂Q̂ = P̂(F̂ − Q̂)` a one-line `lerayAt_sub`.
* `heat_duhamel_hasDerivAt` is the general forced scalar ODE and is independent of
  the torus: any Duhamel coefficient in this tree can be differentiated with it.
