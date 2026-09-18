# ATTEMPTS — lane 330 (T11 / U9d1c): the endpoint Duhamel half-step

Positive and negative record for `theorem torusHalfStepInput : TorusHalfStepInput`.
Module: `formalization/NSFormalization/Section3/T11/DuhamelHalfStep.lean`.

## 0. What the statement actually demands (and why it is not a re-indexing)

`PeriodicSobolev s` is a phantom-indexed `abbrev` of the *one* carrier
`realPeriodicSubmodule ⊆ ℓ²`, so `IsPeriodicReweight r (r+1/2) (v t) (w t)`
is the honest assertion

  `(w t).1 i k = W(k)^{1/4} · (v t).1 i k`  with  `w t ∈ ℓ²`,

i.e. the sequence `k ↦ W(k)^{1/4}(v t)_i(k)` must be square-summable. That is a
genuine half-order gain; no choice of `w` can dodge it. Composing with the
hypothesis `IsPeriodicReweight 3 r (u t) (v t)`, the target is exactly
`IsPeriodicReweight 3 (r+1/2) (u t) (w t)`, i.e. `u(t) ∈ H^{r+1/2}`.

## 1. Route that failed first (recorded, because it is the brief's route)

The brief proposes
`w(t) := e^{νtΔ}A' + ∫₀ᵗ S_frac(ν(t−τ))(P(τ) − Q_r(v τ, v τ)) dτ`
with **both** source terms passed through lane 329's gain-`3/2` smoothing at
order `r−1`.

Obstacle: `S_frac` at order `r−1` needs `P(τ)` as an element of `H^{r−1}`, but
the hypotheses only supply the **order-three** Leray force path
(`hF : IsPeriodicSobolevPath 3 g F`, `hP : IsPeriodicLerayDatum (F t) (P t)`).
Trying to reach order `r−1` from order three by the smoothing itself fails for
a quantitative reason: the gain `σ` is paid with the kernel `(t−τ)^{-σ/2}`,
which is integrable only for `σ < 2`. So the force integral is at most
`H^{3+2−ε}`, while `r` is arbitrary in `[3,∞)`. Measured, not guessed: the
half-step is quantified over every real `r ≥ 3` with a *fixed* order-three
force path, so **no amount of smoothing can substitute for force regularity**.

Second dead end inside the same route: taking `P(τ)` at order `r−1` by
`exists_periodicDatum_smooth` pointwise in `τ` gives a `Classical.choice`
family with no measurability, so the Bochner integral does not even typecheck
as an integral of a strongly measurable function.

## 2. Route that works

Use the force at the **top** order and the plain (bounded, non-singular) heat
semigroup for it; use the singular fractional kernel only for the nonlinearity,
where the input `v` is continuous by hypothesis:

  `w(t) = e^{νtΔ}A′ + ∫₀ᵗ e^{ν(t−τ)Δ} P_{r+1/2}(τ) dτ − ∫₀ᵗ S_frac(ν(t−τ)) Q_r(v τ, v τ) dτ`.

Both integrals exist, and the exponent bookkeeping matches exactly:
`W^{3/4}·W^{(r−3)/2} = W^{((r+1/2)−3)/2}·W^{1/2}` (`torusHalfStep_weight_identity`),
the left side being lane 329's gain `3/2` on lane 328's order-`(r−1)` output and
the right side the order-`(r+1/2)` transport of the contract's own gain-`1`
smoothing of the order-two bilinear.

### 2.1 The force at every real order (the only genuinely new analysis)

`exists_continuous_lerayForcePath σ hg hp hF hP` produces
`Pσ : ℝ → PeriodicSobolev σ` with `Continuous Pσ` and
`IsPeriodicReweight 3 σ (P t) (Pσ t)` for `t ≥ 0`. Three ingredients:

1. `Section3/T10/ForcePaths.lean`'s `continuous_datum_path (m : ℕ)`: the
   order-`m` datum path of a jointly smooth periodic field is continuous —
   **integer orders only**.
2. The ceiling trick: take `m := ⌈σ⌉₊` and descend with lane 319's bounded
   `persistenceDown (m:ℝ) σ (Nat.le_ceil σ)`; `persistence_datum_of_reweight`
   turns the descent into the order-`σ` datum predicate. This is how a real
   order is reached without redoing the Fourier analysis at real order.
3. The Leray projector must be applied *after* the descent, so it has to be a
   bounded operator at every real order. `Section3/T10/Leray.lean` only offered
   the existential `leray_exists_contraction`; §1 of the module upgrades it to
   `torusLerayCLM (s : ℝ) : PeriodicSobolev s →L[ℝ] PeriodicSobolev s`
   (additivity and homogeneity from the frequencywise `ℂ`-linear formula,
   norm `≤ 1`), together with `torusLeray_reweight` (Leray commutes with order
   transport) and `torusLerayCLM_eq_of_isDatum` (uniqueness, which is what
   identifies the hypothesis' `P t` with `torusLerayCLM 3 (F t)`).

### 2.2 Integrability and continuity for free, via a genuine contract

Rather than redo the endpoint-safe estimates, §3 builds

  `torusFracContract r hr hν :
     MNS2.EndpointSafeTwoSpaceDuhamelContract ℝ (PeriodicSobolev (r+1/2)) (PeriodicSobolev (r-1))`

with `linearEvolution = torusHeatCLM`, `positiveSmoothing = torusHeatSmoothingCLM_frac (r-1)`,
`bilinear = torusConvolutionCLM_real r hr` and
`smoothingKernel τ = torusFracConst ν τ · torusFracKernel ν τ`.
Then `intervalIntegrable_duhamelIntegrand_of_continuousOn` and
`continuousOn_duhamelIntegral` are inherited from HeliCorgi.

Note on the majorant: the contract's `norm_positiveSmoothing_apply_le` and
`intervalIntegrable_smoothingKernel` are quantified over *all* `τ > 0` and all
windows, so the window constant cannot be frozen at a fixed `T`. Fix: evaluate
lane 329's constant at the elapsed time itself (`htT := le_rfl`), giving
`torusFracMajorant ν τ = (ντ + (3/4)e^{-1})^{3/4}(ντ)^{-3/4}`, and prove
`torusFracConst_mono` so that on `(0,T]` it is dominated by the frozen
`torusFracConst ν T · torusFracKernel ν τ`, which is integrable by lane 329.

## 3. Errors met, and their fixes (verbatim)

* `Unknown constant 'PiLp.projCLM'` — the coefficient functional had to be built
  by hand (`torusEvalCLM`, `LinearMap.mkContinuous` with bound `1`) from
  `lp.norm_apply_le_norm` and `PiLp.norm_sq_eq_of_L2` + `Finset.single_le_sum`.
* `(deterministic) timeout at 'abstract nested proofs'` and
  `Tactic 'simp' failed ... timeout at 'whnf'` inside the first
  `LinearMap.mkContinuous` for the Leray map. Cause: `simpa` on a goal mentioning
  `‖·‖` at a phantom index. Fix: prove `torusLerayDatum_add` / `_smul` as
  standalone lemmas first and replace `simpa` by `rw [one_mul]; exact …`. After
  this the definition elaborates in seconds; no `set_option maxHeartbeats` is
  used anywhere in the module.
* `failed to synthesize HPow ℂ ℝ ?m` after `push_cast`: `push_cast` pushes the
  `ℝ → ℂ` coercion *into* `Real.rpow`, which has no complex counterpart here.
  Fix: never `push_cast` through a weight; use `simp only [Complex.ofReal_mul]`
  and finish with `linear_combination … * hkey`.
* `Tactic 'rewrite' failed: Did not find an occurrence of ↑⟨t, ⋯⟩`. Cause: the
  mild equation of `TorusForcedMildOn` instantiates the evolution time as the
  subtype `⟨t, htIcc.1⟩` while `torusHalfStepField` uses `Real.toNNReal t`; the
  two are only propositionally equal. Fix: `Real.toNNReal_of_nonneg htIcc.1`
  rewrites one into the other *before* the symbol lemmas are applied, and the
  witness must be spelled `htIcc.1` (not `ht.1`) so that it is syntactically the
  one the structure field produced.
* `rw [C.linear_symbol]` rewrites only the first instantiation; both occurrences
  need explicitly applied forms (`C.linear_symbol (Real.toNNReal t) A' i k`).

## 4. Residuals

**None for this lane's theorem**: `torusHalfStepInput` and the two consumers
(`persistence_halfOrder_ladder_unconditional`, `persistence_unconditional`) are
unconditional, with no named input, no alias and no `def … : Prop` restating a
goal. All 45 declarations print exactly `[propext, Classical.choice, Quot.sound]`.

Out of scope, deliberately:
* no time regularity, no pressure, no momentum equation — those are U9d/U9d2;
* `torusForcedMildOn_persistence` still produces *coefficient* data, not a
  physical field; Fourier inversion is lane 318's open problem;
* the constant `torusFracConst ν τ` is not claimed sharp;
* `continuous_datum_path` needs `g` smooth on **all** of space-time; a
  `ContDiffOn`-on-a-slab version does not exist in the tree, so neither does a
  slab version of `exists_continuous_lerayForcePath`.
