# ATTEMPTS — lane 322, T11 unit U12 (`higherOrderBound`, periodic `eq:Rhigh` + Grönwall)

Non-generated file. Paths tried, exact error text, and the exact residual.

## 0. Target and route

Target: the `higherOrderBound` field of `PeriodicContinuationAPI`
(`research/T11/probes/api_on_canonical.lean:112-121`), copied verbatim into
`research/T11/probes/high_order_closes.lean`.

Route decided after reading the Section 4 mirror
(`research/A04/G1_SPLIT.md` SL0–SL8, `Section4/A04/{EnergyIdentityHigh,
HighContinuation,HighContinuationIntegral,Regularized,Gronwall}.lean`,
`Section4/A01/{Propagation,GronwallInstance}.lean`,
`Section4/A04/RestartFixedForce.lean:236` `higherOrderBound_of_gronwall`):

```
eq:Rhigh  --Young-->  ½(‖u‖²_{H^m})' ≤ C_{m,ν}‖u‖²_{H²}‖u‖²_{H^m} + ‖f‖_{H^m}‖u‖_{H^m}
          --ζ↓0-->    ‖u(t)‖_{H^m} ≤ ‖u(0)‖_{H^m} + ∫₀ᵗ (C_{m,ν}‖u‖²_{H²}‖u‖_{H^m} + ‖f‖_{H^m})
          --Grönwall--> ‖u(t)‖_{H^m} ≤ (‖u(0)‖_{H^m} + B) exp(C_{m,ν} K)
```

Everything from `eq:Rhigh` rightwards is proved here, unconditionally; `eq:Rhigh`
itself is the residual (§3).

## 1. Reuse audit (what did NOT have to be redone)

* `Section4.A04.sqrt_le_primitive_linear` (`Regularized.lean:134`) — the `ζ↓0`
  integral form.  Imports are Mathlib-only, no PDE objects, so it is reusable on
  the torus verbatim.  Used at `E := ‖u(·)‖²_{H^m}`, `K := C_{m,ν}‖u(·)‖²_{H²}`,
  `b := ‖f(·)‖_{H^m}`.
* `Section4.A01.gronwall_bddAbove_Ico` (`Propagation.lean:73`, which pulls in
  `Section4.A04.Gronwall`, also Mathlib-only) — the variable-coefficient Grönwall
  bound with two uniform caps.  Used verbatim.
* `Section3.T11.CriterionBridge.periodicSobolevENorm_eq_datum` — evaluating the
  infimum at a representing datum; the whole real-profile layer rests on it.
* `Section3.T10.ForcePaths.force_coefficient_path` (lane 312) — continuous,
  compactly supported datum path of a test force at every integer order.
* `Section3.T11.Persistence.{persistence_down_weight_le, persistence_datum_of_reweight}`
  and `LocalExistenceProbe.{torusMultiplier, torusMultiplier_norm_le}` — the
  order-descent multiplier and its norm bound.

**Deliberately NOT imported:** `Section4.A04.HighContinuation` (for
`young_high_real`) and `Section4.A04.EnergyIdentityHigh`.  Those drag the whole
whole-space energy chain (`LaplacianAssembly`, `NonlinearBound`, `MomentumDatum`,
`TimeDerivative`, the `Paper3` angular carrier) into Section 3 for six lines of
arithmetic.  `torusYoungAbsorb` reproves exactly `young_high_real`'s statement
with the same perfect-square proof; the docstring says so.

## 2. Paths tried, and what failed

### 2.1 `‖persistenceDown s r h A‖ ≤ ‖A‖` through the bundled CLM — abandoned

```
example (s r : ℝ) (h : r ≤ s) (A : PeriodicSobolev s) :
    ‖persistenceDown s r h A‖ ≤ ‖A‖ := by
  have := torusMultiplier_norm_le s r (fun k ↦ periodicFrequencyWeight k ^ ((r-s)/2)) 1 …
  simpa [persistenceDown, torusMultiplierCLM] using this
```
```
error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000)
has been reached
```
`persistenceDown` unfolds through `torusMultiplierCLM` to `LinearMap.mkContinuous`
of an anonymous structure; `simp` unfolding that and then reducing the `lp`
coercions blows the `whnf` budget.  Fix: do not go through the CLM.
`torusOrderDown` is the bare `torusMultiplier` application, so
`torusMultiplier_norm_le` applies with one `rwa [one_mul]`, and
`IsPeriodicReweight s r A (torusOrderDown s r h A)` is `rfl` (same proof as
`persistenceDown_reweight`).  Cost: one extra `def`; benefit: the lemma elaborates
in milliseconds.

### 2.2 Cauchy–Schwarz on the datum carrier — two wrong names, one `simp` timeout

* `abs_re_inner_le_norm` — `error: Unknown identifier`.  The Mathlib name is
  `re_inner_le_norm` (`InnerProductSpace/Basic.lean:461`), which already gives
  `re ⟪x,y⟫ ≤ ‖x‖‖y‖` without the absolute value.
* `RCLike.inner_apply a b : inner 𝕜 a b = b * conj a` — wrong orientation, gives
  ```
  error: Type mismatch … has type inner ?𝕜 ?a ?b = ?b * (starRingEnd ?𝕜) ?a
  but is expected to have type … = (starRingEnd ℂ) … * …
  ```
  `RCLike.inner_apply'` is the `conj a * b` orientation.
* `simpa [torusRealPairing] using re_inner_le_norm (𝕜 := ℂ) A.1 B.1` →
  ```
  error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000)
  ```
  `simp` tries to normalize the `PiLp`/`lp` inner product.  Fix: three explicit
  `rfl` bridges (`RCLike.re z = z.re`, `‖A‖ = ‖A.1‖` twice) and one `rw`.
* `tsum_sum` — `error: Unknown identifier`.  At this Mathlib pin the name is
  `Summable.tsum_finsetSum`.
* `lp.summable_inner (A.1 i) (P.1 i)` alone →
  ```
  error: typeclass instance problem is stuck, it is often due to metavariables
    PeriodicFrequency → InnerProductSpace ?m ℂ
  ```
  The scalar field is not determined by the arguments; `(𝕜 := ℂ)` fixes it.

### 2.3 Single-mode witness for the pressure drop

The first three attempts at `torusShearDatum` failed on `change` without a type
ascription:
```
error: Function expected at lp.single 2 e0 ?m + lp.single 2 (-e0) ?m
but this term has type ?m
```
`torusConstantDatum` (`LocalExistenceProbe.lean:277`) shows the working idiom:
ascribe the sum to `PeriodicScalarData` inside the `change`.  Afterwards
`simp [lp.single_apply]` leaves `Pi.single` behind, so the pointwise-value lemma
needs `Pi.single_apply` as well — but *only* in the `torusShearDatum_apply` /
`torusShearPressureDatum_apply` lemmas, not in the membership proofs (the linter
flags it as unused there).

### 2.4 `rw [← hwv]` in the final calc — wrong rewrite target

```
error: Type mismatch … (squaredHTwoIntegralT S u).toReal
   vs  (squaredHTwoIntegralT S w.velocity).toReal
```
`rw [← hwv]` (with `hwv : w.velocity = u`) rewrites *every* `u`, including the one
inside the finiteness constant, which must stay `u`.  Fix: `rw [hwv] at hchain`
(forward, in the hypothesis) instead.

## 3. The exact residual

`higherOrderBound_of_energyInequality` has exactly one hypothesis besides the
constant family `Chigh : ℕ → ℝ`.  Written out:

```lean
hRhigh : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField), a ∈ initialClassT →
  ∀ (f : SpaceTimeField), f ∈ forceClassT →
    ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T) (m : ℕ), 3 ≤ m →
      ∀ t ∈ Ioo (0 : ℝ) T, ∃ d g : ℝ, 0 ≤ g ∧
        HasDerivAt (fun r ↦ torusSobolevNormAt (m : ℝ) w.velocity r ^ 2) d t ∧
        (1 / 2) * d + ν * g ^ 2 ≤
          Chigh m * torusSobolevNormAt 2 w.velocity t *
              torusSobolevNormAt (m : ℝ) w.velocity t * g +
            torusSobolevNormAt (m : ℝ) f t * torusSobolevNormAt (m : ℝ) w.velocity t
```

This is `appendix-a-local-theory.tex:131-138` eq:Rhigh, with `g := ‖∇u(t)‖_{H^m}`
existentially quantified (the torus vocabulary fixes no spelling for that norm;
`periodicHomogeneousENorm` is defined only for mean-zero fields, and a velocity
slice with nonzero Galilean mean is not mean zero).  Existential `g` makes the
hypothesis strictly weaker, hence easier to discharge.

**No `def … : Prop` named input is introduced**, deliberately: `hRhigh` is not
reducible to a single missing fact, so naming one would misrepresent the gap.
Two independent facts are missing on the torus.

### 3.1 Missing fact A — time differentiability of the coefficient path

`ClassicalSolutionT.sobolev` (`Section3/T10/PeriodicData.lean:293-297`) gives only
```
∀ m : ℕ, ∃ G, ContinuousOn G (Ico 0 T) ∧ ∀ t ∈ Ico 0 T, IsPeriodicDatum m (u t ·) (G t)
```
The energy identity needs `HasDerivAt (fun r ↦ ‖G r‖²) (2⟪G t, G' t⟫) t`, i.e. the
`ContDiffOn ℝ ∞ G` of `PeriodicLocalRegularity.sobolev_smooth` — which
`SolvesBelowT` does **not** carry.  Section 4 closed the same gap with
`A04.classical_hasSmoothSobolevPath` (`RestartFixedForce.lean:146`), which
transports the local-existence carrier's regularity along uniqueness and
overlapping windows.  The torus analogue needs lane 321's `regularity` field,
which is itself conditional on the still-open `PeriodicQuantitativeLocalInput'`
(`Section3/T11/LocalExistence.lean`).  Deriving it directly from
`velocity_smooth` would mean proving `ℓ²`-norm differentiability of
`t ↦ (W(k)^{m/2} û(t,k))_k` from pointwise-in-`k` smoothness — a dominated
convergence argument in the coefficient sum that is its own sub-lane
(Section 4 spent lanes 053 / `A01.DatumPathDeriv` / `A01.DatumPathSmooth` on it).

Also missing on this branch: the momentum equation in **datum** form
(`deriv G t = ν • L − N − P + F` in `PeriodicSobolev m`), Section 4's SL1/SL2
(`A04/TimeDerivative.lean`, `A04/MomentumDatum.lean`).

### 3.2 Missing fact B — the torus tame product at the pairing level

eq:Rhigh's nonlinear term needs
`|⟪(u·∇)u, u⟫_{H^m}| ≤ C_m ‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}`.
T12's `tameProduct` (`research/T12/probes/api_on_canonical.lean:124-130`) is a
**scalar physical-field** product bound in `periodicScalarSobolevENorm`; it is an
ingredient of that estimate, not the estimate.  Section 4 needed the whole of
`research/A04/SL5_SPLIT.md` (`A04/NonlinearBound.lean`, `NonlinearColumns.lean`,
`NonlinearDatum.lean`, `NonlinearPairing.lean`, `AdvectionDivergence.lean` plus
`A03.outerProductTame`) for the whole-space version.  `Section3/T11/ConvolutionBoundReal.lean`
(lane 328) already has the real-order projected convection CLM
`H^r × H^r → H^{r-1}`, which is the natural starting point; converting it into the
*pairing* bound with the `‖∇u‖_{H^m}` factor is the open step.

Because A and B are independent, the honest shape is one explicit hypothesis
binder carrying eq:Rhigh, not a named `Input` predicate — see `logs/LESSONS.md`
2026-09-18 on alias stubs.

## 4. What the torus *does* settle that R³ needed a lane for

* **Pressure drop** (Section 4's SL4, lane 121, `A04/PressureDrop.lean`, routed
  through Leray self-adjointness).  On the lattice it is three lines of symbol
  algebra: conjugating `∑ⱼ 2πi kⱼ ûⱼ(k) = 0` gives `∑ⱼ 2πi kⱼ conj(ûⱼ(k)) = 0`,
  and the gradient datum is `2πi kᵢ q̂(k)`, so every frequency of the pairing
  vanishes (`torusPressureSymbol_drop`, `torusPressureDrop`).  Exhibited at a
  nonzero velocity datum *and* a nonzero pressure-gradient datum
  (the shear mode `2 e₁ cos 2πx₀`, in the probe — see §6).
* **Order descent** is constant-free on the torus (`periodicSobolevENorm_mono_order`,
  constant `1`), because `1 + 4π²|k|² ≥ 1`; the whole-space version carries the
  operator `D01.lowerVectorL` and its norm.
* **The dissipation sign** (`torusLaplacianSymbol_pairing`) is the exact value
  `−|2πk|² ∑ᵢ |ûᵢ(k)|²` at each frequency, no integration by parts.

## 5. Commands

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.HighOrder
cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/HighOrder.lean
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/high_order_closes.lean
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_high_order.lean
make check
```
All clean, no warnings; 24 `#guard_msgs`-checked axiom prints, each exactly
`[propext, Classical.choice, Quot.sound]`.

## 6. Audit hygiene (post-review-request fix)

`shearFreq` / `shearFreq_ne_neg` print `[propext]` and `shearFreq_component_one`
prints `[propext, Quot.sound]` — strict subsets of the three standard axioms, but
the codex reviewer enforces "every **module** declaration prints exactly the
three" (lane 326 was rejected for this). The whole shear-mode witness block
(12 declarations) therefore moved verbatim from `HighOrder.lean` into
`research/T11/probes/high_order_closes.lean`, where it is local defs plus a
closing `example`. Nothing in the module referred to the witness, so no theorem
needed generalizing to a parametric mode.
