# ATTEMPTS — 326-T11 U9d2a (the pressure of the mild solution)

Lane `326-T11-U9d2a-pressure`, module
`formalization/NSFormalization/Section3/T11/MildPressure.lean`.
Single allowed named input: `PersistenceInput T u` (lane 320's
`ClassicalAssembly.lean`). **No new `def … : Prop` is introduced.**

## 0'. Revision after the codex REJECT (2026-09-18)

All three review findings were closed by *proving* the missing content.

* **Finding 1 (canonical `F − Q`).** The periodic convolution theorem
  `periodicFourierCoeff_mul` is now proved (see §5 below), and from it
  `periodicFourierCoeff_convection_eq_torusConvectionDatum`,
  `torusConvectionDatum_isPeriodicDatum`, `mildPressureSourceCoeff_eq_canonical`
  (the reviewer's exact statement), `mildPressure_gradient_canonical` and
  `mildPressure_gradient_leray_canonical`. The `(I − P)(F − Q)` wording in the
  report is therefore now literal, not an overclaim. Note this *reverses* the
  "not in the tree" conclusion of §0/§3.2 below only in the sense that the
  theorem did not exist and has now been supplied by this lane.
* **Finding 2 (every `H^m`).** `scalar_datum_of_smooth`, `mildPressure_coeff`,
  `mildPressure_scalar_datum` and `mildPressure_memPeriodicHm` export the
  order-`m` weighted coefficient family as the canonical
  `T12.IsPeriodicScalarDatum`, hence `T12.MemPeriodicHmScalar m` of every
  pressure slice; they are bundled into `MildPressureFields`.
* **Finding 3 (axiom audit).** First pass: dropped the two `[propext]`-only
  declarations from the audit. The second review rejected that reading of the
  rule — the gate is *every declaration of the module* — so `testFrequency` and
  `testFrequency_ne_neg` were **moved out of the module** into
  `probes/mild_pressure_closes.lean`, and the non-vacuity theorems
  (`lerayPotentialCoeff_testPressureSource_ne_zero`,
  `lerayPotential_testPressureSource_ne_zero`, `mildPressure_nonzero_instance`)
  were generalized to an arbitrary lattice mode `m` with the hypotheses
  `m ≠ 0`, `¬ m = -m`, `m 0 ≠ 0`. The audit file now covers all 95 module
  declarations and every line prints exactly the standard three axioms.

## 0. Design decision that made the unit tractable

The brief describes the coefficient pressure as the Leray complement of
`F(t) − Q(u(t),u(t))` on the coefficient side. A first pass tried to define
`p̂(t)(k)` from `torusConvectionDatum (u t) (u t) : PeriodicSobolev 2` directly.
That route needs, for the **spatial smoothness** of the inverted pressure, an
all-order weighted summability estimate for the *convolution*

```
∑_k W(k)^N ‖∑_j 2πi k_j ∑'_l û_j(l) û_i(k−l)‖ < ∞,
```

i.e. a discrete Young/weight-shift argument on top of `ConvolutionBound.lean`'s
`weight_cube_shift` (which is only stated at the single exponent 3). It is
provable — `W(k)^N ≤ 4^N (W(l)^N + W(k−l)^N)` plus two Cauchy products — but it
is a multi-hundred-line detour.

(The convolution route above was later supplied anyway, for the *identification*
of the physical convection coefficient with `torusConvectionDatum`; what is
still avoided is the all-order weighted convolution *estimate*, which the
smoothness proof would have needed and which the physical route makes
unnecessary.)

The delivered construction takes the **physical** source

```
mildPressureSource g u := fun z ↦ g z − convectionDivergenceT (torusPhysicalVelocity u) z.1 z.2
```

whose slice is `C^∞` (force smooth + `persistence_physical_spatial_smooth`)
and unit-periodic. Its Fourier coefficients then decay rapidly by
`periodicFourierCoeff_rapid_decay` alone, **no convolution estimate needed**.
The link back to the coefficient side is kept as a theorem:
`mildPressureSourceCoeff_eq_force_sub_convection` proves the source coefficient
is exactly `torusPhysicalCoeff 3 (F t) j k` minus the convection coefficient,
and `lerayPotentialCoeff_leray_complement` proves the defining Leray identity
against the T10 symbol `periodicLeray` for *any* datum of the source.

## 1. Compiler errors actually hit, and the fixes

| # | Error text (abridged) | Cause / fix |
|---|---|---|
| 1 | `unsolved goals ⊢ W^N*‖c‖*W^2 = ‖c‖*W^(N+2)` after `field_simp [pow_add]` | `field_simp` does not see `pow_add` in its simp set the way `rw` does. Fix: `rw [pow_add]; field_simp [hw.ne']`. A trailing `ring` then errors with `No goals to be solved`. |
| 2 | `Unknown constant 'Complex.conj_intCast'` | use `map_intCast` (the `starRingEnd ℂ` is a ring hom). |
| 3 | `rewrite failed … ∑ i ∈ ?s, ?f i * ?a` | `← Finset.sum_mul` was the wrong lemma for `∑ j, C * a j`; `← Finset.mul_sum` is. |
| 4 | `rewrite failed: ?m * (↑(k i) / ?m)` after `simp only [periodicLeray, …, mul_comm]` | `mul_comm` inside `simp only` reassociates unpredictably. Fix: prove the complement as a standalone `have hL : W^(−s/2) * periodicLeray s B i k = Ŝ_i − (k_i/|k|²)(k·Ŝ)` by `congr 1` on the two halves, then `ring`. |
| 5 | `unsolved goals ⊢ ¬?m.153 j = ω` | `ContDiff.of_le (by simp)` / `ContDiff.fderiv_right (by simp)` leave the *level* as a metavariable when the result type is not pinned. Fix: always introduce `have h1 : ContDiff ℝ 1 f := …` / `have hds : ContDiff ℝ ∞ (spatialPartial …) := …` first. |
| 6 | `rewrite failed … fderiv ℝ (f₁ − f₂) x` | `HasFDerivAt.sub`'s `.fderiv` prints the function as `f₁ − f₂`; the goal has `fun y ↦ f₁ y − f₂ y`. Fix: pin the function by `have h : HasFDerivAt (fun y ↦ f₁ y − f₂ y) … := h1.hasFDerivAt.sub h2.hasFDerivAt`. |
| 7 | `(deterministic) timeout at whnf, maximum number of heartbeats (200000)` on `mildPressure_spatial_contDiff` and `mildPressure_gauge` | unifying `ContDiff ℝ ∞ (fun x ↦ mildPressure g u (t,x))` with `ContDiff ℝ ∞ (lerayPotential S)` sends the elaborator into `lerayPotential`'s `tsum`. Fix: the `rfl`-lemma `mildPressure_slice` plus `rw`/`show`, never bare `exact`. |
| 8 | `Continuous (Paper1.torusLift ?m.24)` type mismatch | `Paper1.continuous_torusLift` is stated **only for `Space → ℂ`**. Fix: prove continuity of the complexified lift and postcompose `Complex.continuous_re` (`torusLift p q = (torusLift (↑p) q).re` is `rfl`). |
| 9 | `rewrite failed … (fun x => v (t, x)) (y + coordinateVector q)` | periodicity hypotheses do not `rw` under beta. Fix: `congrArg (fun w : Space ↦ (w j) • w) (hv y q)`, and always ascribe the type of the `have`. |
| 10 | `rewrite failed … ↑0` in `↑(0 x) = 0` | `congrFun h x` has RHS `(0 : Space → ℝ) x`. Fix: ascribe `have hx : … = 0 := congrFun h x`. |

## 2. Lemmas that turned out to already exist (checked before re-proving)

`grep -rn` over `Section3/`, `Paper1/Periodic*`, `Section4/{A01,A02,A04,D01}`,
`vendor/HeliCorgi/Formal/`:

* `periodicFourierCoeff_real_neg` (`T10/Parseval.lean:50`) — conjugate reflection
  for real fields; this is what makes the inverted series real.
* `periodicFourierCoeff_scalarSpatialLaplacianT`, `scalarSpatialLaplacianT_eq`,
  `spatialPartial_complexify`, `periodicFourierCoeff_fderiv`,
  `periodicFourierCoeff_rapid_decay`, `summable_inverse_periodicFrequencyWeight`,
  `periodic_eq_tsum_mFourier`, `summable_periodicFourierCoeff_of_smooth`
  (`T10/FourierCalculus.lean`).
* `memLp_torusLift_vector` (`T10/ForcePaths.lean:18`) — gives the
  `pressure_gradient` `MemLp` field from continuity alone.
* `NavierStokes.PeriodicUniqueness.periodic_fderiv` / `spatial_partial_periodic`
  / `spatial_partial_contDiff` (vendor) — periodicity and smoothness of
  derivatives; `periodic_fderiv` needs **no** differentiability hypothesis.
* `assembly_character_derivative_bound`, `assembly_phase_norm_le`
  (`T11/ClassicalAssembly.lean`) — reused verbatim for the scalar series, so the
  `contDiff_tsum` bound did not have to be redone.
* `integral_mFourier`, `periodicFourierCoeff_const`, `periodicFourierCoeff_sub`,
  `IsPeriodicDatum.integrable_component` (`T10/DatumBasics.lean`).

Nothing about a **periodic convolution theorem**
(`periodicFourierCoeff (f·g) k = ∑' l, f̂(l) ĝ(k−l)`) existed in the tree (the
reviewer independently confirmed this by `grep`). **This lane now supplies it**
as `periodicFourierCoeff_mul`; see §5.

## 3. What is NOT proved — exact residual statements

### 3.1 The `ClassicalSolutionT.pressure_smooth` field (joint slab regularity)

```lean
pressure_smooth :
  ContDiffOn ℝ ∞ (mildPressure g u) (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
```

**Obstacle (hypothesis-level, not effort-level).** `PersistenceInput T u` gives
only `ContinuousOn u_m (Ico 0 T)` at each order; nothing in the allowed input
constrains any time derivative of `t ↦ u t`, hence none of
`t ↦ p̂(t)(k) = lerayPotentialCoeff (mildPressureSource g u (t, ·)) k`. A `C^∞`
statement in `t` is therefore **not derivable** from the permitted hypothesis —
it needs the Duhamel differentiation of `TorusForcedMildOn` (still open, see
`EXISTENCE_ROUTE.md` §U9d2), or a further named input, which this lane was
forbidden to introduce. Delivered instead: the spatial half,
`mildPressure_spatial_contDiff : ∀ t ∈ Ico 0 T, ContDiff ℝ ∞ (fun x ↦ mildPressure g u (t, x))`.

### 3.2 Joint continuity on the slab (weaker, still not delivered)

```lean
ContinuousOn (mildPressure g u) (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
```

**Obstacle, updated.** The periodic convolution theorem this needed is now
proved in this lane, so only two ingredients are missing:

1. a locally uniform all-order weighted convolution bound — for each compact
   `K ⊆ Ico 0 T` and each `N`,
   `sup_{t ∈ K} ∑_k periodicFrequencyWeight k ^ N * ‖torusPhysicalCoeff 2 (torusConvectionDatum (u t) (u t)) i k‖ < ∞`.
   This needs `W(k)^N ≤ 4^N (W(l)^N + W(k−l)^N)` (the `ConvolutionBound.lean`
   weight shift `weight_cube_shift` is stated only at exponent 3) plus two
   Cauchy products, and the uniform coefficient bound
   `∑_k W(k)^N ‖û(t,k)‖ ≤ ‖torusRecoveryWeight‖ * ‖u_{2N+3} t‖` with
   `ContinuousOn u_{2N+3}` giving boundedness on `K`;
2. continuity of `t ↦ ∑' l, û_j(t,l) * û_i(t,k−l)` at fixed `k` (dominated
   convergence against the same bound).

Estimated ≥ 200 further lines; deliberately not attempted inside this lane.

### 3.3 Not in scope, recorded for the assembly lane

`momentum` / `projected` (needs the time derivative of the mild solution) and
`velocity_smooth` are not pressure fields and were not attempted here.

## 5. The periodic convolution theorem (new, supplied by this lane)

```lean
theorem periodicFourierCoeff_mul {f g : Space → ℂ}
    (hpf : IsPeriodicSpatial f) (hsf : ContDiff ℝ ∞ f)
    (hpg : IsPeriodicSpatial g) (hsg : ContDiff ℝ ∞ g) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ f x * g x) k =
      ∑' l, periodicFourierCoeff f l * periodicFourierCoeff g (k - l)
```

Proof: expand `torusLift f` as its own Fourier series
(`eq_torusScalarSeries_of_smooth` + `torusScalarSeries_lift` give
`torusLift_eq_tsum_mFourier`), push the character `mFourier (-k)` and
`torusLift g` inside the `tsum` (`tsum_mul_right`, `tsum_mul_left`,
`mFourier_add`), then exchange `∫` and `∑'` by
`integral_tsum_of_summable_integral_norm`; the norm hypothesis is
`∑' l ‖f̂(l)‖ * ∫ ‖torusLift g‖ < ∞`, which uses the lane's own
`summable_weight_pow_mul_coeff … 0`.

Errors hit while writing it: `tsum_mul_right` / `tsum_mul_left` needed the `←`
direction (the goal has the scalar outside); and
`integral_tsum_of_summable_integral_norm` is oriented `∑' ∫ = ∫ ∑'`, so the
rewrite is `rw [← …]`. The component bridge then needed
`euclidean_sum_apply` (`(∑ j, w j) i = ∑ j, w j i`, via `map_sum` of
`EuclideanSpace.proj`; `PiLp.sum_apply` does not exist), and a
`show`-restatement in `torusConvectionDatum_isPeriodicDatum` to clear a beta
redex that blocked `rw`.

## 4. Positive record — what the construction does buy

* One general theorem `lerayPotential_poisson` gives `Δp = ∇·S` for **every**
  smooth periodic vector source `S`, by Fourier uniqueness
  (`periodic_eq_of_coeff_eq`), not by term-by-term differentiation of a series.
* `lerayPotentialCoeff_leray_complement` is stated against T10's `periodicLeray`
  at an arbitrary Sobolev order `s`, so the assembly lane can feed it whichever
  datum it has.
* The canonical convection datum of `ConvolutionBound.lean` is now identified
  with the physical tensor divergence, so `F − Q` is available on the
  coefficient side and `∇p` is literally `(I − P)(F − Q)`.
* Every pressure slice is in every periodic `H^m`, with the explicit datum
  `W(k)^{m/2} p̂(t)(k)`.
* The construction is proved **not** to be the zero map:
  `lerayPotential_test_ne_zero` and `mildPressure_nonzero_instance` exhibit a
  one-mode smooth periodic force, a genuine persistent coefficient path, and a
  nonzero constructed pressure slice.
