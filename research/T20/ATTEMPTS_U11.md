# ATTEMPTS — T20 U11 `continuationBound` (lane 437)

Target: `Section3/T20/Continuation.lean`, `NSFormalization.Section3.T20.continuationBound`,
the `continuationBound` field of `CriticalRegularityTAPI` verbatim
(`03-torus.tex:486-500`, `eq:criterion`) at `c = criticalSmallnessH1`,
`Ccriterion = hTwoConst ^ 2 * CH1`.

Closed with **no residual and no named input**.  27 declarations, all
`[propext, Classical.choice, Quot.sound]`.

## 1. What turned out to be the real difficulty (and what did not)

* The **orthogonal mode decomposition** `‖u‖²_{H²} = |m|² + ‖v‖²_{H²}` is the only
  genuinely new torus mathematics, and it is short: `IsPeriodicDatum` pins the
  coefficients uniquely, `periodicFourierCoeff_const` deletes the zero mode of a
  constant, `periodicFrequencyWeight 0 = 1`, and T11's `hasSum_freqEnergyT` turns
  both sides into the same `HasSum`.  ~90 lines including the coefficient lemmas.
* The expected long pole — **integrating the differential inequality** — is cheap
  once the *order of operations* is changed.  Applying T12 `hTwo_le_laplacian`
  **before** integrating replaces `ν‖Δv(t)‖²₂` by `(ν/hTwoConst²)‖v(t)‖²_{H²}` in
  U10b's `eq:H1energy`.  The `H²` profile is continuous on the lifespan (from the
  decomposition above plus T11's `continuousOn_torusSobolevNormAt_velocity`),
  whereas **no continuity statement for `t ↦ ‖Δv(t)‖²₂` exists anywhere in the
  tree** and none had to be proved.  This is the single decision that made the
  unit an `M` instead of an `L`.
* `intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le` is the right FTC
  form: it needs only the *majorant* integrable, not the derivative.  The
  derivative witness from U10b is anonymous, so `deriv F` is used as the
  derivative function and `HasDerivAt.deriv` identifies it with `E'`.
* **Left endpoint.**  `F(a) = ‖∇v(a)‖²₂ → 0` as `a → 0⁺` does *not* need
  continuity of `gradientSqT` at `0`.  Termwise `|2πk|² ≤ 1 + |2πk|²` gives
  `F(a) ≤ ‖u(a)‖²_{H¹}`, which is continuous on `Ico 0 T` and vanishes at `0`
  because `w.initial` makes the slice identically zero; `squeeze_zero'` finishes.
* **Right endpoint.**  `S = T` is allowed by the field, so the FTC interval
  `[a,b]` can never reach `S`.  `MeasureTheory.setLIntegral_iUnion_of_directed`
  (`Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:646`) converts
  `∫⁻ over Ioo 0 S` into `⨆ n, ∫⁻ over Ioo 0 (S - S/(n+2))` **with no
  measurability hypothesis on the integrand** — which matters, because the
  integrand `t ↦ ‖v(t)‖²_{H²}` is only known to be nice on `Ico 0 T`.
* `MemForceT (meanFreeForce g)` is true and easy (off the compact time support of
  `g` every slice vanishes, hence so does its mean), so lane 312's
  `force_coefficient_path` applies to `h` directly at order `0`; with T10's
  `sobolevENorm_zero_eq` this gives continuity, `L¹`-ness on `(0,∞)` and
  `∫₀^∞‖h‖²₂ ≠ ⊤` in ten lines.  No new `L²` analysis.
* **U11 does not use U3 (`bIntegral`) or U6 (`meanFreeEquation`).**
  `T20_SPLIT.md` listed "Deps: U10b, U2"; that is exactly right, plus T12
  `hTwo_le_laplacian` and the `w.sobolev` datum path of `ClassicalSolutionT`.

## 2. Failed attempts, with the exact error text

1. **`HasSum.congr_fun` direction.**  Wrote
   `(hsv.add hsm).congr_fun fun k ↦ (freqEnergyT_two_split …).symm`:
   `error: Type mismatch … has type (freqEnergyT 2 (meanFreeVelocity g w.velocity) k t + if k = 0 then ‖meanPathT g t‖ ^ 2 else 0) = freqEnergyT 2 w.velocity k t but is expected to have type freqEnergyT 2 w.velocity k t = …`.
   `HasSum.congr_fun` wants `f b = g b` with `f` the *given* sum, so the `.symm`
   is wrong.
2. **`tsum_le_tsum` is gone in this pin.**
   `error(lean.unknownIdentifier): Unknown identifier 'tsum_le_tsum'`.  The lemma
   is now `Summable.tsum_le_tsum (hf : Summable f) (h : ∀ i, f i ≤ g i) (hg : Summable g)`.
3. **`if_pos` / `if_neg` are deprecated in this pin.**
   `warning: 'if_pos' has been deprecated: Use 'ite_eq_left' instead` and the same
   for `if_neg`; with `warningAsError` downstream these must go.  Replaced by
   `simp [hk]` and `simp only [… , hk, ↓reduceIte, …]`.
4. **`ContinuousOn.pow` + `simpa only [Nat.cast_ofNat]` eta-expands wrongly.**
   `error: Type mismatch: After simplification, term h has type ContinuousOn ((fun t => torusSobolevNormAt 2 w.velocity t) ^ 2) (Ico 0 T) but is expected to have type ContinuousOn (fun t => torusSobolevNormAt 2 w.velocity t ^ 2) (Ico 0 T)`.
   `simpa` rewrote through `Pi.pow`.  Fix: keep the term and rewrite only the
   cast, `rwa [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num] at h`.
5. **`nlinarith` on the absorbed inequality.**
   `error: linarith failed to find a contradiction` with the full U10b context on
   screen.  The missing step was the *product* `CH1·ν⁻¹·∫ₐᵇ‖h‖²₂ ≤ CH1·ν⁻¹·HFtot`,
   which is not linear in the atoms.  Supplying it as
   `mul_le_mul_of_nonneg_left hHle (by positivity)` makes the rest plain
   `linarith`.  The final module contains no `nlinarith` in the assembly
   (only two in elementary `div`/`sq` arithmetic).
6. **`rw [ge_iff_le, ← le_div_iff₀' hνc]`** on an already-`≤` hypothesis:
   `error: Tactic 'rewrite' failed: Did not find an occurrence of the pattern ?m ≥ ?m'`.
   Replaced by multiplying through: `mul_le_mul_of_nonneg_left` plus the identity
   `(c/ν)·((ν/c)·I) = I`.
7. **`field_simp` needs `hTwoConst ≠ 0`, not `hTwoConst ^ 2 ≠ 0`.**  With only
   `hc2.ne'` in the simp set the goal stalls at
   `⊢ (hTwoConst * ∫ …) / hTwoConst = ∫ …`.  `field_simp [hTwoConst_pos.ne']`
   closes it.  An earlier variant that stalled at
   `⊢ … - (hTwoConst ^ 2 * ν ^ 2 * ∫ …) * hTwoConst⁻¹ ^ 2 = …` after
   `field_simp; ring` had the same cause.
8. **Three `← ENNReal.ofReal_pow (norm_nonneg _)` in one `rw` list.**  The third
   fails: `error: Tactic 'rewrite' failed: Did not find an occurrence of the pattern ENNReal.ofReal ‖?m‖ ^ ?n in the target expression ENNReal.ofReal (‖A‖ ^ 2) = ENNReal.ofReal (‖meanPathT g t‖ ^ 2) + ENNReal.ofReal ‖B‖ ^ 2`
   — the placeholder's normed space is fixed by the first rewrite, and the three
   norms live in two different spaces (`PeriodicSobolev 2` and `Space`).  Fix:
   separate `rw`s with the argument given explicitly (`norm_nonneg A`,
   `norm_nonneg B`, `norm_nonneg (meanPathT g t)`).
9. **Named hole inside `rw`.**  `rw [hunion, setLIntegral_iUnion_of_directed _ ?dir]`
   followed by `case dir => …` gives `error: No goals to be solved`.  Hoist the
   directedness into a `have` before the `rw`.
10. **`Ioc a b ⊆ Ioi 0` with `lt_of_lt_of_le ha.1 hx.1`**:
    `error: Application type mismatch: The argument hx.left has type a < x but is expected to have type a ≤ x`.
    Use `lt_trans`.  Also `HasSubset.Subset.eventuallyLE` is deprecated in this
    pin (`Use 'LE.le.eventuallyLE' instead`); pass the subset as a `≤` and use
    `hsub.eventuallyLE`.
11. **`gcongr` discharged its own side goal.**  After
    `have hd : S / ((j:ℝ)+2) ≤ S / ((i:ℝ)+2) := by gcongr`, the follow-up
    `exact hS.le` gave `error: No goals to be solved` — `gcongr` found `0 ≤ S`
    from the context itself.

## 3. Notes for U12 / U13

* U12 consumes `continuationBound` exactly as written: the third conjunct plus
  the second give `squaredHTwoIntegralT S w.velocity ≠ ⊤` for every
  `0 < S ≤ T`, via the first conjunct (the identity).
* U13 installs `Ccriterion := hTwoConst ^ 2 * CH1` and `hCcriterion :=
  Ccriterion_pos`; `c` is still lane 432's `criticalSmallnessH1`, and
  `continuationBound` is stated at that `c`, so no re-shrinking is needed.
* Non-vacuity is again the zero force with the zero solution (lanes 415/428/432's
  sanctioned fallback); a nonzero-force instance still needs a compactly
  time-supported bump in `forceClassT` plus T11 local existence, neither of which
  is assembled anywhere in the tree.
* Reusable beyond U11: `memForceT_meanFreeForce` (the mean-free force is a test
  force — likely wanted by U12/U13), `zero_isPeriodicDatum`,
  `torusSobolevNormAt_initial`, `contDiff_meanPathT`, `enorm_rpow_two`,
  `coeff_meanZeroPart`, `continuousOn_meanFreeHTwoSq`.


> Lead correction after review 437: see `REPORT_437.md` "Lead notes" — the Laplacian-continuity absence claim is narrowed to the torus profile, and the T11 local theory/bump witness (`Section3/T11/Assembly.lean:99,182,525`) exists (nonzero initial data, not a U11 smallness instance).
