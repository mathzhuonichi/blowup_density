# T20 U8 — `criticalEnergy` (`eq:criticalenergy`, `03-torus.tex:420-440`), lane 415

Target: the `criticalEnergy` field of `CriticalRegularityTAPI`
(`Section3/T20/CriticalRegularity.lean:286-299`), verbatim, with
`C₀ = criticalTrilinearConst` (lane 413).
Delivered: `formalization/NSFormalization/Section3/T20/CriticalEnergy.lean`,
theorem `NSFormalization.Section3.T20.criticalEnergy`. No named input, no
residual, no `maxHeartbeats` override.

## What the proof actually is

Everything is done on the **Fourier side** and only the nonlinear term is taken
back to physical space (that is where U7 lives).

1. `y(r)² = ∑ₖ |2πk| ∑ᵢ |û_i(k,r)|²` — `criticalY_toReal_sq_eq_tsum`.
   Two ingredients: (a) the mean-reduction slice identity
   `v(r,·) = meanZeroPartT (u(r,·))` (`meanFreeVelocity_slice_eq`, from lane
   389's `periodicMeanReductionAPI.mean_formula`, i.e. `m(t) = ∫_{T³} u(t)`),
   without which `periodicHomogeneousENorm` of `v(r,·)` is not the Fourier
   series of `u`'s coefficients at all; (b) `T13.exists_homogeneous_datum`,
   which supplies *both* the datum (hence
   `periodicHomogeneousENorm = ‖A‖ₑ` by `T13.homogeneousDatum_unique`) and the
   tsum formula for `‖A‖²` in one shot. `homENorm_toReal_eq_norm` /
   `homENorm_toReal_sq` package this.
2. Differentiating that series: `hasDerivAt_tsum_critFreqEnergy`, the exact
   T11 template `hasDerivAt_torusSobolevNormAt_sq` with the inhomogeneous weight
   `periodicFrequencyWeight k ^ s` replaced by the homogeneous
   `homogeneousDatumWeight (1/2) k ^ 2`. The only new input is
   `homogeneousDatumWeight (1/2) k ^ 2 = √(4π²|k|²) ≤ 1 + 4π²|k|² =
   periodicFrequencyWeight k ^ (1 : ℝ)`
   (`T12.sqrt_angularFrequencySq_le_weight`), which makes T11's order-`1`
   majorant dominate the homogeneous order-`1/2` term verbatim, so
   `T11.abs_freqEnergyDerivT_le (m := 1)` is reused unchanged.
3. The frequency split `rawEnergyDeriv_split`: T11's `freqEnergyDerivT_split`
   instantiated at `m = 0` (where `periodicFrequencyWeight k ^ (0:ℝ) = 1`, so
   `datum_pair_entry` turns the datum pairings into raw-coefficient pairings).
   The **pressure term is already gone** there, by coefficient-side
   solenoidality — nothing new was needed for it.
4. The force term: build the order-`1/2` homogeneous data `Av` of `v(t,·)` and
   `Bh` of `h(t,·)`; termwise `conj(Av_i) Bh_i = W_k² conj(v̂_i) ĥ_i`, and off
   the zero mode `v̂ = û`, `ĥ = ĝ` (`T13.periodicFourierCoeff_meanZeroPart`),
   while at `k = 0` the weight is `0`. Then `T11.torusRealPairing_le` **is** the
   paper's `|⟪Λ^{1/2}h, Λ^{1/2}v⟫| ≤ b y`; only the one-sided form is needed.
5. The convection term: torus Parseval for the real `L²` pairing
   (`hasSum_periodicPairing`, from Mathlib's
   `UnitAddTorus.hasSum_prod_mFourierCoeff` per component) plus
   `IsPeriodicLambda`'s coefficient clause turn
   `∑ₖ |2πk| Re(∑ᵢ conj(û_i) N̂_i)` into `⟪(v·∇)v, Λv⟫`, and lane 413's
   `criticalTrilinear_pairing` bounds it by `C₀ y z²`. The physical `Λv` witness
   comes from `T12.lambda_exists`.
6. Constant transport `(m·∇)v`: **not** done by the physical skew-adjointness
   route.

## Negative results / routes NOT taken, and why

- **U4 `constantTransportSkew` (physical skew-adjointness) is useless for U8.**
  Making `⟪(m·∇)v, Λv⟫ = 0` from it needs two facts that are *not* in the tree:
  U5 `constantTransportCommutesLambda` (unproved) and self-adjointness of `Λ`
  (nowhere). On the Fourier side the same statement is three lines: the symbol
  `∑ⱼ mⱼ·2πikⱼ` is purely imaginary and `∑ᵢ conj(ĉᵢ)ĉᵢ` is real, so the real
  part vanishes at every frequency (`re_sum_conj_fderiv_dir_zero`). **U8 does not
  depend on U5.**
- **Polarization route for the pairing Parseval** (`‖A+B‖²-‖A‖²-‖B‖²` through
  `T10.datum_norm_sq_integral`) was prepared as a fallback and never needed;
  Mathlib's `UnitAddTorus.hasSum_prod_mFourierCoeff` is a direct inner-product
  Parseval and is cheaper. Recorded because it is the only in-repo route if that
  Mathlib lemma ever moves.
- **Building the convection's order-`1/2` datum in `PeriodicSobolev`** (to use
  `T11.hasSum_datum_pair` for the nonlinear term as well) was abandoned: the
  convection field is not mean-zero, so `IsPeriodicHomogeneousDatum` does not
  apply and the `Memℓp` element would have to be built by hand. Pairing
  `Λv` against `(v·∇)v` through Parseval avoids the issue entirely.
- **`rw [← integral_ofReal]`** fails here: `integral_ofReal` is `RCLike`-general
  and its coercion head does not match `Complex.ofReal`; use the ℂ-specialised
  `integral_complex_ofReal` forwards.
- **`Complex.real_smul` does not apply to `IsPeriodicHomogeneousDatum`**: that
  clause is `(homogeneousDatumWeight s k : ℂ) • …`, i.e. a **ℂ**-smul, so the
  rewrite is `smul_eq_mul`. Cost one compile round.
- **`rw` closing by `rfl` does not see through `velocityCoeffT`**: statements
  mixing `velocityCoeffT u i k t` with
  `periodicFourierCoeff (fun x ↦ ((u (t,x) i : ℝ) : ℂ)) k` must be bridged by
  `exact`/type ascription (definitional), never by `rw`. Cost one compile round.
- **`homogeneousDatumWeight` is `Real.rpow` in function form**, so
  `split_ifs` leaves a goal closed only by `rfl`, and `if_neg` is deprecated in
  this pin (already recorded for lane 405; hit again here).
- `continuous_finset_sum` is deprecated in this pin → `continuous_finsetSum`.

## Parallel-work note

The four pieces were first developed as standalone scratch files
(`research/T20/probes/u8_{parseval,transport,deriv,main}.lean`, three of them by
parallel workers) and then merged verbatim into the single module; the scratch
files were deleted after the merge, since every declaration in them now lives in
`Section3/T20/CriticalEnergy.lean`.

## Gates

- `lake build NSFormalization.Section3.T20.CriticalEnergy` — 0 errors.
- `lake env lean` on the module — no output.
- `research/T20/probes/critical_energy_closes.lean` — no output (field-type match
  by `exact` against `CriticalRegularityTAPI.criticalEnergy`, plus a non-vacuity
  instance).
- `research/T20/axioms_u8.lean` — all 21 declarations
  `[propext, Classical.choice, Quot.sound]`.
- `make check` — OK.
