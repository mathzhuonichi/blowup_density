# T12 U4b — the verbatim `velocityCriticalL3` by torus density (lane 401)

Module `formalization/NSFormalization/Section3/T12/CriticalL3Density.lean`.
Closes the residual recorded in `research/T12/ATTEMPTS_U4.md` §"The residual".

## What closed

```
theorem velocityCriticalL3 (v : SpatialField) (hv : MemPeriodicHomogeneous (1 / 2) v) :
    periodicLpENorm 3 v ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v
```

verbatim the API field (`research/T12/probes/api_on_canonical.lean:148-151`), same
constant `CcriticalHalf` as lane 396's `velocityCriticalL3_smooth`.  Route =
`T12_SPLIT.md` U4 option **(A)**, symmetric Fourier truncation (option (B),
mollification, was not needed: the truncation multiplier is the indicator of a
symmetric box, which is exactly the `SpectralGap.reweightDatum` shape already in
the tree, whereas a periodic mollifier would have required constructing `φ_ε` and
computing `φ̂_ε`).

Chain, with the exact reused declarations:

1. `truncField v S x = WithLp.toLp 2 (fun i ↦ (finitePeriodicFourierSum (v̂ᵢ) S x).re)`,
   built on `Paper1.finitePeriodicFourierSum` / `Paper1.periodicCharacter`
   (`Paper1/PeriodicFiniteL3.lean:18`, `Paper1/PeriodicFourierDerivative.lean:24`).
2. `torusLift_finitePeriodicFourierSum` (the lift of a physical partial sum is
   `∑ k ∈ S, mFourier k z * c k`, copied from the chart computation of
   `Paper1.periodicFourierCoeff_eq_cube`) and
   `periodicFourierCoeff_finitePeriodicFourierSum` (orthogonality, via the
   existing `T10.integral_mFourier`).
3. Realness: `conj_finitePeriodicFourierSum_real` from
   `T10.periodicFourierCoeff_real_neg` (conjugate symmetry of the coefficients of
   a real field) plus `S = -S`; hence `ofReal_truncField_apply`, so the `.re` is
   not a truncation of the data, and `periodicFourierCoeff_truncField` is exact.
4. `freqBox N = Fintype.piFinset (fun _ ↦ Finset.Icc (-N) N)` is symmetric,
   monotone and cofinal (`exists_freqBox_superset` via
   `S.sup (univ.sup (natAbs ∘ ·))`), so `tendsto_freqBox : Tendsto freqBox atTop atTop`.
5. `isMeanZeroT_truncField` from `T10.periodicFourierCoeff_zero_eq_mean_component`
   (the zero mode of a mean-zero field vanishes, so the truncation keeps mean zero
   whether or not `0 ∈ S`).
6. `periodicHomogeneousENorm_truncField_le`: `reweightDatum (indicator S) 1 …`
   applied to any homogeneous datum of `v`, with `reweightDatum_norm_le` /
   `reweightDatum_real`; the `iInf`-over-data pattern is copied verbatim from
   `CriticalL3.periodicSobolevENorm_zero_le_half`.
7. `tendsto_eLpNorm_truncField_sub`: componentwise from Mathlib's
   `UnitAddTorus.hasSum_mFourier_series_L2` (the Hilbert basis `mFourierBasis`),
   with `T10.fourier_repr_toLp` identifying `mFourierCoeff` with
   `periodicFourierCoeff`, `Lp.tendsto_Lp_iff_tendsto_eLpNorm'`, and
   `ContinuousMap.toLp` linearity to see the `Lp` partial sum as the lift of the
   physical partial sum; the three components are recombined by `eLpNorm_sum_le`
   and `‖x‖ ≤ ∑ i, |x i|`.
8. `memPeriodicHomogeneous_of_smooth` (new, general order `s ≥ 0`): reweight the
   inhomogeneous datum of `T10.smooth_periodic_datum` by
   `homogeneousDatumWeight s k / periodicFrequencyWeight k ^ (s/2)` (`≤ 1` by the
   public `homogeneousDatumWeight_le_periodicFrequencyWeight_rpow`).  Needed only
   to make the probe non-vacuous — the tree had `smooth_homogeneous_datum_one`
   (`T10/ForcePaths.lean:280`) at order `1` only.
9. `tendstoInMeasure_of_tendsto_eLpNorm` → `TendstoInMeasure.exists_seq_tendsto_ae`
   → `Lp.eLpNorm_lim_le_liminf_eLpNorm` at `p = 3` (valid for an arbitrary
   measure; confirmed by the lane-396 reviewer) → `Filter.liminf_le_liminf` +
   `Filter.liminf_const`.

The finiteness conjunct of `MemPeriodicHomogeneous (1/2) v` is **not used**: the
proof works uniformly (when the right-hand side is `⊤` every bound is trivial),
so only periodicity-free `MemLp (torusLift v) 2` + `IsMeanZeroT v` enter.

## Rejected / failed approaches

- **Uniform (absolutely convergent) Fourier reconstruction**
  (`Paper1.hasSum_periodicFourier_physical`, `…_partialSums`) needs
  `Summable (periodicFourierCoeff f)`.  Cauchy–Schwarz against `Ḣ^{1/2}` requires
  `∑_{k≠0} |2πk|^{-1} < ∞` on `ℤ³`, which **diverges** (exponent must exceed 3).
  So the `Ḣ^{1/2}` datum does not give absolute convergence and the whole
  `FourierReconstructionAdapter` / `PeriodicH2Uniform` line is unusable here; the
  `L²` Hilbert-basis route is the only one available.
- **Three separate a.e. extractions (one per component)** would produce nested
  subsequences; replaced by one vector-valued `eLpNorm` bound
  (`eLpNorm_mono` + `eLpNorm_sum_le` + `eLpNorm_norm`) and a single
  `exists_seq_tendsto_ae`.
- **Asymmetric frequency sets.**  Taking `.re` of `∑_{k∈S} v̂(k)e_k` for a
  non-symmetric `S` changes the coefficients (it symmetrises them), so
  `periodicFourierCoeff_truncField` would be false.  Every statement about
  `truncField` therefore carries `hS : ∀ k ∈ S, -k ∈ S`.

## Pin-specific pitfalls hit (v4.34.0-rc2 + this Mathlib)

- `Finset.sum_image` is `{s : Finset κ} {g : κ → ι} : Set.InjOn g ↑s → ∑ x ∈ s.image g, f x
  = ∑ x ∈ s, f (g x)`: the summand is `f`, the map is `g`, the injectivity is
  `Set.InjOn` (not `∀ x ∈ s, ∀ y ∈ s, …`), and higher-order unification of `f`
  fails on `∑ k ∈ S, χ_{-k} x * c (-k)` — both `(f := …)` and `(g := …)` must be
  given explicitly.  `S.image Neg.neg` and `S.image (fun k ↦ -k)` also do not
  unify by `rw` alone.
- `zero_le` in `ℝ≥0∞` takes **no** explicit argument here, so `zero_le _` fails
  with "Function expected"; write `zero_le`.
- `MeasureTheory.integral_finset_sum` and `tendsto_finset_sum` are deprecated in
  favour of `integral_finsetSum` / `tendsto_finsetSum`; `Tests` is
  `warningAsError`, so the deprecated spellings must not be left in.
- `-m + k = 0 ↔ m = k` is `neg_add_eq_zero` (`linarith` does not act on
  `Fin 3 → ℤ`).
- `Lp ℂ 2 periodicTorusMeasure` and Mathlib's `L²(UnitAddTorus (Fin 3))`
  (i.e. `Lp ℂ 2 volume`) unify only because `Paper1.periodicTorusMeasure` is an
  `abbrev` for `volume` under the same `local instance : MeasureSpace UnitAddCircle`;
  the precedent is `T10/Parseval.lean`, and new code should keep using the
  `periodicTorusMeasure` spelling so elaboration matches.
