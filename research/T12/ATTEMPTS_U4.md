# T12 U4 — `velocityCriticalL3`, attempts and residual (lane 396)

Module `formalization/NSFormalization/Section3/T12/CriticalL3.lean`.

## What closed

`velocityCriticalL3_smooth (v) (SmoothPeriodicT v) (IsMeanZeroT v) :
  periodicLpENorm 3 v ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1/2) v`,
with `CcriticalHalf = criticalL3Const * cutoffGagliardoConst * (gapConst (1/2) + 1)` and
`CcriticalHalf_pos`.

Route (exactly `research/T12/T12_SPLIT.md` U4):
1. `periodicLpENorm 3 v = eLpNorm v 3 (volume.restrict fundamentalCube)`
   (`HaarCube.periodicLpENorm_eq_restrict`, periodicity from `hv.2`).
2. `= eLpNorm (cutoffMul v) 3 (volume.restrict fundamentalCube)` since `cutoffMul v = v` on
   the cube (`Cutoff.cutoffMul_eq_on_cube` + `ae_restrict_of_forall_mem
   measurableSet_fundamentalCube` + `eLpNorm_congr_ae`).
3. `≤ eLpNorm (cutoffMul v) 3 volume` (`eLpNorm_mono_measure _ Measure.restrict_le_self`).
4. `≤ ENNReal.ofReal criticalL3Const * dotHomogeneousENorm (1/2) (cutoffMul v)` — registered
   whole-space `A05.velocityCriticalL3 (cutoffMul v) (memHInfty_cutoffMul hv.1)`, then the
   norm spelling rewritten by the local rfl bridge `a05_dotHomogeneousENorm_eq :
   A05.dotHomogeneousENorm = D01.dotHomogeneousENorm` (same body as
   `Bindings/GradientL6V2.lean:44`; reproved here because `formalization/` cannot import the
   `verification/Bindings` layer).
5. `≤ ofReal criticalL3Const * (ofReal cutoffGagliardoConst * (‖v‖_{L²(Q)} +
   periodicHomogeneousENorm (1/2) v))` — the U3 core `cutoff_gagliardo_half v hv hmean`
   (`gcongr`).
6. absorb `‖v‖_{L²(Q)} ≤ ofReal (gapConst (1/2)) * periodicHomogeneousENorm (1/2) v`
   (`l2Q_le_homogeneous_half`), then ℝ≥0∞ semiring algebra (`ENNReal.ofReal_add/_mul`,
   `ring`) collapses the constant to `CcriticalHalf`.

`l2Q_le_homogeneous_half` chain: `eLpNorm v 2 (restrict Q) = eLpNorm (torusLift v) 2 Haar`
(`HaarCube.eLpNorm_torusLift_eq_restrict`, reversed) `= periodicSobolevENorm 0 v`
(`T15.periodicSobolevENorm_zero_eq`, order-zero Parseval) `≤ periodicSobolevENorm (1/2) v`
(new `periodicSobolevENorm_zero_le_half`, below) `≤ ofReal (gapConst (1/2)) *
periodicHomogeneousENorm (1/2) v` (`SpectralGap.spectralGap` at `s = 1/2`).

`periodicSobolevENorm_zero_le_half` (physical `L²` ≤ inhomogeneous `H^{1/2}`): from any
order-`1/2` datum of `v`, the bounded even multiplier `w k = periodicFrequencyWeight k ^
((0 - 1/2)/2)` (|w| ≤ 1 by `Real.rpow_le_one_of_one_le_of_nonpos` and `one_le_fourierWeight`,
even by `fourierWeight_neg`) yields the order-`0` datum by `SpectralGap.reweightDatum`, whose
`ℓ²` norm is ≤ the order-`1/2` norm by `reweightDatum_norm_le` (the coefficient identity
`w k · pfw^{1/4} = pfw^0 = 1` is `Real.rpow_add`).

The `∀`-quantified field is over `SmoothPeriodicT ∧ IsMeanZeroT`; finiteness of the
homogeneous norm is **not** assumed (when it is `⊤` the RHS is `⊤` and the bound is trivial,
`ENNReal.mul_top` with `ofReal CcriticalHalf ≠ 0`), and `MemPeriodicHomogeneous (1/2) v`
needed by `spectralGap`/`l2Q_le_homogeneous_half` is then rebuilt from smoothness
(`memLp_torusLift_vector`), mean-zero, and the finite branch.

Every declaration audits to `[propext, Classical.choice, Quot.sound]`
(`research/T12/axioms_u4.lean`).

## The residual: the general `MemPeriodicHomogeneous (1/2)` field

Exact statement not proved (the verbatim API field):

```
theorem velocityCriticalL3 (v : SpatialField) (hv : MemPeriodicHomogeneous (1 / 2) v) :
    periodicLpENorm 3 v
      ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v
```

`MemPeriodicHomogeneous (1/2) v = IsPeriodicSpatial v ∧ MemLp (torusLift v) 2
periodicTorusMeasure ∧ IsMeanZeroT v ∧ periodicHomogeneousENorm (1/2) v ≠ ⊤` (checked in
`MeanZeroCalculus.lean:60`) carries **no smoothness**, while both analytic inputs require it:
`memHInfty_cutoffMul` needs `ContDiff ℝ ∞ v` and `cutoff_gagliardo_half` needs
`SmoothPeriodicT v`. So the general case genuinely requires an approximation step, not a
reindexing.

Residual proof obligation (torus density / mollification, an `L` campaign, deliberately not
attempted here):

- construct a periodic mollification `v_ε` (convolution with a smooth periodic approximate
  identity), smooth, periodic, mean-zero;
- coefficient multiplier bound `periodicHomogeneousENorm (1/2) v_ε ≤
  periodicHomogeneousENorm (1/2) v` (mollifier symbol `|φ̂_ε(k)| ≤ 1`, a `reweightDatum`-style
  step);
- `v_ε → v` a.e. (or in `L²`), and lower semicontinuity of `eLpNorm · 3` under a.e.
  convergence (Fatou) to get `periodicLpENorm 3 v ≤ liminf periodicLpENorm 3 v_ε`;
- apply `velocityCriticalL3_smooth` to each `v_ε` and pass to the `liminf`.

Mathlib's `MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm` supplies lower semicontinuity for
arbitrary measures, including torus Haar; the remaining work is the smooth periodic mean-zero
approximation, its homogeneous norm control, and convergence — hence a separate lane (U4b), not a
silent weakening of the field. (Corrected after review 396.)

## Failed approaches / pitfalls (pin renames, private lemmas)

- `mul_le_mul_left'` is **not** resolvable in this environment (`unknown identifier`) — the
  monotonicity steps `c * a ≤ c * b` were done with `gcongr` instead. `gcongr` on the absorb
  step also discharges the leaf `L ≤ gapConst·H` from `hL` in context by assumption, so an
  explicit `exact hL` after it is a "no goals" error; dropped it.
- `SpectralGap.reweightDatum_enorm_le`, `periodicFrequencyWeight_pos`,
  `periodicFrequencyWeight_neg` are **private**; reconstructed the enorm bound from the public
  `reweightDatum_norm_le` via `ofReal_norm` + `ENNReal.ofReal_le_ofReal`, and used the public
  `FourierEmbeddings.one_le_fourierWeight` / `fourierWeight_neg` for positivity and evenness.
- `ParsevalZero.memLp_torusLift_smooth` is **private**; the `MemLp (torusLift v) 2` fact came
  from the public `T10.memLp_torusLift_vector hv.1.continuous 2` instead.
- `simpa … using reweightDatum_norm_le …` could not close the iInf leaf `‖⟨reweightDatum…,
  hmem0⟩‖ₑ ≤ ‖A.1‖ₑ` because the subtype/underlying norm equality is defeq but not
  syntactic; split off a separate `hnorm : ‖reweightDatum…‖ₑ ≤ ‖A.1.1‖ₑ` and closed the leaf
  by `exact hnorm` (defeq, exactly as `SpectralGap.homogeneous_le_sobolev` relies on
  `le_rfl`).
- the mixed `ℂ • (ℝ • ℂ)` scalar chain in the order-0 datum identity was normalized with
  `simp only [smul_eq_mul, Complex.real_smul]` then `← mul_assoc, ← Complex.ofReal_mul` and the
  real scalar identity `w k · pfw^{1/4} = pfw^0`.
