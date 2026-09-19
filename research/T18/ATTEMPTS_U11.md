# T18 U11 attempts and elaboration ledger

## Successful route

- The upstream bounds really contain four powers:
  `C_F(ε^(1/2)+ε^(1/2-s))` and
  `C_H(ε^(3/2)+ε^(3/2-s))`.  For `0<ε≤1` and `0≤s`, antitonicity
  in the exponent absorbs the first term of each pair.  Therefore the chosen
  Spec constant is
  `2 * (scaling.sobolevConst s + correction.sobolevConst s)`.
- `periodicDatum_add` and datum uniqueness turn `MemLp.add` and
  `eLpNorm_add_le` into the triangle inequality for the infimum-over-paths
  `forceSobolevENormT`.
- T11's existing `persistenceDown t s` is the required contractive Bessel
  multiplier.  `persistence_datum_of_reweight` shows that it represents the
  same physical slice, giving both `forceSobolevENormT_mono_order` and
  `memForceSobolevT_mono_order`.
- For `s<0`, monotonicity bounds the order-`s` difference norm by its order-zero
  norm.  The proved U11 estimate at `s=0` tends to zero by
  `Paper1.sobolev_error_tendsto_zero`; squeezing closes the limit.  Lowering
  the honest order-zero path closes `negative_s_memLp`.

## Failed and corrected elaboration attempts

### 0. The referenced lane-438 report is absent from this base

The requested report path is not present in this worktree; attempting to read
it produced exactly:

```text
sed: can't read research/T17/REPORT_438.md: No such file or directory
```

`rg --files | rg 'REPORT_438'` also returned no match.  This was not a proof
blocker: the checked-in T11 module already contains the stronger reusable
pieces `persistenceDown`, `persistenceDown_reweight`, and
`persistence_datum_of_reweight`, from which U11's local monotonicity theorem is
proved.

### 1. Elaborating before building the newly imported dependency

The first direct `lake env lean` preceded the required dependency build and
failed exactly with:

```text
../formalization/NSFormalization/Section3/T18/SobolevRate.lean:1:0: error: object file '/data_8T/ping/blowup_density/.claude/worktrees/445-T18-U11-sobolev-rate/formalization/.lake/build/lib/lean/NSFormalization/Paper1/ScalingLimits.olean' of module NSFormalization.Paper1.ScalingLimits does not exist
```

Building `NSFormalization.Paper1.ScalingLimits` and
`NSFormalization.Section3.T11.Persistence` fixed this staging error.

### 2. Assuming an integrable-data Fourier additivity lemma already existed

`PeriodicSmoothSobolev.periodicFourierCoeff_add` requires continuity and lives
in another namespace; the available T10 integrable lemma was only for
subtraction.  The attempted unqualified use failed exactly with:

```text
../formalization/NSFormalization/Section3/T18/SobolevRate.lean:43:5: error(lean.unknownIdentifier): Unknown identifier `periodicFourierCoeff_add`
```

The module now proves `periodicFourierCoeff_add_integrable` directly by
`integral_add`, using the integrability conjunct already carried by
`IsPeriodicDatum`.

### 3. Asking `positivity` to discover positivity hidden behind record fields

The first proof of the assembled constant and the two real bound expressions
used bare `positivity`.  It did not unfold the threaded positivity fields:

```text
../formalization/NSFormalization/Section3/T18/SobolevRate.lean:163:2: error: failed to prove positivity/nonnegativity/nonzeroness
../formalization/NSFormalization/Section3/T18/SobolevRate.lean:209:58: error: failed to prove positivity/nonnegativity/nonzeroness
../formalization/NSFormalization/Section3/T18/SobolevRate.lean:212:58: error: failed to prove positivity/nonnegativity/nonzeroness
```

These are now explicit applications of
`scaling.sobolevConst_pos`, `correction.sobolevConst_pos`, `mul_pos`,
`mul_nonneg`, and `Real.rpow_nonneg`.

### 4. Using the old argument order for `Real.rpow_nonneg`

At this Mathlib pin, the theorem takes the proof `0 ≤ ε` before the exponent;
passing `ε` itself produced exactly:

```text
../formalization/NSFormalization/Section3/T18/SobolevRate.lean:221:32: error: Application type mismatch: The argument
  ε
has type
  ℝ
of sort `Type` but is expected to have type
  0 ≤ ?m.633
of sort `Prop` in the application
  Real.rpow_nonneg ε
```

The corrected calls are `Real.rpow_nonneg hε.1.le exponent`.

### 5. Wrong Unicode glyph for the neighborhood notation

An initial transcription used a visually similar script capital instead of
Lean's neighborhood notation.  The parser errors were:

```text
../formalization/NSFormalization/Section3/T18/SobolevRate.lean:259:11: error: unexpected token '>'; expected ':' or term
../formalization/NSFormalization/Section3/T18/SobolevRate.lean:308:9: error: expected token
```

The theorem now spells the filter without glyph ambiguity as
`nhdsWithin (0 : ℝ) (Ioi 0)` and the target as `nhds (0 : ℝ≥0∞)`.

### 6. Applying `ENNReal.tendsto_ofReal` before normalizing the target zero

Direct `apply` did not identify `nhds (ENNReal.ofReal 0)` with `nhds 0` early
enough.  The exact error was:

```text
../formalization/NSFormalization/Section3/T18/SobolevRate.lean:314:4: error: Tactic `apply` failed: could not unify the conclusion of `@ENNReal.tendsto_ofReal`
  Tendsto (fun a => ENNReal.ofReal (?m a)) ?f (𝓝 (ENNReal.ofReal ?a))
with the goal
  Tendsto (fun ε => ENNReal.ofReal (forceDiffSobolevConst data 0 * (ε ^ (1 / 2 - 0) + ε ^ (3 / 2 - 0)))) (𝓝[>] 0) (𝓝 0)

Note: The full type of `@ENNReal.tendsto_ofReal` is
  ∀ {α : Type ?u.75} {f : Filter α} {m : α → ℝ} {a : ℝ},
    Tendsto m f (𝓝 a) → Tendsto (fun a => ENNReal.ofReal (m a)) f (𝓝 (ENNReal.ofReal a))
```

Introducing the real-valued limit as `hr` and finishing with
`simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hr` resolves it.

### 7. Probe parsing without the `ENNReal` scoped notation

The standalone probe initially omitted `open scoped ENNReal`, giving:

```text
../research/T18/probes/u11_closes.lean:74:29: error: expected token
../research/T18/probes/u11_closes.lean:98:49: error: expected token
../research/T18/probes/u11_closes.lean:188:6: error: `negative_s_memLp` is not a field of structure `Spec.PeriodicInsertionU11Fields`
../research/T18/probes/u11_closes.lean:189:16: error(lean.unknownIdentifier): Unknown identifier `Spec.MemForceSobolevT`
```

The last two were parser cascades.  Opening the scope fixed all four.

### 8. Treating the copied Spec honesty carrier as definitionally identical

After unfolding only the probe copy, Lean still saw the canonical wrapper
`NSFormalization.Section3.T15.MemForceSobolevT`.  The exact leading error was:

```text
../research/T18/probes/u11_closes.lean:190:4: error: Type mismatch: After simplification, term
  NSFormalization.Section3.T18.forceDifference_sobolev_memLp data
has type
  ∀ (s : ℝ), 0 ≤ s → s < 1 / 2 → ∀ ε ∈ Ioc 0 (NSFormalization.Section3.T18.ε₀ data),
    MemForceSobolevT 1 s (fun z => NSFormalization.Section3.T18.force data ε z - data.g z)
but is expected to have type
  ∀ (s : ℝ), 0 ≤ s → s < 1 / 2 → ∀ ε ∈ Ioc 0 (NSFormalization.Section3.T18.ε₀ data),
    ∃ G, NSFormalization.Section3.T10.IsPeriodicSobolevPath s
      (fun z => NSFormalization.Section3.T18.force data ε z - data.g z) G ∧
      MemLp G 1 forceTimeMeasure
```

Unfolding both wrappers exposed one remaining bridge issue.

### 9. The two copied `forceTimeMeasure` names need their registered bridge

Even after both honesty wrappers were unfolded, the canonical and contract
measure names remained distinct.  The exact terminal difference in both the
positive and negative guard errors was:

```text
but is expected to have type
  … ∃ G,
    NSFormalization.Section3.T10.IsPeriodicSobolevPath s … G ∧
      MemLp G 1 forceTimeMeasure
```

where the inferred canonical term printed:

```text
… ∧ MemLp G 1 NSFormalization.Section4.A02.forceTimeMeasure
```

The final probe destructs the canonical witness and rebuilds the Spec witness,
using `Bindings.TorusLocalTheory.isPeriodicSobolevPath_eq` and
`Bindings.datumLemmas_forceTimeMeasure_eq` explicitly.  This also makes the
conversion evidence readable instead of relying on a large `simpa`.

There is no remaining proof or elaboration error.
