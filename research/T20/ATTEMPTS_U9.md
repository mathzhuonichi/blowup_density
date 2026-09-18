# T20 U9 (`yBound`, `eq:ybound`) — attempts, dead ends, pin-specific traps

Lane 428, 2026-09-18.  Module `formalization/NSFormalization/Section3/T20/YBound.lean`.

## What worked (the delivered route)

1. **`critLower`, one bounded even symbol instead of two maps.**  R43 lowers the
   force datum in two steps (`lowerVectorL 2 (1/2)` then the Bessel→homogeneous
   `ofSobolevVectorL`).  On the torus one symbol does both:
   `critSymbol k = |2πk|^{1/2} / (1+4π²|k|²)^{1/2}`, bounded by `1` because
   `homogeneousDatumWeight (1/2) k ≤ W(k)^{1/4} ≤ W(k)^{1/2}` (`W ≥ 1`), and even.
   `T11.torusMultiplierCLM 1 (1/2) …` packages it as a continuous **linear** map,
   which is what makes both continuity statements one-liners.
2. **Both continuity long poles come from datum paths already in the tree.**
   Force: `T10.force_coefficient_path hg 1` (lane 312) — continuous, compactly
   supported order-one datum path of `g` on **all** of `ℝ`.  Velocity:
   `w.sobolev 1` — `ContinuousOn` on `Ico 0 T`.  Composing with `critLower` and
   `homENorm_eq_enorm_of_datum` (lane 415) turns each into the continuity of the
   real profile, because the homogeneous datum is *unique* (the coefficient clause
   of `IsPeriodicHomogeneousDatum` is a pointwise formula), so the infimum in
   `periodicHomogeneousENorm` is attained at that one datum.
   **No new analysis was needed for the FTC**: `b` is continuous on `ℝ`, so
   `intervalIntegral.integral_hasDerivAt_right` gives `N' = b` at *every* real
   time and `N` is continuous by `continuous_iff_continuousAt`.
3. **The clamp.**  `Paper1.critical_norm_bound` wants `Continuous y` on all of
   `ℝ`, but T11 only gives `ContinuousOn … (Ico 0 T)`.  Fix: run the scalar lemma
   on `ŷ s = y (min (max s 0) t)` (`ContinuousOn.comp_continuous`), which equals
   `y` on `Icc 0 t` and, since `Ioo 0 t` is open, has the same derivative there
   (`HasDerivAt.congr_of_eventuallyEq` + `filter_upwards [isOpen_Ioo.mem_nhds hs]`).
4. **Two scalar passes, not one.**  `critical_norm_bound` concludes `y ≤ ρ`, which
   is the *weaker* half of `eq:ybound`.  The paper's `y(t) ≤ ∫₀ᵗ b` needs a second
   pass: with `y ≤ ρ < K = ν/(2C₀)` established on all of `[0,t]`, the absorption
   `critical_energy_absorption` + `critical_squared_derivative_bound` holds
   unconditionally there, and `Paper1.sqrt_energy_le_primitive` applies directly
   to give `√(ŷ²) ≤ N`.  Trying to get `y ≤ N` out of `critical_norm_bound` alone
   is impossible — its statement discards `N` in the last `.trans (hNbound t ht)`.

## Rejected / failed approaches

- **Re-deriving `continuous_bootstrap` with `ContinuousOn`.**  Considered first
  (the `IsCompact (Icc 0 T ∩ y⁻¹' {K})` step needs
  `ContinuousOn.preimage_isClosed_of_isClosed` instead of `isClosed_eq`).  Dropped:
  the clamp reuses the existing scalar lemmas verbatim and is ten lines.
- **`exact_mod_cast` / `simpa only [Nat.cast_one]` to move
  `IsPeriodicDatum ((1:ℕ):ℝ)` to `IsPeriodicDatum (1:ℝ)`.**  Both fail at this pin
  (`mod_cast has type IsPeriodicDatum (↑1) z A but is expected to have type
  IsPeriodicDatum 1 z A`; `norm_cast` does not descend into the order argument of
  a predicate).  What works: `have hcast : ((1:ℕ):ℝ) = 1 := Nat.cast_one` and
  `rw [hcast] at hdat`.
- **`eLpNorm_zero` (probe).**  `rw [… , eLpNorm_zero]` reports "did not find an
  occurrence of the pattern `eLpNorm 0 ?p ?μ`" even though the goal is literally
  `eLpNorm 0 1 forceTimeMeasure ≤ 0` — at this pin `eLpNorm_zero` is stated over
  the generic `ENorm` carrier `ε` and does not unify through the submodule's
  norm instance.  `simp` reduces `≤ 0` to `= 0` and then stalls for the same
  reason.  `eLpNorm_zero'` (the `fun _ => 0` spelling) closes it.
- **`positivity` on `criticalTrilinearConst`.**  As in lanes 405/413, it cannot
  see through the opaque `def`; every positivity fact is an explicit
  `have hC := criticalTrilinearConst_pos` + `linarith`.
- **`ENNReal.zero_toReal`** does not exist at this pin; `(0 : ℝ≥0∞).toReal = 0`
  is closed by `rfl`.

## Constant

`criticalSmallness = 1/(8·criticalTrilinearConst)`.  The proof only needs
`c ≤ 1/(2·C₀)` (that is exactly `ρ < c·ν ≤ ν/(2C₀) = K`), which is why the
general form `yBound_of_le` carries that hypothesis; `1/(8·C₀)` is chosen so that
the structure's **strict** shrinking `c < 1/(4·C₀)` (`criticalSmallness_lt_quarter`)
also holds, since `1/(4·C₀)` itself would only give `≤`.
