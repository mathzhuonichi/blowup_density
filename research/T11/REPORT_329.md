# 329-T11 — U9d1b fractional heat smoothing (`σ = 3/2`), unconditional

## 1. Theorems / exact statements

All of the following are proved outright: no named input, no `def … : Prop`
packaging a goal, no `sorry`/`admit`/`axiom`/`native_decide`, no
`set_option maxHeartbeats`. Module `NSFormalization.Section3.T11`.

**The symbol bound with an explicit constant.**

```lean
def torusFracConst (ν T : ℝ) : ℝ := (ν * T + 3 / 4 * Real.exp (-1)) ^ (3 / 4 : ℝ)
def torusFracKernel (ν t : ℝ) : ℝ := (ν * t) ^ (-(3 / 4) : ℝ)
def torusFracSymbol (ν t : ℝ) (k : PeriodicFrequency) : ℝ :=
  periodicFrequencyWeight k ^ (3 / 4 : ℝ) * torusHeatSymbol ν t k

theorem torusFracSymbol_le {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t) (htT : t ≤ T)
    (k : PeriodicFrequency) :
    torusFracSymbol ν t k ≤ torusFracConst ν T * torusFracKernel ν t
```

i.e. `W(k)^{3/4} e^{-νt·4π²|k|²} ≤ (νT + (3/4)e^{-1})^{3/4} (νt)^{-3/4}` for every
lattice frequency and every `0 < t ≤ T`. The `1` in `W = 1 + 4π²|k|²` is paid for
by the summand `νT`; the summand `(3/4)e^{-1}` is the maximum of `y ↦ y e^{-4y/3}`,
whose `3/4`-power is the brief's `(3/4)^{3/4} e^{-3/4}`. That one-variable
maximization is proved separately and used in the probe:

```lean
theorem rpow_three_quarters_mul_exp_neg_le {y : ℝ} (hy : 0 ≤ y) :
    y ^ (3 / 4 : ℝ) * Real.exp (-y) ≤ (3 / 4 : ℝ) ^ (3 / 4 : ℝ) * Real.exp (-(3 / 4 : ℝ))
```

**The order-`(s+3/2)` datum, its compatibility and its estimate.**

```lean
def torusHeatSmoothingFrac (s : ℝ) {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t) (htT : t ≤ T)
    (A : PeriodicSobolev s) : PeriodicSobolev (s + 3 / 2)

theorem torusHeatSmoothingFrac_reweight (s : ℝ) {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (htT : t ≤ T) (A : PeriodicSobolev s) :
    IsPeriodicReweight s (s + 3 / 2) (torusHeat s hν.le ht.le A)
      (torusHeatSmoothingFrac s hν ht htT A)

theorem torusHeatSmoothingFrac_norm_le (s : ℝ) {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (htT : t ≤ T) (A : PeriodicSobolev s) :
    ‖torusHeatSmoothingFrac s hν ht htT A‖ ≤ torusFracConst ν T * torusFracKernel ν t * ‖A‖
```

The compatibility is the canonical `IsPeriodicReweight` of
`Section3/T10/PeriodicData.lean` applied **to the heat image** `torusHeat s … A`
with ratio `W(k)^{((s+3/2)-s)/2} = W(k)^{3/4}` — not an index erasure on the same
weighted sequence (the defect `REPORT_319.md` flags). Also proved:
`torusHeatSmoothingFrac_apply` (coefficient identity, `rfl`),
`torusHeatSmoothingFrac_solenoidal` (incompressibility is preserved),
`torusFracSymbol_nonneg`, `torusFracSymbol_neg` (evenness, hence the real
conjugate-reflection subspace is preserved), `torusFracSymbol_zero`
(`torusFracSymbol ν t 0 = 1`), `torusFracSymbol_sub` (semigroup splitting).

**The bounded linear realization.**

```lean
def torusHeatSmoothingCLM_frac (s : ℝ) {ν T : ℝ} (hν : 0 < ν) (t : ℝ) (ht : 0 < t)
    (htT : t ≤ T) : PeriodicSobolev s →L[ℝ] PeriodicSobolev (s + 3 / 2)

theorem torusHeatSmoothingCLM_frac_opNorm_le (s : ℝ) {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (htT : t ≤ T) :
    ‖torusHeatSmoothingCLM_frac s hν t ht htT‖ ≤ torusFracConst ν T * torusFracKernel ν t
```

with `torusHeatSmoothingCLM_frac_eq` / `_apply` / `_norm_le` tying it to the datum
construction by `rfl`.

**The endpoint kernel.**

```lean
theorem torusFracKernel_integrableOn {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    IntegrableOn (fun τ : ℝ => torusFracKernel ν τ) (Ioc 0 t) volume

theorem torusFracKernel_intervalIntegrable {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    IntervalIntegrable (fun τ : ℝ => torusFracKernel ν (t - τ)) volume 0 t

theorem torusFracKernel_integral {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    (∫ τ in (0 : ℝ)..t, torusFracKernel ν (t - τ)) = 4 * t ^ (1 / 4 : ℝ) * ν ^ (-(3 / 4) : ℝ)
```

**Strong continuity on `Ioc 0 T`.**

```lean
theorem torusFracPath_continuousOn (s : ℝ) {ν T : ℝ} (hν : 0 < ν) (A : PeriodicSobolev s) :
    ContinuousOn (torusFracPath s hν T A) (Ioc 0 T)

theorem torusHeatSmoothingCLM_frac_continuousOn (s : ℝ) {ν T : ℝ} (hν : 0 < ν)
    (A : PeriodicSobolev s) {u : ℝ → PeriodicSobolev (s + 3 / 2)}
    (hu : ∀ t : ℝ, ∀ ht : 0 < t, ∀ htT : t ≤ T,
      u t = torusHeatSmoothingCLM_frac s hν t ht htT A) :
    ContinuousOn u (Ioc 0 T)
```

The second form is the consumer-facing one: any path agreeing with the CLM on the
window is continuous there, so nothing downstream must use `torusFracPath`
(a total `dite` extension of the window, `0` outside, needed only so that
`ContinuousOn` can be stated).

**Non-vacuity.** `torusHeatSmoothingFrac_constant` (the zero mode is fixed) plus a
module `example`: for `c i ≠ 0`, `torusHeatSmoothingFrac 3 … (torusConstantDatum 3 c) ≠ 0`.
The probe strengthens this to a genuine nonzero frequency: `singleMode 3 (1,0,0) c`
(the conjugate pair `{k₀, -k₀}`, the smallest datum of `realPeriodicSubmodule`
carrying `k₀ ≠ 0`) has image coefficient `torusFracSymbol ν t k₀ · c ≠ 0`.

## 2. Files

| path | content |
|---|---|
| `formalization/NSFormalization/Section3/T11/FractionalSmoothing.lean` | new module, 32 declarations (2 named local instances, 8 defs, 22 theorems) |
| `research/T11/probes/fractional_smoothing_closes.lean` | probe at `s = 3` on a single lattice mode; every target of the brief instantiated; own axiom audit |
| `research/T11/axioms_fractional_smoothing.lean` | `#guard_msgs`-guarded `#print axioms` for all 32 module declarations |
| `research/T11/ATTEMPTS_FRACTIONAL_SMOOTHING.md` | routes tried and rejected, exact error text, residuals |
| `research/T11/REPORT_329.md` | this report |
| `research/T11/T11_SPLIT.md` | one appended status line (append only) |

No existing module was modified. Imports: only
`NSFormalization.Section3.T11.Persistence` (which transitively brings
`LocalExistence`, `LocalExistenceProbe`, `T10.PeriodicData`, `PeriodicHeatMultiplier`).

## 3. Gaps

* **`TorusHalfStepInput` is not discharged.** This lane delivers the linear half
  only. The remaining obligation is the endpoint Duhamel argument on `Ico 0 T`
  plus a real-order bilinear bound `H^r × H^r → H^{r-1}`; lane 317's
  `torusScalarConvectionLp_norm_le` is stated at order 3 only. `Persistence.lean`
  says this in its own docstring ("a fractional multiplier estimate alone does not
  discharge it"); nothing here contradicts that, and **no new named input was
  introduced**.
* **No physical-field statement.** `torusHeatSmoothingFrac … A` is a coefficient
  object. It is the order-`(s+3/2)` reweighting of the heat image of `A`, i.e. a
  datum of `e^{νtΔ}z` rather than of `z`; recovering the physical field is U9d's
  Fourier-inversion problem (lane 318, partial).
* **The constant is an upper bound only.** `torusFracConst ν T = (νT + (3/4)e^{-1})^{3/4}`
  is not claimed sharp, and no lower bound is proved. It does degrade like
  `(νT)^{3/4}` for large `νT` — inherent to the inhomogeneous weight `1 + 4π²|k|²`
  on a window of length `T`, not an artefact of the proof.
* **The kernel mass is not yet wired to a contract field.** `torusFracKernel_integral`
  and `torusFracKernel_intervalIntegrable` are stated in the shape
  `EndpointSafeTwoSpaceDuhamel.lean:429-438` wants, but no `TorusTwoSpaceContract`
  instance at gain `3/2` is built here.
* No error text remains: both new Lean files compile with zero errors and zero
  warnings. Errors encountered during development, and their fixes, are in
  `ATTEMPTS_FRACTIONAL_SMOOTHING.md` §3.

## 4. Commands and results

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.FractionalSmoothing
  → ✔ [9974/9974] Built NSFormalization.Section3.T11.FractionalSmoothing (6.6s)
    Build completed successfully (9974 jobs).   [0 errors; the only warnings are
    pre-existing ones in Paper1/PeriodicLocalLifespan.lean]

cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/FractionalSmoothing.lean
  → no output (0 errors, 0 warnings)

cd verification && lake env lean ../research/T11/probes/fractional_smoothing_closes.lean
  → no output (0 errors, 0 warnings; all 7 embedded #guard_msgs axiom checks pass)

cd verification && lake env lean ../research/T11/axioms_fractional_smoothing.lean
  → no output: all 32 declarations print exactly
    [propext, Classical.choice, Quot.sound]

make check   (from the worktree root)
  → contract/architecture checks OK; test_contract_policy 13/13 OK;
    check_work_queue: "45 work items: ownership, contract registration and task
    cards consistent."
```
