# REPORT_401 — T12 U4b verbatim `velocityCriticalL3` by torus density (Opus; transcribed by lead from the agent message, report-file guard)

Lane 401 is complete. Full report below (I did not create `research/T12/REPORT_401.md` — report-file guard).

---

# Lane 401 — T12 U4b: the verbatim `velocityCriticalL3` by torus density

Commit `90f8fa88` on branch `erenup/401-T12-U4b-critical-l3-density`. No push, no merge, no rebase. No `sorry`/`admit`/`axiom`/`native_decide`, no `set_option` at all, no named input, no placeholder.

## 1. What was proved (exact statement)

The **verbatim API field** — not a weakened or repackaged form:

```lean
theorem velocityCriticalL3 (v : SpatialField) (hv : MemPeriodicHomogeneous (1 / 2) v) :
    periodicLpENorm 3 v ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v
```

Identical in binder order, hypothesis and both sides to `api_on_canonical.lean:148-151`, with the **same constant** `CcriticalHalf = criticalL3Const * cutoffGagliardoConst * (gapConst (1/2) + 1)` as lane 396's smooth theorem. The probe closes the `∀`-shape by `exact velocityCriticalL3`.

Route: `T12_SPLIT.md` U4 option **(A)**, symmetric Fourier truncation. (Option (B), mollification, was not needed — the truncation multiplier is the indicator of a symmetric box, which is exactly the `SpectralGap.reweightDatum` shape already in the tree, whereas a periodic mollifier would have required constructing `φ_ε` and computing `φ̂_ε` from scratch.)

The proof does **not** use the finiteness conjunct of `MemPeriodicHomogeneous`: only `MemLp (torusLift v) 2` and `IsMeanZeroT v` enter; when the right-hand side is `⊤` the chain is still valid.

## 2. What exists in Lean now

All paths absolute.

- `/data_8T/ping/blowup_density/.claude/worktrees/401-T12-U4b-critical-l3-density/formalization/NSFormalization/Section3/T12/CriticalL3Density.lean` — 560 lines, 23 public + 9 private declarations, builds with 0 errors / 0 warnings. Public API:
  - `torusLift_finitePeriodicFourierSum`, `periodicFourierCoeff_finitePeriodicFourierSum` (orthogonality of the torus monomials, via the existing `T10.integral_mFourier`);
  - `periodicCharacter_neg`, `conj_finitePeriodicFourierSum_real` — a partial Fourier sum of a **real** field over a negation-closed frequency set is real (uses `T10.periodicFourierCoeff_real_neg`), so the componentwise `.re` in the definition below does **not** truncate the data;
  - `truncField v S`, `truncField_apply`, `ofReal_truncField_apply`, `periodicFourierCoeff_truncField` (the datum of the truncation is **exactly** the restriction of the datum of `v`), `isPeriodicSpatial_truncField`, `contDiff_truncField`, `smoothPeriodicT_truncField`;
  - `freqBox N`, `mem_freqBox`, `freqBox_neg_closed`, `freqBox_mono`, `exists_freqBox_superset`, `tendsto_freqBox` (cofinality in the finite subsets of `ℤ³`);
  - `integrable_torusLift_truncField`, `isMeanZeroT_truncField`;
  - `periodicHomogeneousENorm_truncField_le` (at **every** order `s`: `‖truncField v S‖_{Ḣ^s} ≤ ‖v‖_{Ḣ^s}`, by the indicator `reweightDatum`);
  - `tendsto_eLpNorm_truncField_sub` (`L²(T³)` convergence of the truncations, from Mathlib's `UnitAddTorus.hasSum_mFourier_series_L2` for the Hilbert basis `mFourierBasis`);
  - `memPeriodicHomogeneous_of_smooth` (new, general order `s ≥ 0`: smooth + mean-zero + periodic ⇒ finite homogeneous datum — the tree had only the order-`1` case `T10.smooth_homogeneous_datum_one` at `T10/ForcePaths.lean:280`);
  - `velocityCriticalL3`.
- `/data_8T/ping/blowup_density/.claude/worktrees/401-T12-U4b-critical-l3-density/research/T12/probes/critical_l3_density_closes.lean` — closes the canonical API shape by `exact`, records the machinery, and instantiates hypothesis **and** conclusion on the nonzero smooth mean-zero witness `densityProbeMZ = meanZeroPartT (x ↦ cos(2π x₀)·e₀)` whose `MemPeriodicHomogeneous (1/2)` membership comes from `memPeriodicHomogeneous_of_smooth`. Nothing vacuous.
- `/data_8T/ping/blowup_density/.claude/worktrees/401-T12-U4b-critical-l3-density/research/T12/axioms_u4b.lean` — all 23 public declarations print exactly `[propext, Classical.choice, Quot.sound]`.
- `/data_8T/ping/blowup_density/.claude/worktrees/401-T12-U4b-critical-l3-density/research/T12/ATTEMPTS_U4B.md`, U4b status block in `research/T12/T12_SPLIT.md`, one line at the top of `logs/LESSONS.md`.

Reuse: `Paper1.finitePeriodicFourierSum` / `periodicCharacter` (+`_smooth`, `_periodic`, `_eq_mFourier`), `T10.integral_mFourier`, `T10.periodicFourierCoeff_real_neg`, `T10.periodicFourierCoeff_zero_eq_mean_component`, `T10.fourier_repr_toLp`, `T10.memLp_torusLift_component/_vector`, `T10.smooth_periodic_datum`, `T12.SpectralGap.reweightDatum(_real/_norm_le)`, `T12.homogeneousDatumWeight_le_periodicFrequencyWeight_rpow`, `T12.one_le_fourierWeight`/`fourierWeight_neg`, `T12.velocityCriticalL3_smooth`, and Mathlib's `UnitAddTorus.*`, `Lp.tendsto_Lp_iff_tendsto_eLpNorm'`, `tendstoInMeasure_of_tendsto_eLpNorm`, `TendstoInMeasure.exists_seq_tendsto_ae`, `Lp.eLpNorm_lim_le_liminf_eLpNorm`.

## 3. Gaps

**None for U4.** The residual recorded in `research/T12/ATTEMPTS_U4.md` is closed; U4 now delivers the verbatim field, so no error text to report.

Two honest scope notes (not gaps in the delivered theorem):

- `memPeriodicHomogeneous_of_smooth` exists only because the tree lacked a general-order smooth homogeneous datum; it is used **only** by the probe for non-vacuity, never by `velocityCriticalL3` itself.
- Approaches that do **not** work here, recorded so they are not retried: the uniform-reconstruction line (`Paper1.hasSum_periodicFourier_physical`, `tendsto_periodicFourier_partialSums`, `PeriodicH2Uniform`) needs `Summable (periodicFourierCoeff f)`, and Cauchy–Schwarz against `Ḣ^{1/2}` would require `∑_{k≠0}|2πk|^{-1} < ∞` on `ℤ³`, which **diverges** (the exponent must exceed 3). So absolute convergence is unavailable at the critical index and the `mFourierBasis` `L²` route plus an a.e. subsequence is the only one. Also, taking `.re` over a non-symmetric frequency set symmetrises the coefficients, so `periodicFourierCoeff_truncField` would be false — every `truncField` statement carries `hS : ∀ k ∈ S, -k ∈ S`.

Pin-specific pitfalls hit (all now in `ATTEMPTS_U4B.md` and `logs/LESSONS.md`):
- `Finset.sum_image` is `{g : κ → ι} : Set.InjOn g ↑s → ∑ x ∈ s.image g, f x = ∑ x ∈ s, f (g x)` — summand is `f`, map is `g`, injectivity is `Set.InjOn`; higher-order unification of `f` fails on `∑ k ∈ S, χ_{-k} x * c (-k)`, so **both** `(f := …)` and `(g := …)` must be supplied. Errors seen: `Type mismatch … ?m.224 (-x)` and then `periodicCharacter k x * c k has type ℂ but is expected to have type PeriodicFrequency`.
- `zero_le` in `ℝ≥0∞` takes no explicit argument: `zero_le _` gives `error: Function expected at zero_le`.
- `-m + k = 0 → k = m` is `neg_add_eq_zero` (`linarith` fails on `Fin 3 → ℤ`: `linarith failed to find a contradiction`).
- `integral_finset_sum` / `tendsto_finset_sum` are deprecated → `integral_finsetSum` / `tendsto_finsetSum`.
- `Lp ℂ 2 periodicTorusMeasure` unifies with Mathlib's `L²(UnitAddTorus (Fin 3))` only because `Paper1.periodicTorusMeasure` is an `abbrev` for `volume` under the same `local instance : MeasureSpace UnitAddCircle`; precedent `T10/Parseval.lean`.

## 4. Commands run and results

All from `/data_8T/ping/blowup_density/.claude/worktrees/401-T12-U4b-critical-l3-density`, after `. scripts/lean-env.sh`, `lake` from `verification/`, `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T12.CriticalL3Density` → `✔ [10044/10044] Built NSFormalization.Section3.T12.CriticalL3Density (3.1s)`, `Build completed successfully (10044 jobs).` — 0 errors. (The `⚠` lines in the log are pre-existing replayed warnings from unrelated `Paper1`/`Source` modules.)
- `lake env lean ../formalization/NSFormalization/Section3/T12/CriticalL3Density.lean` → **empty output** (0 errors, 0 warnings).
- `lake env lean ../research/T12/probes/critical_l3_density_closes.lean` → **empty output** (every `example` closes).
- `lake env lean ../research/T12/axioms_u4b.lean` → 23 lines, each `depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `make check` → `Ran 13 tests … OK`; `45 work items: ownership, contract registration and task cards consistent.`
- `make test` → completed through `Tests.CompletedDensity`: `Contract BlowupDensity.Tests.checkedCompletedDensity: checked; standard logical axioms only` (all registered contracts still green).
- `grep -n "sorry\|admit\|axiom\|native_decide\|maxHeartbeats"` on the module and the probe → no hits.
- `git commit` → `90f8fa88`, 6 files, +890 lines. Nothing pushed.
