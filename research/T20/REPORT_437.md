# REPORT_437 — T20 U11 continuationBound (Opus; transcribed by lead from the agent message, report-file guard)

Lane 437 is complete. U11 closed with no residual.

## 1. What was proved

`eq:criterion` / the continuation paragraph of `prop:critical` (`paper/sections/03-torus.tex:486-500`) — as the `continuationBound` field of `CriticalRegularityTAPI` **verbatim**:

```lean
theorem continuationBound : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (criticalSmallnessH1 * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ (S : ℝ), 0 < S → S ≤ T →
            squaredHTwoIntegralT S w.velocity =
                meanModeCriterionIntegral S g w.velocity ∧
              meanModeCriterionIntegral S g w.velocity ≤
                ENNReal.ofReal S * criticalRho g ^ (2 : ℝ) +
                  ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2) *
                    meanFreeForceLTwoSqIntegral (meanFreeForce g) ∧
              ENNReal.ofReal S * criticalRho g ^ (2 : ℝ) +
                  ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2) *
                    meanFreeForceLTwoSqIntegral (meanFreeForce g) ≠ ⊤
```

**The constant.** `def Ccriterion : ℝ := hTwoConst ^ 2 * CH1`, i.e. `(1 + 1/(4π²))² · 2` — checked by `rfl` in the probe — with `Ccriterion_pos` (the structure's `hCcriterion`). `hTwoConst` is T12's mean-zero `H²`/Laplacian comparison constant, `CH1 = 2` is lane 432's `eq:H1energy` constant. The smallness radius `c` is unchanged from lane 432: `criticalSmallnessH1`, so U13 needs no further shrinking.

No named input, no placeholder, no goal repackaging, no `maxHeartbeats` override, no edits to any existing module. All 27 declarations print exactly `[propext, Classical.choice, Quot.sound]`.

**Three findings worth the lead's attention.**

- **The one genuinely new torus ingredient is short.** The orthogonal decomposition `‖u(t)‖²_{H²} = |m(t)|² + ‖v(t)‖²_{H²}` follows because removing the spatial mean deletes exactly the `k = 0` coefficient and the order-2 Bessel weight there is `1`; T11's `hasSum_freqEnergyT` then makes both sides the same `HasSum`. ~90 lines including the coefficient lemmas.
- **The expected long pole (integrating `eq:H1energy`) is cheap if you reorder the steps.** Applying T12 `hTwo_le_laplacian` *before* integrating turns U10b into `(‖∇v‖²₂)' + (ν/hTwoConst²)‖v‖²_{H²} ≤ CH1·ν⁻¹‖h‖²₂`, so only the `H²` profile needs integrability — and that profile is continuous for free from the decomposition plus T11's `continuousOn_torusSobolevNormAt_velocity`. There is **no** continuity statement for `t ↦ ‖Δv(t)‖²₂` anywhere in the tree and none had to be proved. Both endpoints are also cheaper than expected: `‖∇v(a)‖²₂ → 0` by the termwise squeeze `|2πk|² ≤ 1+|2πk|²` against `‖u(a)‖²_{H¹}` (which vanishes at `t = 0` by `w.initial`), and the open right endpoint `S = T` by `MeasureTheory.setLIntegral_iUnion_of_directed`, which carries **no measurability hypothesis on the integrand**.
- **U11 does not depend on U3 (`bIntegral`) or U6 (`meanFreeEquation`).** The real dependency set is U2 (`meanBound`, `reductionRegular`), U10b, T12 `hTwo_le_laplacian`, and the `w.sobolev` datum path of `ClassicalSolutionT`. Also `MemForceT (meanFreeForce g)` turns out to be true and easy, so lane 312's `force_coefficient_path` applies to `h` directly at order 0 and the force `L²` budget (`∫₀^∞‖h‖²₂ ≠ ⊤`) is ten lines — no new `L²` analysis.

## 2. What exists in Lean now

- `/data_8T/ping/blowup_density/.claude/worktrees/437-T20-U11-continuation-bound/formalization/NSFormalization/Section3/T20/Continuation.lean` (823 lines, 27 declarations). Reusable beyond U11, and U12/U13 will want several: `memForceT_meanFreeForce` (the mean-free force is itself a test force), `torusSobolevNormAt_two_sq_split` and its `ℝ≥0∞` form `sobolevENorm_two_sq_split`, `coeff_meanZeroPart`, `continuousOn_meanFreeHTwoSq`, `meanFreeHTwoSq_integral_le` (the `H²` budget on every `(0,b)`), `meanFreeForceLTwoSqIntegral_eq` / `_ne_top`, `zero_isPeriodicDatum`, `torusSobolevNormAt_initial`, `contDiff_meanPathT`, `enorm_rpow_two`, `Ccriterion` / `Ccriterion_pos`.
- `/data_8T/ping/blowup_density/.claude/worktrees/437-T20-U11-continuation-bound/research/T20/probes/continuation_closes.lean` — checks `example (API : CriticalRegularityTAPI) : continuationBoundFieldType API.c API.Ccriterion := API.continuationBound` (so the spelling is the structure field, not a paraphrase), `example : continuationBoundFieldType criticalSmallnessH1 Ccriterion := continuationBound`, `Ccriterion = (1 + 1/(4*Real.pi^2))^2 * 2` by `rfl`, `Ccriterion_pos`, and non-vacuity at lanes 415/428/432's zero-force zero-solution instance (`ν = 1`, `T = 1`, `S = 1`) including a proof that the smallness hypothesis is satisfiable (`ρ = 0 < c·ν`), producing all three conjuncts.
- `/data_8T/ping/blowup_density/.claude/worktrees/437-T20-U11-continuation-bound/research/T20/axioms_u11.lean`, `/data_8T/ping/blowup_density/.claude/worktrees/437-T20-U11-continuation-bound/research/T20/ATTEMPTS_U11.md`, the U11 status block in `/data_8T/ping/blowup_density/.claude/worktrees/437-T20-U11-continuation-bound/research/T20/T20_SPLIT.md`, one line at the top of `/data_8T/ping/blowup_density/.claude/worktrees/437-T20-U11-continuation-bound/logs/LESSONS.md`.
- Committed as `6643f95f` on `erenup/437-T20-U11-continuation-bound`; working tree clean; nothing pushed, merged or rebased.

## 3. Gaps

**No mathematical gap** — the field is closed outright. Three notes for the lead:

- Non-vacuity is again the zero force with the zero solution (lanes 415/428/432's sanctioned fallback). A nonzero-force instance still needs a compactly time-supported bump in `forceClassT` plus T11 local existence; neither is assembled anywhere in the tree.
- U12 consumes this as written: conjuncts 1+2+3 give `squaredHTwoIntegralT S w.velocity ≠ ⊤` for every `0 < S ≤ T`, which is the input of T11's `lifespanInfiniteOfLocallyFinite`.
- The eleven failed approaches, each one compile round, are in `ATTEMPTS_U11.md` with exact error text. The four that cost the most: (a) `tsum_le_tsum` no longer exists at root — `error(lean.unknownIdentifier): Unknown identifier 'tsum_le_tsum'`; it is `Summable.tsum_le_tsum (hf) (h) (hg)`; (b) three `← ENNReal.ofReal_pow (norm_nonneg _)` in one `rw` list — the third fails with `Did not find an occurrence of the pattern ENNReal.ofReal ‖?m‖ ^ ?n in the target expression ENNReal.ofReal (‖A‖ ^ 2) = ENNReal.ofReal (‖meanPathT g t‖ ^ 2) + ENNReal.ofReal ‖B‖ ^ 2`, because the placeholder's normed space is pinned by the first rewrite and the three norms live in two spaces; split into separate `rw`s with explicit `norm_nonneg A` / `norm_nonneg B`; (c) `nlinarith` on the absorption step gave `linarith failed to find a contradiction` — the missing piece was the non-linear product `CH1·ν⁻¹·∫ₐᵇ‖h‖²₂ ≤ CH1·ν⁻¹·HFtot`, supplied by `mul_le_mul_of_nonneg_left`, after which plain `linarith` works; (d) `field_simp` needs `hTwoConst ≠ 0`, not `hTwoConst^2 ≠ 0`, or it stalls at `⊢ (hTwoConst * ∫ …) / hTwoConst = ∫ …`. Also this pin has deprecated `if_pos` / `if_neg` and `HasSubset.Subset.eventuallyLE`.

I did not write `research/T20/REPORT_437.md` — my standing instruction forbids writing report/summary `.md` files; the full report is this message, as the brief's fallback allows.

## 4. Commands run and results

All from `/data_8T/ping/blowup_density/.claude/worktrees/437-T20-U11-continuation-bound`, after `. scripts/lean-env.sh`, `lake` from `verification/` with `LEAN_NUM_THREADS=6`.

| Command | Result |
|---|---|
| `lake build NSFormalization.Section3.T20.H1Energy NSFormalization.Section3.T20.MeanReduction` | exit 0 — confirms the two inputs co-import and the closure is warm |
| `lake env lean ../research/T20/scratch/names437.lean` (name probe, deleted) | resolved everything except three namespace typos: `contDiff_galileanMeanT` is in `T11.Transport`, `squaredHTwoIntegralT` in `T11`, `sub_le_integral_of_hasDeriv_right_of_le` in `intervalIntegral` |
| `lake env lean` on `Continuation.lean`, attempt 1 (§1) | **failed**, 1 error: `Continuation.lean:182:36: Type mismatch … Eq.symm (freqEnergyT_two_split …)` (wrong `HasSum.congr_fun` direction) |
| attempt 2 (§2 added) | **failed**, 5 errors: two `ContinuousOn … ((fun t => …) ^ 2)` type mismatches from `simpa only [Nat.cast_ofNat]`, `simp made no progress`, `Unknown identifier 'tsum_le_tsum'`, `No goals to be solved` |
| attempt 3 (§3 added) | **0 errors first try** |
| attempt 4 (§4 added) | **failed**, 3 errors: `Application type mismatch: hx.left has type a < x`, `linarith failed to find a contradiction` (the absorption step), `rewrite failed: Did not find … ?m ≥ ?m'` |
| attempts 5–7 (§4 arithmetic) | two more `field_simp` stalls, fixed by `field_simp [hTwoConst_pos.ne']` |
| attempt 8 (§5 added) | **failed**, 2 errors: the triple `ENNReal.ofReal_pow` rewrite, and `No goals to be solved` from a `?dir` named hole inside `rw` |
| attempt 9 (final) | `lake env lean ../formalization/NSFormalization/Section3/T20/Continuation.lean` → exit 0, **0 bytes of output** |
| `lake build NSFormalization.Section3.T20.Continuation` | `Build completed successfully (10655 jobs)`, **0 errors**; only pre-existing upstream warnings replayed from `NSFormalization/Source/*`, `NSFormalization/Paper1/*`, `vendor/HeliCorgi/Formal/*` |
| `lake env lean ../research/T20/probes/continuation_closes.lean` | exit 0, **0 bytes of output** |
| `lake env lean ../research/T20/axioms_u11.lean` | exit 0; **27/27** records, the only distinct line being `depends on axioms: [propext, Classical.choice, Quot.sound]` |
| `grep -nE "sorry\|admit\|native_decide\|maxHeartbeats\|^axiom \|Prop :="` over the new module | one hit, the docstring line "No `sorry`, no `admit`, no `axiom`, …" |
| `make check` | exit 0 |
| `make test` | exit 0 |
| `git status --short` before commit | only the 4 new files plus `logs/LESSONS.md` and `research/T20/T20_SPLIT.md` — **no existing Lean module touched** |
| `git commit` | `6643f95f [437-T20] U11 continuationBound: orthogonal H² mode split + the H² time budget`; tree clean; no push/merge/rebase |


## Lead notes after review 437 (REJECT on procedure and records only; Lean and mutation checks passed)

1. **Absence claim narrowed.** "Laplacian-square continuity is nowhere in the tree" is too broad: `Section4/C01/EnstrophyBounds.lean:67` (`laplacianSq_continuousOn`) and `C01/JetPaths.lean:212` prove it on ℝ³ solution slabs. They are whole-space results and do not apply to the torus profile, so U11's reordering (apply `hTwo_le_laplacian` before integrating) stands; the claim is now "no *torus* continuity of `t ↦ ‖Δv(t)‖²₂` is in the tree and none was needed".
2. **Local theory and bump exist.** "Neither a compact-time force bump nor T11 local existence is assembled" is wrong: `Section3/T11/Assembly.lean:99` (`periodicLocalSolution`), `:182` (assembled API) and `:525` (`periodicLocalTheoryAPI_nonvacuous`, with an explicit bump and force membership at `:531`, `:555`) exist. That witness uses nonzero initial data and does not establish the U11 smallness hypothesis, so the lane's zero-force witness remains the appropriate non-vacuity instance; a nonzero-force small-datum instance is a separate (T20 U13) item.
3. **Line count** corrected to 823 (27 declarations, unchanged).
4. The base-aware gate failed only because the worktree predates #396 (`ConservativeForcing.lean`); the merge into integration below refreshes it, and the lane touches no `verification/` file.
