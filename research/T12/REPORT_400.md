# REPORT_400 — T12 U5 `gradientLSix` (Opus; transcribed by lead from the agent message, report-file guard)

Lane 400 is complete and committed. Report follows.

---

## 1. What was proved

The U5 target closed **verbatim**, no named input, no placeholder, no residual.

`/data_8T/ping/blowup_density/.claude/worktrees/400-T12-U5-gradient-l6/formalization/NSFormalization/Section3/T12/GradientLSix.lean:641`

```lean
theorem gradientLSix :
    ∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v →
      periodicLpENorm 6 (gradientTensor v) ≤
        ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian v)
```

This is character-for-character the `gradientLSix` field of `MeanZeroSobolevCalculusAPI` at `research/T12/probes/api_on_canonical.lean:184-187`, with the API data field `Csix` replaced by the module's explicit constant.

The constant (`:614`) and its positivity (`:617`):

```lean
def Csix : ℝ :=
  343 * NSFormalization.Section4.A05.gradientL6Const * leibnizConst * (1 + 2 * hTwoConst)

theorem Csix_pos : 0 < Csix
```

where `leibnizConst = 1 + 6 * cutoffGradBound + cutoffLapBound` (`:312`), `cutoffGradBound = Classical.choose exists_cutoff_fderiv_bound`, `cutoffLapBound = Classical.choose exists_cutoff_lap_bound` (a new existence lemma proved in the module for `Δχ`), `gradientL6Const` is the registered whole-space constant of `Section4/A05/GradientL6.lean:52`, and `hTwoConst = 1 + 1/(4π²)` from `FourierEmbeddings.lean:127`.

Route taken is exactly route (c) of the brief: Haar→cube (U1) → `∇(χv) = ∇v` on the cube (U2, χ ≡ 1 on `ball 0 (5/2) ⊇ [0,1]³`) → `Measure.restrict_le_self` → registered `A05.eLpNorm_gradTensor_six_le` on `χv` → Leibniz → lattice tiling with the lane-377 count `7³ = 343` → the two torus lower-order bounds.

## 2. What exists in Lean now

New module (699 lines, 52 declarations), all public, all audited:
`/data_8T/ping/blowup_density/.claude/worktrees/400-T12-U5-gradient-l6/formalization/NSFormalization/Section3/T12/GradientLSix.lean`

The load-bearing intermediate results, in dependency order:

- `periodicLpENorm_two_le_laplacian`, `periodicLpENorm_gradientTensor_le_laplacian` (`:101`, `:167`) — the two new torus estimates `‖v‖_{L²(T³)} ≤ hTwoConst·‖Δv‖_{L²}` and `‖∇v‖_{L²(T³)} ≤ hTwoConst·‖Δv‖_{L²}` for smooth mean-zero periodic `v`. Built from `SpectralGap.reweightDatum` with the real even multipliers `1/(1+4π²|k|²)` and `|2πk|/(1+4π²|k|²)`, `T10.parseval_forward`, `T10.gradient_eq_homogeneousENorm`, lane-377's `meanZeroPartT_eq_self`, and `FourierEmbeddings.hTwo_le_laplacian`.
- `dirDeriv_smul_eq`, `dirDeriv_add_eq`, `lap_cutoffMul_eq` (`:232`) — the Leibniz identity `Δ(χv) = χΔv + ∑ᵢ((∂ᵢχ)(∂ᵢv) + (∂ᵢχ)(∂ᵢv)) + (Δχ)v`.
- `smoothL2_cutoffMul` (`:273`) — `χv` satisfies the hypothesis of the registered whole-space theorem.
- `norm_lap_cutoffMul_le` (`:320`) — the pointwise majorant.
- `lap_cutoffMul_eq_zero` (`:417`) — `Δ(χv)` vanishes off `closedBall 0 3 = tsupport χ`.
- `lintegral_lap_cutoffMul_le`, `eLpNorm_lap_cutoffMul_le` (`:496`, `:533`) — the tiling step: `‖Δ(χv)‖_{L²(ℝ³)} ≤ 343·‖majorant‖_{L²(Q)}`.
- `gradTensor_cutoffMul_eqOn`, `eLpNorm_leibnizMajorant_le`, `ofReal_Csix`, `gradientLSix`.

Also new, generic and reusable: `contDiff_dirDeriv`, `hasCompactSupport_dirDeriv`, `contDiff_lap`, `hasCompactSupport_lap`, `eqOn_zero_dirDeriv`, `eqOn_zero_lap`, `isPeriodicSpatial_gradientTensor`, `norm_coordinateVector`, `tsupport_cutoff_eq`.

Supporting files (all absolute paths under the worktree root `/data_8T/ping/blowup_density/.claude/worktrees/400-T12-U5-gradient-l6`):
- `research/T12/probes/gradient_l6_closes.lean` — closes the API field by `exact gradientLSix`, closes `Csix_pos`, exhibits the six intermediate estimates, and instantiates the field on a nonzero smooth mean-zero periodic witness (`probeMZ`, the lane-377 single cosine mode made mean-free), so neither hypotheses nor conclusion are vacuous.
- `research/T12/axioms_u5.lean` — `#print axioms` for all 52 declarations.
- `research/T12/ATTEMPTS_U5.md` — positive and negative record.
- `research/T12/T12_SPLIT.md` — U5 status block marked COMPLETE.
- `logs/LESSONS.md` — one line of pin-specific pitfalls.

No existing module was edited. Commit `240b1d55` on branch `erenup/400-T12-U5-gradient-l6`; nothing pushed, merged or rebased.

## 3. Gaps

**No residual theorem** — the verbatim statement is closed. Two honest limitations:

1. **`Csix` is a closed term but not a numeral.** `leibnizConst` depends on `Classical.choose` of the sup bounds `‖∇χ‖_∞` and `‖Δχ‖_∞`; `Cutoff.lean` (lane 365) only exposes these as existentials (`exists_cutoff_fderiv_bound`), and Mathlib gives no explicit `C⁰/C²` bounds for `ContDiffBump`. `gradientL6Const` itself already contains Mathlib's irreducible `eLpNormLESNormFDerivOfEqInnerConst`, so this opacity is the accepted upstream state (`Section4/A05/GradientL6.lean:50-53`). Making it numeric is a separate (and probably unpleasant) unit.
2. **Non-triviality of the left side is not proved.** The probe shows the hypotheses are satisfied by a nonzero field; it does not prove `periodicLpENorm 6 (gradientTensor probeMZ) ≠ 0`. The API field does not require it, and no other T12 probe proves the analogue.

The constant is also lossy relative to the paper (`343` from the cube count, `6·‖∇χ‖_∞` from the three directions doubled, `1 + 2·hTwoConst` from the two lower-order terms); `appendix-b-embeddings.tex:109-110` leaves constants free, so this is within spec.

Rejected routes, recorded in `research/T12/ATTEMPTS_U5.md`: (a) the direct imaginary Fourier symbol `2πi kⱼ/(-4π²|k|²)` for `‖∂ⱼv‖_{L²(T³)}` — `SpectralGap.reweightDatum` accepts only a real even multiplier, so this needs a ~100-line complex re-proof of the carrier/norm/reality lemmas; sidestepped via `gradient_eq_homogeneousENorm`, where the multiplier `|2πk|` is real and even; (b) a Caccioppoli / whole-space integration-by-parts derivation of `‖∇v‖_{L²}`, abandoned because it yields a self-referential quadratic that has to be solved in `ℝ≥0∞`.

## 4. Commands run and results

All from the worktree, each shell sourcing `. scripts/lean-env.sh`, `lake` from `verification/` with `LEAN_NUM_THREADS=6`.

| command | result |
|---|---|
| `lake build NSFormalization.Section3.T12.HaarCube NSFormalization.Section3.T12.CutoffGagliardo NSFormalization.Section3.T12.FourierEmbeddings` | `Build completed successfully (9999 jobs).` (dependency warm-up) |
| `lake build NSFormalization.Section3.T12.GradientLSix` | `✔ [10000/10000] Built NSFormalization.Section3.T12.GradientLSix (3.4s)` / `Build completed successfully (10000 jobs).` — 0 errors |
| `lake env lean ../formalization/NSFormalization/Section3/T12/GradientLSix.lean` | **no output** (0 errors, 0 warnings) |
| `lake env lean ../research/T12/probes/gradient_l6_closes.lean` | **no output** |
| `lake env lean ../research/T12/axioms_u5.lean` | 52 lines, each `depends on axioms: [propext, Classical.choice, Quot.sound]`; 52/52 match exactly, nothing else printed |
| `grep -nE "sorry\|admit\|axiom\|native_decide\|maxHeartbeats"` on the module and probe | only the docstring sentence "No `sorry`, no `axiom`, …"; no tokens |
| `make check` | `exit=0` (`check_formalization_plan.py`, `check_contracts.py`, `test_contract_policy.py` 13 tests OK, `check_work_queue.py` "45 work items … consistent") |
| `git commit` | `240b1d55 [400-T12] U5: gradientLSix verbatim on T³ (route (c), no named input)`; working tree clean |

Failed intermediate attempts (all fixed, full list in `ATTEMPTS_U5.md`), with the exact errors:
- `HasCompactSupport.sum` → `error(lean.unknownIdentifier): Unknown constant`; replaced by `Fin.sum_univ_three` + `HasCompactSupport.add`.
- `rw [fderiv_smul …]` on `fderiv ℝ (fun y => c y • w y) x` → `Tactic `rewrite` failed: Did not find an occurrence of the pattern fderiv ℝ (c • w) x`; fixed with a `show` into the Pi-operation form (same for `fderiv_add`).
- `abel` on `(A+B)+(B+C) = A+(B+B)+C` with `B` an `ℝ`-smul → `unsolved goals … 2 • dirDeriv i cutoff x • dirDeriv i v x`; fixed with `simp only [add_assoc]`.
- `eLpNorm_const_smul_le _ _` → `Function expected at eLpNorm_const_smul_le`; the lemma takes no explicit arguments and will not unify `leibnizMajorant v` with `?c • ?f`, so a `rfl`-rewrite was inserted first.
- `simp only [… Real.sqrt_eq_rpow]` left `(periodicAngularFrequencySq k).rpow (1/2) = periodicAngularFrequencySq k ^ (1/2)`; closed by `rfl`.
- `positivity` → `failed to prove positivity/nonnegativity/nonzeroness` on `0 ≤ 2 * hTwoConst` and on `0 ≤ homogeneousDatumWeight 1 k / periodicFrequencyWeight k`; fixed with `linarith` / `div_nonneg` after bringing `hTwoConst_pos` / `fourierWeight_pos` into context.

One deviation from the brief: it asked me to try writing `research/T12/REPORT_400.md`. My operating instructions forbid writing report/summary `.md` files, so I did not create it — the brief's stated fallback applies and the full report is this message. The negative-results ledger (`ATTEMPTS_U5.md`), the `T12_SPLIT.md` status block and the `LESSONS.md` line were all written as required.
