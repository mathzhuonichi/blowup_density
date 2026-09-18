# REPORT_406 — T22 U-A3b verbatim `cutoffMultiplier` (Opus; transcribed by lead from the agent message, report-file guard)

Lane 406 is complete — the verbatim field is closed. Report follows (the brief's fallback: no `REPORT_406.md` file, full report here).

## 1. What was proved

`BoundedDomainNormAPI.cutoffMultiplier` **verbatim**, for every real `s`:

```lean
theorem cutoffMultiplier : ∀ (s : ℝ) (χ : Space → ℝ),
    ContDiff ℝ ∞ χ → HasCompactSupport χ →
    ∃ C : ℝ, 0 < C ∧ ∀ A : RealVectorSobolev s,
      ∃ B : RealVectorSobolev s,
        IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ
```

All four residuals R1–R4 closed. No `sorry`/`admit`/`axiom`/`native_decide`, no named inputs, no `maxHeartbeats`, no edits to existing Lean modules.

**R1 did not need what lane 397 thought it needed.** Two corrections to `ATTEMPTS_UA3.md`:

- The `L²`/tempered-level product↔convolution identity is **never used and was not proved**. R1 closes at the *Schwartz* level (`fourier_mul_eq_scalarConvolution`, `angularFourier_mul`) and is transported to all `L²` data by `LinearMap.extendOfNorm` along the dense range of `angularDatumL s`. The **graph conjunct needs no convolution at all** — only `angularRealization_datum` plus a one-`ext` compatibility lemma `smulLeftCLM_schwartz`; convolution enters only the *norm* conjunct.
- The R1 formula in `ATTEMPTS_UA3.md` is **wrong by the angular amplitude**. The correct normalization is `angularFourier (u·v) = frequencyUnit^(-3/2) • (angularFourier u ∗ angularFourier v)` — the `c³` Jacobian of `y = c z` cancels only two of the three `c^{-3/2}` amplitudes. As literally written (no factor), R1 is false unless `frequencyUnit = 1`. Lane 406 absorbs it into the constant: `cutoffFieldConst s χ = frequencyUnit^(-3/2) * cutoffMultiplierConst s χ + 1`.

Mathlib's forward theorem was enough: `SchwartzMap.convolution B f g` is *defined* as `𝓕⁻(pairing B (𝓕f) (𝓕g))`, so running it on `𝓕⁻u, 𝓕⁻v` with `fourier_fourierInv_eq` gives `𝓕⁻(u·v) = 𝓕⁻u ∗ 𝓕⁻v`, and `Real.fourierInv_eq_fourier_neg` + `integral_neg_eq_self` flip it to `𝓕`.

**R3 — the Mathlib lemma the coordinator asked me to cite:** `PiLp.norm_eq_of_L2 : ‖x‖ = √(∑ i, ‖x i‖ ^ 2)` (`Mathlib/Analysis/Normed/Lp/PiLp.lean:779`; siblings `PiLp.norm_sq_eq_of_L2:791`, `PiLp.nnnorm_eq_of_L2:785`, `EuclideanSpace.norm_eq`), used twice, with `ofReal_norm` and `ENNReal.ofReal_mul`. No separate "datum-norm ↔ eLpNorm" lemma was needed — the datum *is* an `Lp` element. `REPORT_397.md` now carries a dated correction of the "none of R1–R4 has an in-tree proof" claim.

## 2. What exists in Lean now

`/data_8T/ping/blowup_density/.claude/worktrees/406-T22-UA3b-cutoff-multiplier-field/formalization/NSFormalization/Section3/T22/CutoffMultiplierField.lean` (368 lines, 18 declarations, all `[propext, Classical.choice, Quot.sound]`): `fourier_mul_eq_scalarConvolution`, `angularFourier_mul`, `angularDatumL`/`denseRange_angularDatumL`/`angularDatum_ae`, `cutoffFieldConst(_pos)`, `norm_angularDatum_smulLeft_le`, `cutoffOperator`/`cutoffOperator_datum`/`norm_cutoffOperator_le`, `smulLeftCLM_schwartz`, `angularRealization_cutoffOperator`, `realSymmetry_angularDatum`/`realSymmetry_cutoffOperator`/`cutoffOperator_mem_realSubspace`, `cutoffMultiplier`.

Other files (all absolute paths under the same worktree root):
- `research/T22/probes/cutoff_multiplier_field_closes.lean` — field type matched by `exact` in both directions, plus non-vacuity: `ContDiffBump` cutoff with `χ 0 = 1`, concrete **nonzero** datum (three copies of the angular datum of the real complexified bump), with `‖A‖ₑ ≠ 0` and `‖A‖ₑ < ⊤`.
- `research/T22/probes/rev397_field_target_406.lean` — the 397 reviewer's REJECT-criterion probe reproduced with the one extra import; it now closes. The original `rev397_field_target.lean` is untouched as the review record.
- `research/T22/axioms_ua3b.lean` — 17 `#print axioms`, all standard.
- `research/T22/ATTEMPTS_UA3B.md` — positives, the two R1 corrections, and every failed approach.
- `research/T22/T22_SPLIT.md` — U-A3 status `DONE — lane 406` (U-Z1 may now consume the field); U-A5 sentence corrected: `LocalizationBoundary`'s `domainL2Sq_le_whole:64` / `domainL2Sq_eq_whole_of_compl_eq_zero:73` carry **no `s` premise** (verified by reading them — pure `∫‖·‖²` set-integral facts); what they lack is an `∫‖·‖² ↔ eLpNorm` bridge at `p=2`, not a range of `s`. The "`0<s<1` only" label belongs to that module's Gagliardo near/far split.
- `logs/LESSONS.md` — one new top line (pin-specific: the `SchwartzMap.convolution` definitional trick, the dense-extension shortcut, the `c^{-3/2}` amplitude, `PiLp.norm_eq_of_L2` exists).

Branch `erenup/406-T22-UA3b-cutoff-multiplier-field`, 3 commits (`57d3a43b`, merge `a9a91209` of `origin/erenup/397-T22-UA3-cutoff-multiplier`, `d9177b70`). Not pushed, not rebased. The 397 review record and its probes are merged in, so this branch supersedes 397 for the PR.

## 3. Gaps

None for the field itself. Two things a future lane may still want, neither blocking:

- The **`L²`-level product↔convolution identity** (`ATTEMPTS_UA3.md` R1 as literally stated, with the missing `frequencyUnit^(-3/2)`) remains unproved in the tree. It is not needed by `cutoffMultiplier`; anyone wanting a closed-form `b i` for a general `L²` datum still owes it.
- `cutoffFieldConst` is not sharp: the `+1` shift is there only to make `C > 0` at `χ = 0`.

Failed approaches, all recorded in `ATTEMPTS_UA3B.md` with the error text: `rw [integral_neg_eq_self]` fails on a beta-redex integrand (needs `exact integral_neg_eq_self _ volume`); `rw [cutoffOperator_datum]` leaves `unsolved goals / case hχ` once `cutoffOperator` no longer takes `hχ hc` (pass them explicitly); `nlinarith` fails on `a·n ≤ (a+1)·n` after `unfold cutoffFieldConst` re-introduces the spelling `set` had abstracted (rewrite with `← hdd` first); `angularRealization_datum` fails to rewrite under the `denseRange_angularDatumL` induction because the point is presented as `angularDatumL s φ` (`simp only [angularDatumL_apply]` first); `SchwartzMap.injective_toLp` needs an explicit `show psi.toLp 2 volume = (0 : 𝓢).toLp 2 volume`.

## 4. Commands run and results

From the worktree, `. scripts/lean-env.sh`, `lake` from `verification/` with `LEAN_NUM_THREADS=6`:

- `lake build NSFormalization.Section3.T22.CutoffMultiplierField` → `✔ Built … (3.2s)` / `Build completed successfully (9877 jobs).`, 0 errors.
- `lake env lean ../formalization/NSFormalization/Section3/T22/CutoffMultiplierField.lean` → no output.
- `lake env lean ../research/T22/probes/cutoff_multiplier_field_closes.lean` → no output.
- `lake env lean ../research/T22/probes/rev397_field_target_406.lean` → no output.
- `lake env lean ../research/T22/axioms_ua3b.lean` → 17/17 `depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `make check` → `OK` (13 policy tests) + `45 work items: ownership, contract registration and task cards consistent.`
- `make test` → 44 contracts `checked; standard logical axioms only`.
- `git fetch origin && git merge --no-edit origin/erenup/397-T22-UA3-cutoff-multiplier` → `Merge made by the 'ort' strategy`, 4 files added, no conflicts; full rebuild after the merge still green.
