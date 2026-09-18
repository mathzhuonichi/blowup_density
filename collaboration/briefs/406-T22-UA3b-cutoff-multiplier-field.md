# Lane 406-T22-UA3b-cutoff-multiplier-field — T22 U-A3b: close the verbatim `cutoffMultiplier` field on top of lane 397's engine (residuals R1–R4)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/406-T22-UA3b-cutoff-multiplier-field` (git branch `erenup/406-T22-UA3b-cutoff-multiplier-field`, based on lane 397's branch merged
with `origin/erenup/integration-section3`; it contains `Section3/T22/CutoffMultiplier.lean` — `besselW`, `besselW_peetre`, the engine `eLpNorm_besselWeight_scalarConvolution_le`
and its cutoff specialization `eLpNorm_cutoff_multiplier_le` with `cutoffMultiplierConst s χ` — plus `Section3/T22/{Domain,RestrictBridge,WeightRatio,OrderZeroIsometry,CutoffKernel,OrderZero}.lean`).
Read `CLAUDE.md`, **`research/T22/ATTEMPTS_UA3.md` §"Why the verbatim field is NOT closed" (R1–R4 with exact statements)**, `research/T22/REPORT_397.md`, `research/T22/T22_SPLIT.md`
§0 and unit U-A3, the canonical field `Section3/T22/Domain.lean` (`BoundedDomainNormAPI.cutoffMultiplier`, `IsCutoffDatum`, `angularRealization`, `RealVectorSobolev`),
`Section3/T22/OrderZero.lean` (lane 393: `orderZeroDatum_surjective`, `conjugation_fourierInv_of_mem` — the realSubspace/reality pattern you need for R2),
`Section3/T22/CutoffKernel.lean` (lane 391: `cutoffSchwartz`), `Section4/R44/TrilinearJ.lean:181` (analogous half-order reality fact), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T22/CutoffMultiplierField.lean` (namespace `NSFormalization.Section3.T22`): `theorem cutoffMultiplier` whose type is literally the
canonical `BoundedDomainNormAPI.cutoffMultiplier` field (check with a probe `example : <field type> := cutoffMultiplier`). Work through the residuals in the order the long pole dictates:
**R1** (product → convolution at the datum level): for `b i := besselW s • scalarConvolution (angularFourier χ_ℂ) (besselW (-s) • (A i))`, show `angularRealization s (b i) ψ =
angularRealization s (A i) (smulLeftCLM ℂ (χ·) ψ)` for every test `ψ`. Strategy: prove the Schwartz-level identity first — for Schwartz `f`, `𝓕(χ f) = 𝓕χ ∗ 𝓕f` follows from the
forward Mathlib convolution theorem (grep `fourier_convolution`, `fourierIntegral_convolution`, `SchwartzMap.fourierTransformCLE`) applied to `𝓕⁻¹`-preimages, then transfer to
the angular normalization (`frequencyUnit`/dilation bookkeeping — read `angularFourier` in `Section3/T22/Domain.lean` or wherever it is defined) — then pass to `L²` data by the
density/continuity of the pairing (`angularRealization` is a continuous functional of the datum in `L²`; the convolution engine gives the needed continuity). If a step needs a
lemma Mathlib lacks, isolate it as the single exact residual, do not assume it. **R2**: `realSymmetry (b i) = b i` from real-evenness of `angularFourier χ_ℂ` (χ real, `𝓕χ(-ξ) = conj 𝓕χ(ξ)`).
**R3**: `‖B‖ₑ² = Σ_i ‖B i‖ₑ²` (`PiLp 2` Pythagoras) and datum norm ↔ `eLpNorm` of the weighted transform. **R4**: `C := cutoffMultiplierConst s χ + 1` (positivity for every `χ`).
Deliverables: the module, `research/T22/probes/cutoff_multiplier_field_closes.lean` (field-type match by `exact` + a nonzero non-vacuity instance), `research/T22/axioms_ua3b.lean`,
`research/T22/ATTEMPTS_UA3B.md` (which residual closed, which did not, exact statements/errors), status line in `T22_SPLIT.md` (U-A3), one `logs/LESSONS.md` line if pin-specific.
Also correct the `T22_SPLIT.md` U-A5 status sentence that calls `LocalizationBoundary`'s `domainL2Sq_*` "`0<s<1` only" (review 393: those `L²` helpers have no `s` premise; they need an integral-to-eLpNorm bridge).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.CutoffMultiplierField` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement / files / gaps with error text / commands and results). Try `research/T22/REPORT_406.md`; if the
report-file guard blocks it, put the full report in your final message.
