# Lane 397-T22-UA3-cutoff-multiplier — T22 U-A3 (analytic core): the `cutoffMultiplier` field of `BoundedDomainNormAPI` verbatim (a smooth compactly supported cutoff acts as a bounded multiplier on every inhomogeneous Sobolev datum space, all real `s`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/397-T22-UA3-cutoff-multiplier` (git branch `erenup/397-T22-UA3-cutoff-multiplier`, based on lane 391's branch merged with
`origin/erenup/integration-section3`: `Section3/T22/{Domain,RestrictBridge,WeightRatio,CutoffKernel,OrderZeroIsometry}.lean` — lane 386's `weight_ratio_le`/`sobolevBesselWeight_norm_ratio_le`
(Peetre with constant `2^(|s|/2)` in the `Paper3.sobolevBesselWeight` spelling), lane 391's `integrable_weighted_fourier_cutoff` (angular and Mathlib conventions) and
`lintegral_weighted_fourier_cutoff_ne_top`, `cutoffSchwartz`). Read `CLAUDE.md`, **`research/T22/T22_SPLIT.md` §0 and unit U-A3 (target verbatim `research/T22/Spec.lean:140-144`,
route)**, `research/T22/REPORT_{386,391}.md`, the datum layer (`Section4/D01/*.lean`: `RealVectorSobolev s`, the weighted `L²` model, `angularRealization`, `realSubspace`;
`Paper3/SobolevHilbertModel.lean` `sobolevBesselWeight`; `Section3/T22/Domain.lean` `IsCutoffDatum s χ A B` = `SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ))` pairing),
`formalization/NSFormalization/Source/YoungConvolution.lean` (`eLpNorm_convolution_one_two` — Young `L¹ ∗ L² → L²`), `Section3/T12/TameProduct.lean` (lane 342's `torusYoungConvolution` —
the ℤ³ analogue and its proof pattern), and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; the `maxHeartbeats` note of lane 387).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). An honest partial with the exact residual statement and error text beats a stub.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T22/CutoffMultiplier.lean` (namespace `NSFormalization.Section3.T22`): `theorem cutoffMultiplier` — the field verbatim: for every
real `s` and smooth compactly supported `χ`, `∃ C > 0, ∀ A : RealVectorSobolev s, ∃ B : RealVectorSobolev s, IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ` (match the Spec's exact
quantifier order and spellings). Route (T22_SPLIT U-A3): `C := peetreConst s · ∫ (1+‖ζ‖²)^(|s|/2) ‖𝓕χ ζ‖` (386 constant × 391 kernel mass, `> 0`); for `A`, define `B` componentwise so
that `weighted datum(B) = (weighted 𝓕χ) ∗ weighted datum(A)` in the angular normalization (the Fourier product↔convolution identity for the Schwartz multiplier against a tempered
datum — establish it through the pairing that `IsCutoffDatum` states, i.e. `angularRealization s (B i) ψ = angularRealization s (A i) (χ·ψ)` for every Schwartz test `ψ`);
`weight_ratio_le` dominates the output weight pointwise by the kernel-weighted convolution; `eLpNorm_convolution_one_two` (Young) gives `‖B‖ₑ ≤ ofReal C * ‖A‖ₑ`; `𝓕χ` real-even (real `χ`)
preserves `realSubspace`, so `B : RealVectorSobolev s`; unfold `smulLeftCLM` to close `IsCutoffDatum s χ A B`. This is the critical path of T22 (`zeroExtensionComparison` U-Z1 reduces
to it); if the full convolution identity is too heavy, deliver the smooth-datum case (`A` the datum of a Schwartz field) completely plus the exact residual for general tempered data.

## Deliverables
1. `Section3/T22/CutoffMultiplier.lean`; 2. probe `research/T22/probes/cutoff_multiplier_closes.lean` (the canonical field closed by `exact`; non-vacuity: a `ContDiffBump` cutoff and the
order-0 datum of a nonzero bump field, both norms finite); 3. `research/T22/ATTEMPTS_UA3.md`, `research/T22/axioms_ua3.lean`, status in `research/T22/T22_SPLIT.md` U-A3, report
`research/T22/REPORT_397.md` (if a guard blocks the write, put the full report in your final message).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.CutoffMultiplier` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements and the constant / files / gaps with exact error text / commands and results).
