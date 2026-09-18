# Lane 391-T22-UA2-cutoff-kernel — T22 U-A2: the Fourier transform of a smooth compactly supported cutoff is weighted-`L¹` for every polynomial weight

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/391-T22-UA2-cutoff-kernel` (git branch `erenup/391-T22-UA2-cutoff-kernel`, based on `origin/erenup/integration-section3` after #348:
`Section3/T22/{Domain,RestrictBridge,WeightRatio}.lean` (lane 386's `weight_ratio_le`, `sobolevBesselWeight_norm`)). Read `CLAUDE.md`, **`research/T22/T22_SPLIT.md` §0 and unit U-A2
(and U-A3 for how it is consumed: the `cutoffMultiplier` field of `research/T22/Spec.lean` — read the exact weight and Fourier-transform spellings the datum layer uses:
`Section4/D01/*.lean` `angularFourier`/`𝓕`, `Paper3/SobolevHilbertModel.lean` `sobolevBesselWeight`)**, `research/T22/REPORT_386.md`, Mathlib's Schwartz-space Fourier
transform (`SchwartzMap.fourierTransformCLM`, `SchwartzMap.decay`/`one_add_le_sup_seminorm_apply`, `HasCompactSupport.toSchwartzMap`-type constructions — grep the exact names
under this pin; `Section4/D01/HomogeneousWitness.lean` `schwartzAngularFourier :99` / `integrable_homogeneous_schwartz :109` already do a similar weighted-integrability argument),
and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). An honest partial with the exact residual statement and error text beats a stub.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T22/CutoffKernel.lean` (namespace `NSFormalization.Section3.T22`):
`theorem integrable_weighted_fourier_cutoff {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (s : ℝ) : Integrable (fun ζ => (1 + ‖ζ‖^2) ^ (|s|/2) * ‖𝓕χ ζ‖)`
in the exact Fourier-transform spelling the datum layer uses (state it for the transform U-A3 will convolve with — if the layer uses the angular/unitary transform, state and prove
that version, and derive the Mathlib `𝓕` version or vice versa via the dilation relating them). Route: `χ` smooth with compact support gives a `SchwartzMap` (build it: all iterated
derivatives are bounded with compact support, so every seminorm is finite); `𝓕χ` is Schwartz (`SchwartzMap.fourierTransformCLM`); Schwartz decay gives `‖𝓕χ ζ‖ ≤ C_N (1 + ‖ζ‖)^(−N)`
for every `N` (`SchwartzMap.one_add_le_sup_seminorm_apply` or `decay`); choose `N > |s| + 3` and use `integrable_one_add_norm` (`MeasureTheory.integrable_one_add_norm` for
`EuclideanSpace ℝ (Fin 3)`, `finrank = 3`) with the comparison `(1+‖ζ‖²)^(|s|/2) ≤ (1+‖ζ‖)^{|s|}`. Also the corollary in the `ENNReal`/`lintegral` form if U-A3's statement needs it
(read `cutoffMultiplier` and provide both), and the scalar/vector `χ • z` convolution-kernel form only if trivial.

## Deliverables
1. `Section3/T22/CutoffKernel.lean`; 2. probe `research/T22/probes/cutoff_kernel_closes.lean` (a concrete `ContDiffBump`-built `χ`, `s = 1/2` and `s = −2`); 3. `research/T22/ATTEMPTS_UA2.md`,
`research/T22/axioms_ua2.lean`, status in `research/T22/T22_SPLIT.md` U-A2, report `research/T22/REPORT_391.md` (if a guard blocks the write, put the full report in your final message).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.CutoffKernel` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands and results).
