# Lane 163-C01-e5-enstrophy — C01 row E5: the enstrophy time derivative

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/163-C01-e5-enstrophy` (git branch
`erenup/163-C01-e5-enstrophy`, based on `origin/erenup/integration`). Read `CLAUDE.md`,
`collaboration/HANDOFF.md` §0 (rules) and §2 P2, and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree. Never touch `/data_8T/ping/blowup_density` (root checkout) or any
  other worktree. Never `git push`, never merge, never rebase. Committing on your own branch is allowed.
- Lean setup: every shell must first run `. scripts/lean-env.sh`; run `lake` ONLY from
  `verification/` (`cd verification && LEAN_NUM_THREADS=6 lake build …`); drafts via
  `cd verification && lake env lean ../research/C01/<file>.lean`.
- No `sorry`, `admit`, `axiom`, `native_decide`. `set_option maxHeartbeats N in` only per
  declaration with `N ≤ 400000` and a comment. Do not edit existing modules; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of
  `formalization/NSFormalization/Section4/{D01,A03,A04,A01,C01}`. Before citing a paper line, `sed -n` it.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; include a
  non-vacuity `example` on `A04.zeroSol` with `memForceR_zero` (see `research/C01/axioms_e4.lean`).

## Goal
Row **E5** of `research/C01/ENERGY_SPLIT.md` (`:114`): for a classical solution
`w : ClassicalSolutionR ν a f T` with `hf : MemForceR f`, at every interior time `t ∈ Ioo 0 T`,
`d/dt ∑ᵢ ‖∂ᵢu(t,·)‖²_{L²} = 2 ∑ᵢ ⟪∂ᵢu, ∂ᵢ∂ₜu⟫ = −2 ⟪Δu, ∂ₜu⟫` — the enstrophy analogue of row E4,
which lane 150 closed in `Section4/C01/EnergyDerivative.lean` (`energyDerivative_hasDerivAt`, via the
vendor's `EulerOrdinarySobolev.wordEnergy_hasDerivWithinAt` at `s = 0` on a translated window
`Icc 0 (S − c)`, with `hA` = velocity jet continuity, `hB` = `∂ₜu` jet continuity from
`PressureJetPath.temporalSlicePath_jetLp_continuous`, `hd` = pointwise time derivative).

Route: the same vendor lemma at `s = 1` (`wordEnergy 1 A = wordEnergy 0 A + ∑ᵢ‖∂ᵢ A‖²` — check the
vendor's definition of `wordEnergy` and `wordField` in `vendor/NavierStokesAndEuler/…/Euler/OrdinaryWordTime.lean:69-87`
and `OrdinaryWordSpace`), subtract the `s = 0` identity, then the integration by parts
`∑ᵢ ⟪∂ᵢu, ∂ᵢ∂ₜu⟫ = −⟪Δu, ∂ₜu⟫` via `field_directional_ibp` (grep the vendor for it) on carrier-B
`SmoothL2Field`s. Mirror `EnergyDerivative.lean` step by step (window shift, `projIcc`,
`HasDerivWithinAt → HasDerivAt`, the `s = 1` word bridge analogous to `wordEnergy_zero` /
`wordInner_sum_zero`).

Context: `Section4/C01/EnergyDerivative.lean`, `EnergySpec.lean`, `EnergyBounds.lean`,
`MomentumCarrierB.lean` (`velocitySliceField`, `temporalSliceField`, `laplacianField_velocitySlice_field`),
`JetPaths.lean`, `PressureJetPath.lean`, `Vocabulary.lean` (`gradientSq`, `norm_toLp_sq_eq_l2Sq`),
`research/C01/Spec.lean:487` (`enstrophyIdentity`) and `:364-400`, `research/C01/REVIEW_E4.md`,
`research/C01/ATTEMPTS_E4.md` (pitfalls: `HasDerivAt.scomp`, instance diamonds, `⟪⟫` notation,
`Nat.zero_add` for `range (0+1)`).

## Deliverables
1. New module `formalization/NSFormalization/Section4/C01/Enstrophy.lean`
   (namespace `NSFormalization.Section4.C01`):
   - `wordEnergy_one` (the `s = 1` collapse) and the `s = 1` pairing-sum collapse;
   - `enstrophyDerivative_hasDerivAt`: `HasDerivAt (fun ρ => ∑ᵢ ‖(∂ᵢ u)(ρ,·)‖²_{L²}) (2 ∑ᵢ ⟪∂ᵢu, ∂ᵢ∂ₜu⟫) r`
     on the interior of a window `[c, S] ⊂ (0, T)` (state it in the raw-integral/`toLp` vocabulary
     used by `EnergyDerivative.lean`);
   - `enstrophyDerivative_eq_neg_laplacian`: the value equals `−2 ⟪Δu(t,·), ∂ₜu(t,·)⟫` by
     integration by parts (vendor `field_directional_ibp` or the tree's `laplacian_pairing`);
   - a clamp-free corollary at every `t ∈ Ioo 0 T` (mirror `energyIdentity_classical_unconditional`).
2. Records: `research/C01/ATTEMPTS_E5.md`; conformance `research/C01/axioms_e5.lean`; update
   `research/C01/ENERGY_SPLIT.md` row E5 (DONE or exact residual).

## Gates (run all, paste outputs)
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.C01.Enstrophy` (silent),
`lake env lean` on the module (0 output), `lake env lean ../research/C01/axioms_e5.lean`,
`make check` from the worktree root.

## Report
Commit on your branch and end with a four-part report: 1. theorems proved (names, exact statements);
2. what is in Lean now; 3. gaps (exact residual with error text); 4. commands and results.
Also write it to `research/C01/REPORT_163.md`.
