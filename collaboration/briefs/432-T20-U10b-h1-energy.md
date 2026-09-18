# Lane 432-T20-U10b-h1-energy — T20 U10b: `hOneEnergy` verbatim (`eq:H1energy`: `E' + ν‖Δv‖²₂ ≤ CH1·ν⁻¹·‖h‖²₂` under `ρ < cν`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/432-T20-U10b-h1-energy` (git branch `erenup/432-T20-U10b-h1-energy`, = lane 428's branch + lane 429's branch + `origin/erenup/integration-section3`
(which has lane 427's dedupe of `contDiff_dirDeriv` into `Section3/T12/DirDeriv.lean`, so `GradientLSix` and `GradientLambdaL3` can now be imported together)). It contains
`Section3/T20/{CriticalRegularity,MeanReduction,BIntegral,ConstantTransport,CriticalTrilinear,CriticalEnergy,YBound,H1Trilinear}.lean`. Read `CLAUDE.md`, **`research/T20/T20_SPLIT.md` §0 and unit U10b**
(`:170-178`), the canonical field `hOneEnergy` in `Section3/T20/CriticalRegularity.lean:330-342` (with `gradientSqT`, `laplacianSqT`, `lTwoSqT` defined nearby — read them), `paper/sections/03-torus.tex:467-484`
(`eq:H1energy`), `research/T20/REPORT_415.md` (U8: the Fourier-side derivative template `hasDerivAt_tsum_critFreqEnergy`, `hasSum_periodicPairing`, `rawEnergyDeriv_split`, `advection_mean_split`,
`meanFreeVelocity_slice_eq`, how pressure/mean-transport drop), `REPORT_428.md` (U9: `yBound`, `yBound_of_le`, `criticalSmallness`, `criticalY_ne_top`, `criticalYProfileT`), `REPORT_429.md` (U10a:
`h1Trilinear_slice` in the `criticalY`/`laplacianSqT` slice spelling, `h1TrilinearConst`), T11 `EnergyIdentity.lean` (`hasDerivAt_torusSobolevNormAt_sq` at order 1 — this is exactly `gradientSqT`'s
derivative), `HighOrder.lean:312,345,367` (pressure drop, mean-transport drop) and `:386 torusYoungAbsorb`, the R³ analogue `Section4/R44/Absorption.lean`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T20/H1Energy.lean` (namespace `NSFormalization.Section3.T20`): `def CH1 : ℝ` (explicit, positive: `CH1_pos`) and `theorem hOneEnergy` whose type is
literally the canonical field at `c := criticalSmallness` (or a smaller explicit `c` if the absorption needs `c < 1/(4·h1TrilinearConst)`-type smallness — then define `def criticalSmallnessH1` and
export both `yBound_of_le`-style compatibility and the strict `c < 1/(4C₀)` fact U13 needs; say which), probe `example : hOneEnergyFieldType criticalSmallness CH1 := hOneEnergy` mirroring lanes
415/428. Route: differentiate `gradientSqT (v(s))` along the mean-free velocity (order-1 analogue of U8's derivative — T11's `hasDerivAt_torusSobolevNormAt_sq` / U8's `hasDerivAt_tsum_critFreqEnergy`
at the homogeneous order-1 weight); pair `meanFreeEquation` against `−Δv`: pressure and mean-transport terms vanish on the Fourier side (as in U8), dissipation gives `+ν·laplacianSqT`, the convection
term is bounded by `h1Trilinear_slice` (U10a) `≤ C₁·y(t)·‖Δv‖²₂` and absorbed using `yBound` (U9): `y(t) ≤ ρ < c·ν` so `C₁·y ≤ ν/4` when `c ≤ 1/(4C₁)` (adjust `c` accordingly); the force term
`|⟪h, Δv⟫| ≤ ‖h‖₂‖Δv‖₂ ≤ (ν/4)‖Δv‖²₂ + ν⁻¹‖h‖²₂` (Young, `torusYoungAbsorb`), giving `E' + ν‖Δv‖²₂ ≤ CH1·ν⁻¹·‖h‖²₂` after moving the absorbed halves (set `CH1` accordingly, e.g. `2` or `1` — state
the exact value). Handle finiteness of the `.toReal`s via `reductionRegular`/`criticalY_ne_top`/`periodicLpENorm_two_laplacian_ne_top` (429). Deliverables: the module,
`research/T20/probes/h1_energy_closes.lean` (field-type match; non-vacuity at the zero-force zero-solution instance of lanes 415/428 incl. the satisfiable smallness hypothesis),
`research/T20/axioms_u10b.lean`, `research/T20/ATTEMPTS_U10B.md`, U10b status line in `T20_SPLIT.md`, one `logs/LESSONS.md` line if pin-specific.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.H1Energy` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement and constants / files / gaps with error text / commands and results). Try `research/T20/REPORT_432.md`; if the report-file
guard blocks it, put the full report in your final message.
