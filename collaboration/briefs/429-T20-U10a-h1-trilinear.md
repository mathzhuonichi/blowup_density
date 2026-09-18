# Lane 429-T20-U10a-h1-trilinear — T20 U10a: the mean-zero `H¹` trilinear estimate `|⟪(v·∇)v, Δv⟫| ≤ C₁ · y · ‖Δv‖²₂` on T³

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/429-T20-U10a-h1-trilinear` (git branch `erenup/429-T20-U10a-h1-trilinear`, based on `origin/erenup/integration-section3`, which contains
`Section3/T20/{CriticalRegularity,MeanReduction,BIntegral,ConstantTransport,CriticalTrilinear}.lean` and the full T12 set incl. lane 401's verbatim `velocityCriticalL3` (`CriticalL3Density.lean`),
lane 400's `gradientLSix` (`GradientLSix.lean`: `‖∇v‖₆ ≤ Csix·‖Δv‖₂`, plus `periodicLpENorm_gradientTensor_le_laplacian` and the Leibniz/tiling helpers), lane 405's `GradientLambdaL3.lean`
(column bound `periodicLpENorm_gradientTensor_le_sum`, `eLpNorm_torus_le_sum_of_norm_le`)). Read `CLAUDE.md`, **`research/T20/T20_SPLIT.md` §0, unit U10a (`:166-169`) and unit U10b** (the consumer:
`hOneEnergy` field `Section3/T20/CriticalRegularity.lean:330-342` uses `gradientSqT`, `laplacianSqT`, `lTwoSqT` — read their definitions and match the spelling U10b will need),
`paper/sections/03-torus.tex:467-484` (`eq:H1energy` and the `‖v‖₃‖∇v‖₆‖Δv‖₂` step, `:475-477` for `‖∇(∂ⱼv)‖₂ ≤ ‖Δv‖₂`), lane 413's `Section3/T20/CriticalTrilinear.lean` (the three-factor torus Hölder
`lintegral_enorm_mul_three_le_torus`, `enorm_inner_advection_le`, `criticalAdvectionHolderT`, and the U8 bridge pattern — reuse them; do not re-prove), `research/T20/REPORT_413.md`, `REPORT_400.md`,
and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T20/H1Trilinear.lean` (namespace `NSFormalization.Section3.T20`): for smooth periodic mean-zero `v` (with `MemPeriodicHomogeneous (1/2) v`
so that `y < ⊤`, as in U8), `|∫ y : PeriodicTorus, torusLift (fun x ↦ inner ℝ (advection (lift v) 0 x) (laplacian v x)) y ∂periodicTorusMeasure| ≤ h1TrilinearConst *
(periodicHomogeneousENorm (1/2) v).toReal * laplacianSqT v` — state it in exactly the slice spelling U10b will apply (`laplacianSqT` = `‖Δv‖²₂` as defined in `CriticalRegularity.lean`; give the
`ℝ≥0∞` form too). Route: pointwise `‖⟨(v·∇)v, Δv⟩‖ ≤ ‖v‖·‖∇v‖·‖Δv‖`; three-factor Hölder with exponents `(3, 6, 2)` on the torus (generalise lane 413's `(3,3,3)` lemma or use Mathlib's
`ENNReal.lintegral_prod_norm_pow_le` directly with `1/3 + 1/6 + 1/2 = 1`); `‖v‖₃ ≤ CcriticalHalf·y` (`velocityCriticalL3`), `‖∇v‖₆ ≤ Csix·‖Δv‖₂` (`gradientLSix`); so `C₁ := CcriticalHalf * Csix` with `_pos`.
The `‖∇(∂ⱼv)‖₂ ≤ ‖Δv‖₂` Fourier fact is only needed if your spelling of `‖∇v‖₆`'s input differs from `gradientLSix`'s — check first. Deliverables: the module, `research/T20/probes/h1_trilinear_closes.lean`
(the estimate at a nonzero smooth mean-zero witness such as `meanZeroPartT (x ↦ cos(2π x₀)·e₀)`, plus a shape check in U10b's slice spelling `fun x ↦ meanFreeVelocity g w.velocity (t, x)`),
`research/T20/axioms_u10a.lean`, `research/T20/ATTEMPTS_U10A.md`, U10a status line in `T20_SPLIT.md`, one `logs/LESSONS.md` line if pin-specific.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.H1Trilinear` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement and constant / files / gaps with error text / commands and results). Try `research/T20/REPORT_429.md`; if the report-file
guard blocks it, put the full report in your final message.
