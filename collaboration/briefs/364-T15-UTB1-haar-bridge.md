# Lane 364-T15-UTB1-haar-bridge — T15 U-TB1: the energy Haar/Lebesgue single-copy bridges `eLpNorm (torusLift (periodize f)) 2 periodicTorusMeasure = eLpNorm f 2 volume` (+ gradient companion)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/364-T15-UTB1-haar-bridge` (git branch `erenup/364-T15-UTB1-haar-bridge`, based on `origin/erenup/integration-section3`).
Read `CLAUDE.md`, **`research/T15/T15_SPLIT.md` §0 and unit U-TB1**, `Section3/T13/ConstantEndpoints.lean` (`endpoint_zero_eq :364` — Lebesgue on the cube = whole ℝ³ for `f`
supported in the cube; `periodize_eq_of_mem_cube`, `interior_fundamentalCube`), `Section3/T13/TorusIdentity.lean` (`lintegral_fundamentalCube_ofReal :419`,
`fundamentalCube_ae_eq_halfOpenCube :402`, `torusLift_torusPoint :459` — Haar on the torus = Lebesgue on the cube), `Section3/T10/PeriodicData.lean` (`torusLift`,
`periodicTorusMeasure`, `energyENormT`/`energyGradientT` spellings — check `research/T10/Spec.lean:139` for `energyGradientT`), `Section3/T13/Localization.lean:86` (`gradientENorm`),
and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No placeholders, no aliases, no named inputs, no goal repackaging.** A `def X : Prop := <goal>` or a hypothesis equal to the target is a stub and will be discarded without review;
  an honest partial with the exact residual statement and error text is fine.
- Before claiming a lemma is "not in the tree", `grep -rn` `Section3/T10`, `Section3/T13`, `Section4/I03`, `verification/Contracts/V1/Scaling.lean`, `verification/Bindings/Scaling.lean`.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
1. `theorem eLpNorm_torusLift_periodize (f : SpatialField) (hf : ContDiff ℝ ∞ f) (hsupp : tsupport f ⊆ interior fundamentalCube) :
     eLpNorm (torusLift (periodize f)) 2 periodicTorusMeasure = eLpNorm f 2 volume`
   (weaken the hypotheses if the proof allows — e.g. measurability + support in the cube; say what you proved). Route: Haar on `T³` = Lebesgue on the cube (`torusLift_torusPoint`,
   `lintegral_fundamentalCube_ofReal`, `fundamentalCube_ae_eq_halfOpenCube`), `periodize f = f` on the cube (`periodize_eq_of_mem_cube`), Lebesgue on the cube = whole space for
   `f` supported inside (`endpoint_zero_eq`). Work in `lintegral` form (`eLpNorm_eq_lintegral_rpow_enorm` / `eLpNorm` at `p = 2`) and convert.
2. The gradient companion: the same identity for the spatial gradient, in T10's `energyGradientT`-compatible spelling versus T13's `gradientENorm` (state exactly which two norms you
   identify; `periodize` commutes with the gradient on the cube by `periodize_eq_of_mem_cube` on an open neighbourhood — use `periodize_eventuallyEq`/`interior` to differentiate).
3. Slice form for the time-dependent use (T15's energy norm is a time-slice integral): `∀ t, eLpNorm (torusLift (periodize (fun x => F (t,x)))) 2 periodicTorusMeasure = eLpNorm (fun x => F (t,x)) 2 volume`
   under the per-slice support hypothesis — a corollary of 1.

## Deliverables
1. `formalization/NSFormalization/Section3/T15/HaarBridge.lean` (namespace `NSFormalization.Section3.T15`); 2. probe `research/T15/probes/haar_bridge_closes.lean` (non-vacuity: the
`ContDiffBump` witness of `research/T13/probes/constant_endpoints_closes.lean`); 3. `research/T15/ATTEMPTS_UTB1.md`, `research/T15/axioms_utb1.lean`, status in `research/T15/T15_SPLIT.md`
U-TB1, report `research/T15/REPORT_364.md` (if a guard blocks the write, put the full report in your final message).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.HaarBridge` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands and results).
