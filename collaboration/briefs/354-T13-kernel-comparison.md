# Lane 354-T13-kernel-comparison — T13 `localization`, part 2: the kernel comparison on the cube with the paper's geometric constant, `ITorus s (periodize f) ≤ IReal s f + 4 · tailGeomConst s c r · ‖f‖₂²`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/354-T13-kernel-comparison` (git branch `erenup/354-T13-kernel-comparison`, based on lane 353's branch
merged with `origin/erenup/integration-section3`: canonical modules `Section3/T13/{Localization,ConstantEndpoints,TorusIdentity,LocalizationKernel}.lean`
— lane 353's `LocalizationKernel.lean` has `summable_latticeVector_rpow`, `tailSum`, `tailConst`, `latticeTail_le_tailConst`, `two_r_lt_one_of_closure_ball_subset`,
`periodicSobolevENorm_le_l2_add_homogeneous`; lane 344's `ConstantEndpoints.lean` has `periodize_eq_of_mem_cube`, `interior_fundamentalCube`, `tsupport_subset_cube`,
`eq_zero_of_mem_cube`; lane 345's `TorusIdentity.lean` has `periodicKernel_unfold`, `lintegral_eq_tsum_halfOpenCube`, `fundamentalCube_ae_eq_halfOpenCube`).
Read `CLAUDE.md` (hard rules), **`research/T13/ATTEMPTS_LOCALIZATION_KERNEL.md` (§"Residual lemmas needed for a correct §2" — this lane is exactly those four
items; note why the naive constant `tailConst s (2r)` is insufficient)**, `research/T13/REPORT_353.md`, `REPORT_344.md`, `REPORT_345.md`, `research/T13/COMPARISON.md`,
`paper/sections/03-torus.tex:73-98` (the proof of `eq:localization`, esp. `:79-92` where the separation `d = dist(closure B, ∂Q)` enters), and the top 40 lines of
`logs/LESSONS.md` (**name every instance explicitly**; a lead-written constant in a brief is a suggestion to verify, not a hard target — if a statement below is false as
written, say so with the counterexample and prove the corrected statement).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). Honest partial with exact residual statements and error text beats a stub.
- Before claiming a lemma is "not in the tree", `grep -rn` `Section3/T13/*.lean`, `Section3/T10/*.lean`, `Section3/T12/*.lean`. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`.

## Goal — the four residual items of `ATTEMPTS_LOCALIZATION_KERNEL.md`, as standalone theorems (statements to verify, then prove)
1. `exists_separation {c r} (hr : 0 < r) (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube) : ∃ δ, 0 < δ ∧ closure (Metric.ball c r) ⊆ {x | ∀ i, δ ≤ x i ∧ x i ≤ 1 − δ}`
   (compactness of the closed ball inside the open cube; `interior_fundamentalCube = (0,1)³` from 344).
2. `tailGeomConst s c r : ℝ≥0∞` with `tailGeomConst_lt_top (hs : 0 < s) …` and
   `latticeTail_le_tailGeomConst : ∀ x ∈ closure (ball c r), ∀ y ∈ fundamentalCube, latticeTail s (x − y) ≤ tailGeomConst s c r`
   (for `n ≠ 0`: either `‖x − y + n‖ ≥ δ`-type lower bound from the separation (for the finitely many `n` with `‖n‖` small) or `‖x − y + n‖ ≥ ‖n‖/2` (for `‖n‖ ≥ 2√3`, since
   `‖x − y‖ ≤ √3`); sum the two regimes with `summable_latticeVector_rpow`; define the constant as whatever the proof produces — an explicit `ℝ≥0∞` expression in `s, δ`).
3. `iTorus_singular_le : ∫⁻ x in fundamentalCube, ∫⁻ y in fundamentalCube, ofReal ‖f x − f y‖² · fractionalRadialKernel s (x − y) ≤ IReal s f`
   (substitute `y = x + h` in the inner integral — `lintegral` is translation invariant for the Haar measure on `EuclideanSpace`: `MeasureTheory.lintegral_add_right_eq_self`
   / `Measure.IsAddRightInvariant` — then Tonelli `lintegral_lintegral_swap` and enlarge both domains to `ℝ³` by `lintegral_mono_set`/`setLIntegral_le_lintegral`; watch the
   orientation of the difference: `IReal` is written with `f (x + h) − f x`, so `h = y − x` and the kernel is even).
4. `iTorus_periodize_le {s c r f} (hs : 0 < s) (hs1 : s < 1) (hr : 0 < r) (hball : closure (ball c r) ⊆ interior fundamentalCube) (hf : ContDiff ℝ ∞ f) (hsupp : SupportedInBall c r f) :
   ITorus s (periodize f) ≤ IReal s f + 4 * tailGeomConst s c r * (eLpNorm f 2 volume) ^ 2`
   (assemble: `periodize f = f` on `Q` (344), split `periodicKernel s h = fractionalRadialKernel s h + latticeTail s h` (separate the `n = 0` term of the `tsum` — match how
   `latticeTail` is defined in `Localization.lean:66`), item 3 for the singular part; for the tail part the integrand vanishes unless `x ∈ ball ∨ y ∈ ball` (outside the ball
   `f = 0`), on that region `latticeTail ≤ tailGeomConst` by item 2 (use `x ∈ closure (ball c r)` or symmetry `latticeTail s (−h) = latticeTail s h` for the `y ∈ ball` case),
   `‖f x − f y‖² ≤ 2‖f x‖² + 2‖f y‖²`, `|Q| = 1`, giving `4 · tailGeomConst · ∫‖f‖²`; convert `∫⁻ ‖f‖²` to `(eLpNorm f 2 volume)^2` — if a different spelling of `‖f‖₂²` is more
   convenient for lane 359 (assembly), state it and prove the conversion lemma).

## Deliverables
1. New module `formalization/NSFormalization/Section3/T13/KernelComparison.lean` (namespace `NSFormalization.Section3.T13`) with the four theorems (exact statements as
   above or the corrected ones, each documented).
2. Probe `research/T13/probes/kernel_comparison_closes.lean`: the four theorems instantiated on the `ContDiffBump` field of `research/T13/probes/constant_endpoints_closes.lean`
   (non-vacuity), plus an `example` sketching lane 359's assembly of `localization` from `torus_identity` (345), `endpoint_zero`/`constant_pos_finite` (344),
   `periodicSobolevENorm_le_l2_add_homogeneous` (353), `iTorus_periodize_le` (this lane) and a `wholeSpace_identity`-shaped hypothesis **inside the example only**.
3. Records: `research/T13/ATTEMPTS_KERNEL_COMPARISON.md`, conformance `research/T13/axioms_kernel_comparison.lean`, status line in `research/T13/COMPARISON.md`,
   report `research/T13/REPORT_354.md` (if a guard blocks the write, put the full report in your final message).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T13.KernelComparison` (0 errors), `lake env lean` on the module, probe and axioms file;
`make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and constants / files / gaps with exact error text / commands and results).
