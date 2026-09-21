# Lane 312-T10-force-paths — all-order coefficient paths for `MemForceT` forces and the vector gradient/energy identities (T10 needs-a-lemma items 11 and 12)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/312-T10-force-paths` (git branch `erenup/312-T10-force-paths`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean`, `Section3/T11/LocalTheory.lean`, `Section3/T12/*.lean`, and the registered
contract `verification/Contracts/V1/TorusData.lean`). Read `CLAUDE.md`, `research/T10/COMPARISON.md` §"Needs a lemma" items **11** and **12** (`:128-134`), `research/T10/REVIEW_305-T10-fourier-calculus.md`
§3 (the two blocking gaps this lane closes — read them completely), `research/T10/REPORT_305.md` (what `FourierCalculus.lean` already gives you: derivative/Laplacian symbols, decay, summability),
`Section3/T10/PeriodicData.lean` (`IsPeriodicSobolevPath :218-230`, `forceSobolevENormT`, `MemForceT :237-245`, `energyEssSupT`/`energyGradientT`/`energyENormT`, `coefficientEnergy*`), `Paper1/PeriodicSmoothSobolev.lean`
(`smoothPeriodicWeightedFourierLp :45`, `norm_smoothPeriodicWeightedFourierLp :53`), and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include non-vacuity `example`s (the zero force; a single-mode force with a smooth compactly supported time profile).
- No named inputs expected; if something is genuinely out of reach, name exactly ONE input with its exact statement and prove everything else.

## Goal — module `formalization/NSFormalization/Section3/T10/ForcePaths.lean` (namespace `NSFormalization.Section3.T10`)
1. **Item 11 — coefficient paths of forces**: for `f` with `MemForceT f` (smooth, unit-periodic in space, compact time support in `(0,∞)`; read the exact definition), for every `m : ℕ` there is
   `G : ℝ → PeriodicSobolev (m : ℝ)` with `IsPeriodicSobolevPath (m : ℝ) f G` (exact predicate from `PeriodicData.lean`), `Continuous G` (or the regularity the predicate/consumers demand:
   `ContDiff ℝ ∞ G` if provable via the coefficient formula and differentiation under the integral — say which you prove), strong measurability, and finite norms: `forceSobolevENormT 1 (m : ℝ) f ≠ ⊤`
   and `forceSobolevENormT 2 (m : ℝ) f ≠ ⊤` (whatever `forceSobolevENormT q s f` unfolds to — read it; the compact time support + continuity in `t` of `‖G t‖` gives both). Also export the
   slicewise statement: for each `t`, `IsPeriodicDatum (m : ℝ) (f (t,·)) (G t)` with the integrability conjunct (amendment 1) from smoothness on the compact torus. If `Paper1` already has the
   existing `PeriodicForceSpace`-type interface (`grep -rn PeriodicForceSpace formalization/NSFormalization/Paper1`), prove the identification `MemForceT f ↔ …` the reconciliation lists (item 11's last clause).
2. **Item 12 — gradient/energy identities**: (a) the vector full-gradient identity: for smooth periodic `v : SpatialField`, `eLpNorm (torusLift (fun x ↦ gradient tensor of v)) 2 = ` the
   coefficient expression `(∑' k, 4π²|k|² ∑ i ‖v̂_i(k)‖²)^{1/2}` (spell the gradient tensor as `Section3/T12/MeanZeroCalculus.lean`'s `gradientTensor` and reuse `FourierCalculus.periodicFourierCoeff_gradient_sq`
   + `Parseval`), (b) the physical/coefficient energy identity: for fixed finite `T` and `z` smooth periodic on `[0,T]`, `energyENormT T z = coefficientEnergyENormT T z` (or the two halves
   `energyEssSupT`/`energyGradientT` vs `coefficientEnergyEssSupT`/`coefficientEnergyGradientT` separately) — read both definitions; if the equality needs a measurability/regularity hypothesis in time,
   state it exactly.
3. The componentwise `SpatialField` corollaries the 305 review lists as missing (derivative, decay, Laplacian, gradient for vector fields), each with a conformance line.

## Deliverables
1. The module; probe `research/T10/probes/force_paths_examples.lean`; conformance `research/T10/axioms_force_paths.lean`.
2. Records `research/T10/ATTEMPTS_FORCE_PATHS.md` (paths tried, exact error text); report `research/T10/REPORT_312.md`; append "Registered/proved by lane 312" notes to items 11/12 in `research/T10/COMPARISON.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.ForcePaths` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[312-T10] ForcePaths`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
