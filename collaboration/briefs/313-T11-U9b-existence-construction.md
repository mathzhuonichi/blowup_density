# Lane 313-T11-U9b-existence-construction — the periodic quantitative local existence, first construction sub-lane (route R2 fixed by lane 311)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/313-T11-U9b-existence-construction` (git branch `erenup/313-T11-U9b-existence-construction`, based on `origin/erenup/integration-section3` **after** lane 311 landed:
`formalization/NSFormalization/Section3/T11/LocalExistenceProbe.lean` (the `T³` two-space contract `TorusTwoSpaceContract`, `torusForcedPicard`, `TorusForcedMildOn`, `TorusPicardConstants`, the proved
heat-semigroup rung `torusHeat*`, `torus_bilinear_bound`, `torusHomogeneousSolution*`), `research/T11/EXISTENCE_ROUTE.md` (**binding**: route R2, §"Subsequent sub-lanes: exact targets"),
`research/T11/LEAD_AMENDMENTS.md` (**binding**: amendment 1 — the named input is now `PeriodicQuantitativeLocalInput'` with order-wise force bounds `M : ℕ → ℝ≥0∞`), `research/T11/T11_SPLIT.md`
(§0 ground rules, U9), the T10 modules incl. `FourierCalculus.lean` and (if landed) `ForcePaths.lean`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Peeling rule**: the only allowed named input is the residue of `PeriodicQuantitativeLocalInput'` that you do not discharge, stated exactly as ONE `def … : Prop` (e.g. the convolution
  boundedness of the projected convection symbol on the coefficient carrier, if that is what remains); everything else proved. Never weaken a target.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include non-vacuity `example`s.

## Goal — module `formalization/NSFormalization/Section3/T11/LocalExistence.lean` (namespace `NSFormalization.Section3.T11`)
1. Define `PeriodicQuantitativeLocalInput'` **verbatim from `LEAD_AMENDMENTS.md`** and re-derive lane 311's `quantitative_lifespan_lower_bound` from it (`quantitative_lifespan_lower_bound'`).
2. Take the **first two targets** of `EXISTENCE_ROUTE.md` §"Subsequent sub-lanes" in order (read their exact statements there — typically: (i) the bilinear/convolution estimate for the projected
   convection symbol on the weighted `ℓ²` carrier at the orders the contract needs (`H³`-type product bound via `Section3/T12/SpectralGap.lean`'s reweighting and the Fourier-calculus decay, or the
   discrete Young inequality on `Fin 3 → ℤ`), and (ii) the forced Picard iteration on a short interval: existence and uniqueness of a fixed point of `torusForcedPicard` in the complete carrier,
   with the explicit `TorusPicardConstants` and the lifespan lower bound in terms of the datum norm and the force bounds), and prove them. If (i) is out of reach in one lane, isolate it as the
   single named input and finish (ii) conditionally on it — say so exactly.
3. Write `research/T11/EXISTENCE_ROUTE.md` §"U9b status" (append only): what is proved, what remains for U9c–e with exact statements.

## Deliverables
1. The module; probe `research/T11/probes/existence_u9b.lean` (the proved statements instantiated on the zero datum / a single mode); conformance `research/T11/axioms_existence_u9b.lean`.
2. Records `research/T11/ATTEMPTS_EXISTENCE_U9B.md` (paths tried, exact error text, the residual named input with its exact statement); report `research/T11/REPORT_313.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.LocalExistence` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[313-T11] LocalExistence (U9b)`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
