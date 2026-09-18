# Lane 385-T17-U5U6-derivative-bounds — T17 U5 + U6 (pure transport): `correction_derivative_bound` and `force_derivative_bound` on the concrete correction

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/385-T17-U5U6-derivative-bounds` (git branch `erenup/385-T17-U5U6-derivative-bounds`, based on `origin/erenup/integration-section3` after
#342: `Section3/T17/{CorrectionProfile,Transport,LatticeDeriv}.lean` — lane 373's `correctionData`, `correctionData_correction` (`rfl`), `correctionForce`, `force_eq`; lane 369's
`latticeLift_iteratedFDeriv_eq` (general `∃ k` form) and `latticeLift_iteratedFDeriv_norm_le_iSup`). Read `CLAUDE.md`, **`research/T17/T17_SPLIT.md` §0 and units U5, U6**,
**`research/T17/Spec.lean:870-900`** (`correction_derivative_bound :878`, `force_derivative_bound :893` — the two halves of `eq:derivativebounds`, `03-torus.tex:226-233`, verbatim
targets: `j` time and `m` space derivatives of norm `≤ C(ε⁻¹)^{2j+m}` on the correction, `≤ C(ε⁻¹)^{2+m}` on the force), `research/T17/REPORT_{369,373}.md`, the Euclidean bounds
`formalization/NSFormalization/Paper1/*.lean` (`physical_mixed_derivative_bound :291` — `|∂ₜʲ∂ₓᵝ physicalCorrection| ≤ C (ε⁻¹)^{2j+m}` on `Ioc 0 1`; `physicalForce_spatial_derivative_bound :270`
— grep the exact names/files), and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No placeholders, no aliases, no named inputs, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
Two modules, `Section3/T17/CorrectionDeriv.lean` and `Section3/T17/ForceDeriv.lean` (namespace `NSFormalization.Section3.T17`), each ending in a theorem whose statement is the
Spec's field **verbatim** on the concrete correction (`D := correctionData …`, bare `(x₀, T)` as lanes 370/373/375; the `hv : ContDiff ℝ ∞ v` premise only if the Paper1 bound needs
it — say so): `correction_derivative_bound` (route: `correctionData_correction` rewrites `D.correction ε` to `latticeLift (physicalCorrection …)`; `latticeLift_iteratedFDeriv_eq` moves the
iterated derivative to the single nearby copy; Paper1's `physical_mixed_derivative_bound` closes it; `D.ε₀ ≤ 1` from the placement hypotheses — take the hypotheses the Spec's field
quantifies over) and `force_derivative_bound` (route: `force_eq` + `latticeLift_iteratedFDeriv_eq` + Paper1's `physicalForce_spatial_derivative_bound`). Define the constants as the
Paper1 constants (`def correctionDerivConst`, `def forceDerivConst : ℕ → ℕ → ℝ` or the Spec's shape) and prove their nonnegativity fields if the Spec has them.

## Deliverables
1. The two modules; 2. probe `research/T17/probes/derivative_bounds_closes.lean` restating the two Spec fields token-for-token and closing each by `exact`; non-vacuity on the nonzero
constant reference + T16 cutoffs as in `research/T17/probes/transport_closes.lean`; 3. `research/T17/ATTEMPTS_U5U6.md`, `research/T17/axioms_u5u6.lean`, status in `research/T17/T17_SPLIT.md`
U5/U6, report `research/T17/REPORT_385.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.CorrectionDeriv NSFormalization.Section3.T17.ForceDeriv` (0 errors), `lake env lean` on modules / probe /
axioms file; `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T17/REPORT_385.md`.
