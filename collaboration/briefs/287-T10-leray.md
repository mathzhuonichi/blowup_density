# Lane 287-T10-leray — the periodic Leray projector fields `leray_exists_contraction` and `leray_projector` of `TorusDataAPI`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/287-T10-leray` (git branch `erenup/287-T10-leray`, based on `origin/erenup/integration-section3` **after** lane 283 landed:
it contains the canonical T10 module `formalization/NSFormalization/Section3/T10/PeriodicData.lean` (namespace `NSFormalization.Section3.T10`)
and the probe `research/T10/probes/api_on_canonical.lean`, which states the full `TorusDataAPI` over that module). Read `CLAUDE.md` (Lean
environment; hard rules), `research/T10/Spec.lean` docstrings for the fields below, `research/T10/RECONCILIATION.md` §5 (lead amendment 1:
`IsPeriodicDatum` carries `Integrable (torusLift z) periodicTorusMeasure`; `parseval_forward` carries `MemLp … 2`), `research/T10/CANONICAL.md`
(which declarations are reused from `formalization/NSFormalization/Paper1/TorusCube.lean`), `research/T10/COMPARISON.md` §"Needs a lemma", and the
top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no
  edits to existing modules (in particular not to `PeriodicData.lean` — if a definition there blocks you, isolate the exact statement you need as one
  named hypothesis, prove everything else, and report it; do not weaken the target statements).
- The target statements are **exactly** the corresponding fields of `research/T10/probes/api_on_canonical.lean` (same quantifier order, same
  hypotheses). Copy them verbatim as theorem statements; a probe `research/T10/probes/leray_closes.lean` must show each theorem closes the field
  (`example : <field statement> := <your theorem>`).
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/TorusCube.lean`, `Paper1/Periodic*.lean`,
  `Section4/D01/`, and Mathlib's `Mathlib/Analysis/Fourier/AddCircleMulti.lean`, `Mathlib/Analysis/Fourier/AddCircle.lean`,
  `Mathlib/MeasureTheory/Group/AddCircle.lean`, `Mathlib/Analysis/Normed/Lp/lpSpace.lean`. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]` (`#print axioms`); include a non-vacuity `example` on a concrete field (e.g. the zero field or a
  constant field).

## Goal
Prove:
- `leray_exists_contraction : ∀ s (A : PeriodicSobolev s), ∃ B : PeriodicSobolev s, IsPeriodicLerayDatum A B ∧ ‖B‖ ≤ ‖A‖ ∧ IsSolenoidalPeriodicDatum B`.
  Route (pure ℓ² algebra, no analysis): `B i k := periodicLeray s A i k`. Show (a) for each `k` the map `v ↦ v - k (k·v)/|k|²` on `Fin 3 → ℂ` is the
  orthogonal projection onto `k^⊥` and is a contraction coordinatewise-summed: `∑ i, ‖B i k‖² ≤ ∑ i, ‖A i k‖²` (expand; the cross term cancels, or use
  Cauchy–Schwarz `|k·v|² ≤ |k|² ∑|v_i|²`); (b) hence each `fun k => B i k` is in `lp 2` (`Memℓp` via summable domination: `‖B i k‖² ≤ ∑ j ‖A j k‖²`,
  `memℓp_gen`/`Memℓp.of_norm_le`-style lemmas; check `Mathlib/Analysis/Normed/Lp/lpSpace.lean` for the exact API — the sum over `k` of the RHS is
  finite since each `A j ∈ lp 2`); (c) `‖B‖ ≤ ‖A‖` in `WithLp 2 (Fin 3 → lp _ 2)` from the termwise bound (`PiLp.norm_sq_eq_of_L2`, `lp.norm_rpow_eq_tsum`,
  `ENNReal.toReal`-free real route); (d) reality: the symbol is real and even in `k` (`(-k) i * ∑ j (-k) j v j / |−k|² = k i (∑ k j v j)/|k|²`, and
  `star` commutes with real scalars), so `B ∈ realPeriodicSubmodule`; (e) solenoidal: `∑ j, periodicDerivativeSymbol j k * B j k = 0` for every `k`
  (`k = 0`: symbol is `0`; `k ≠ 0`: `∑ j k_j (v_j - k_j (k·v)/|k|²) = k·v - |k|² (k·v)/|k|² = 0`; `|k|² ≠ 0` as a sum of squares of integers not all zero —
  cast carefully `((∑ j, (k j : ℝ)^2 : ℝ) : ℂ)`).
- `leray_projector : ∀ s (A B C : PeriodicSobolev s), IsPeriodicLerayDatum A B → IsPeriodicLerayDatum B C → C = B` (idempotence coordinatewise:
  `periodicLeray s (periodicLeray s A) i k = periodicLeray s A i k`, then `Subtype.ext` + `lp` extensionality).
Also export `periodicLeray_of_solenoidal : IsSolenoidalPeriodicDatum A → ∀ i k, periodicLeray s A i k = A.1 i k` (every solenoidal datum is fixed) —
the "needs a lemma" item 7.

## Deliverables
1. New module `formalization/NSFormalization/Section3/T10/Leray.lean` (namespace `NSFormalization.Section3.T10`) with the theorems above;
   the probe `research/T10/probes/leray_closes.lean`; conformance `research/T10/axioms_leray.lean` (`#print axioms` of every theorem).
2. Records `research/T10/ATTEMPTS_LERAY.md` (paths tried, exact error text of anything that failed, any residual named hypothesis with its exact
   statement and why it is true mathematically); report `research/T10/REPORT_287.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.Leray` (0 errors), `lake env lean` on the module, the probe and
the axioms file (0 output apart from the `#print axioms` lines), `make check` from the worktree root.

## Report
Commit on your branch (`[287-T10] Leray`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
