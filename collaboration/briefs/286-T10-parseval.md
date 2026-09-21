# Lane 286-T10-parseval — vector Parseval on the torus: `parseval_forward` and `parseval_backward` of `TorusDataAPI`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/286-T10-parseval` (git branch `erenup/286-T10-parseval`, based on `origin/erenup/integration-section3` **after** lane 283 landed:
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
  hypotheses). Copy them verbatim as theorem statements; a probe `research/T10/probes/parseval_closes.lean` must show each theorem closes the field
  (`example : <field statement> := <your theorem>`).
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/TorusCube.lean`, `Paper1/Periodic*.lean`,
  `Section4/D01/`, and Mathlib's `Mathlib/Analysis/Fourier/AddCircleMulti.lean`, `Mathlib/Analysis/Fourier/AddCircle.lean`,
  `Mathlib/MeasureTheory/Group/AddCircle.lean`, `Mathlib/Analysis/Normed/Lp/lpSpace.lean`. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]` (`#print axioms`); include a non-vacuity `example` on a concrete field (e.g. the zero field or a
  constant field).

## Goal
Prove:
- `parseval_backward : ∀ z, IsPeriodicSpatial z → MemLp (torusLift z) 2 periodicTorusMeasure → ∃ A : PeriodicSobolev 0, IsPeriodicDatum 0 z A`
  (with the integrability conjunct of amendment 1: `MemLp 2 ⇒ Integrable` on a probability space — `MemLp.integrable`; and `periodicTorusMeasure`
  is a probability measure: find or prove the instance).
- `parseval_forward : ∀ z (A : PeriodicSobolev 0), IsPeriodicDatum 0 z A → MemLp (torusLift z) 2 periodicTorusMeasure → ‖A‖ₑ = eLpNorm (torusLift z) 2 periodicTorusMeasure`.
Route: Mathlib's `UnitAddTorus.mFourierBasis : HilbertBasis (d → ℤ) ℂ (Lp ℂ 2 (volume : Measure (UnitAddTorus d)))` (in
`Mathlib/Analysis/Fourier/AddCircleMulti.lean`; check the exact name and the lemma identifying `mFourierBasis.repr f n` with `mFourierCoeff f n` for
`f : Lp ℂ 2`, and `HilbertBasis.repr` is an isometry onto `lp 2`, so `‖repr f‖ = ‖f‖`). Apply it to each complex component
`(torusLift z) · i` as an `Lp` element (`MemLp.toLp`), get the ℓ² coefficient sequence with `‖·‖² = ‖component‖²_{L²}`, assemble the three
components into `PeriodicVectorData = WithLp 2 (Fin 3 → lp …)` (`PiLp` norm: `‖A‖² = ∑ i, ‖A i‖²`), prove reality
(`A i (-k) = star (A i k)` from `z` real-valued: `mFourierCoeff` at `-k` of a real function is the conjugate — prove via `integral_conj` and the
character identity), and relate `∑ i, ‖component i‖²_{L²}` to `eLpNorm (torusLift z) 2` (`EuclideanSpace` norm: `‖v‖² = ∑ i, ‖v i‖²`,
`eLpNorm` as `(∫⁻ ‖·‖ₑ^2)^{1/2}`, `lintegral` of a finite sum). The local model for continuous functions is
`NSFormalization.Paper1.hasSum_sq_periodicFourierCoeff` (`Paper1/TorusCube.lean:87`) — read its proof and generalize to `MemLp 2`.
Use `ENNReal`/`ℝ≥0∞` carefully: state and prove the real-valued identity first, then convert (`ENNReal.ofReal`, `enorm_eq_ofReal_norm`, `eLpNorm_eq_lintegral_rpow_enorm`).

## Deliverables
1. New module `formalization/NSFormalization/Section3/T10/Parseval.lean` (namespace `NSFormalization.Section3.T10`) with the theorems above;
   the probe `research/T10/probes/parseval_closes.lean`; conformance `research/T10/axioms_parseval.lean` (`#print axioms` of every theorem).
2. Records `research/T10/ATTEMPTS_PARSEVAL.md` (paths tried, exact error text of anything that failed, any residual named hypothesis with its exact
   statement and why it is true mathematically); report `research/T10/REPORT_286.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.Parseval` (0 errors), `lake env lean` on the module, the probe and
the axioms file (0 output apart from the `#print axioms` lines), `make check` from the worktree root.

## Report
Commit on your branch (`[286-T10] Parseval`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
