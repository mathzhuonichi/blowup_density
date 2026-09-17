# Lane 284-T10-physical-bridge — the physical-layer fields of `TorusDataAPI`: `torusLift_injective`, `torusLift_surjective`, `mean_decomposition`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/284-T10-physical-bridge` (git branch `erenup/284-T10-physical-bridge`, based on `origin/erenup/integration-section3` **after** lane 283 landed:
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
  hypotheses). Copy them verbatim as theorem statements; a probe `research/T10/probes/physical_bridge_closes.lean` must show each theorem closes the field
  (`example : <field statement> := <your theorem>`).
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/TorusCube.lean`, `Paper1/Periodic*.lean`,
  `Section4/D01/`, and Mathlib's `Mathlib/Analysis/Fourier/AddCircleMulti.lean`, `Mathlib/Analysis/Fourier/AddCircle.lean`,
  `Mathlib/MeasureTheory/Group/AddCircle.lean`, `Mathlib/Analysis/Normed/Lp/lpSpace.lean`. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]` (`#print axioms`); include a non-vacuity `example` on a concrete field (e.g. the zero field or a
  constant field).

## Goal
Prove the three fields that live entirely on the physical layer (unit-periodic fields on ℝ³ and their lifts to `UnitAddTorus (Fin 3)`):
- `torusLift_injective : ∀ z w : SpatialField, IsPeriodicSpatial z → IsPeriodicSpatial w → torusLift z = torusLift w → z = w`.
  Route: every `x : Space` differs from the `(0,1]³` representative of its class (`UnitAddTorus.measurableEquivPiIoc 0` applied to the quotient
  image of `x`) by an integer vector, and `IsPeriodicSpatial` (invariance under `+ coordinateVector i`) gives invariance under all of `ℤ³` by
  induction on each coordinate (`Int.induction_on`, both signs). Prove and export that lemma (`periodic_shift_int : IsPeriodicSpatial z → ∀ x (k : Fin 3 → ℤ), z (x + ∑ i, (k i : ℝ) • coordinateVector i) = z x`, or the equivalent with `EuclideanSpace` coordinates) — later lanes need it.
- `torusLift_surjective : ∀ Z : PeriodicTorus → Space, ∃ z, IsPeriodicSpatial z ∧ torusLift z = Z` (take `z x := Z (quotient image of x)`).
- `mean_decomposition : ∀ z, IsPeriodicSpatial z → Integrable (torusLift z) periodicTorusMeasure → (∀ x, constantPartT z x + meanZeroPartT z x = z x) ∧ IsMeanZeroT (meanZeroPartT z)`
  (`meanT z = ∫ y, torusLift z y ∂periodicTorusMeasure`; use that `periodicTorusMeasure` is a probability measure — find or prove the instance for
  `UnitAddTorus (Fin 3)`; `torusLift (z - c) = torusLift z - c` pointwise).
Also prove the bridge lemmas the other T10 lanes will want: `torusLift_apply_of_periodic` (`torusLift z (quot x) = z x` for periodic `z`),
`isPeriodicSpatial_torusLift_comp`, and `meanT_const`.

## Deliverables
1. New module `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean` (namespace `NSFormalization.Section3.T10`) with the theorems above;
   the probe `research/T10/probes/physical_bridge_closes.lean`; conformance `research/T10/axioms_physical_bridge.lean` (`#print axioms` of every theorem).
2. Records `research/T10/ATTEMPTS_PHYSICAL_BRIDGE.md` (paths tried, exact error text of anything that failed, any residual named hypothesis with its exact
   statement and why it is true mathematically); report `research/T10/REPORT_284.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.PhysicalBridge` (0 errors), `lake env lean` on the module, the probe and
the axioms file (0 output apart from the `#print axioms` lines), `make check` from the worktree root.

## Report
Commit on your branch (`[284-T10] PhysicalBridge`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
