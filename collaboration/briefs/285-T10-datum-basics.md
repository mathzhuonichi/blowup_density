# Lane 285-T10-datum-basics — the coefficient-side fields `datum_unique`, `datum_real`, `meanZero_datum` of `TorusDataAPI`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/285-T10-datum-basics` (git branch `erenup/285-T10-datum-basics`, based on `origin/erenup/integration-section3` **after** lane 283 landed:
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
  hypotheses). Copy them verbatim as theorem statements; a probe `research/T10/probes/datum_basics_closes.lean` must show each theorem closes the field
  (`example : <field statement> := <your theorem>`).
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/TorusCube.lean`, `Paper1/Periodic*.lean`,
  `Section4/D01/`, and Mathlib's `Mathlib/Analysis/Fourier/AddCircleMulti.lean`, `Mathlib/Analysis/Fourier/AddCircle.lean`,
  `Mathlib/MeasureTheory/Group/AddCircle.lean`, `Mathlib/Analysis/Normed/Lp/lpSpace.lean`. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]` (`#print axioms`); include a non-vacuity `example` on a concrete field (e.g. the zero field or a
  constant field).

## Goal
Prove:
- `datum_unique : ∀ s z (A B : PeriodicSobolev s), IsPeriodicDatum s z A → IsPeriodicDatum s z B → A = B` (`Subtype.ext` + `lp`/`WithLp` extensionality:
  both are the same explicit sequence).
- `datum_real : ∀ s z A, IsPeriodicDatum s z A → ∀ i k, A.1 i (-k) = star (A.1 i k)` (this is `A.2`, the membership in `realPeriodicSubmodule` — check
  what `A.1 i (-k)` unfolds to and close it).
- `meanZero_datum : ∀ s z A, IsPeriodicDatum s z A → ∃ B : PeriodicSobolev s, IsPeriodicDatum s (meanZeroPartT z) B ∧ B ∈ meanZeroPeriodicSobolev s`.
  Route: `B := A` with the zero mode of every component set to `0` (show it is still in `lp 2` — a finite modification, e.g. `A - (zero-mode part)` using
  `lp.single`; and still in `realPeriodicSubmodule`). Fourier coefficients of `meanZeroPartT z = z - meanT z`: for the constant `c := meanT z`,
  `periodicFourierCoeff (fun _ => (c i : ℂ)) k = if k = 0 then c i else 0` (Mathlib: `UnitAddTorus.mFourierCoeff` of a constant — look for
  `mFourierCoeff_const`/`mFourier_zero`/orthogonality `integral_mFourier`; prove it if absent); linearity of `mFourierCoeff` under subtraction needs
  the **integrability conjunct** of `IsPeriodicDatum` (amendment 1) — `torusLift` of a component is integrable because the vector lift is
  (`Integrable.norm`-type bound or `PiLp`/`EuclideanSpace` coordinate projection is a bounded linear map). At `k = 0`: coefficient of `z_i` minus
  `c i = meanT z i` is `0` because `meanT z = ∫ torusLift z` and the coordinate of a Bochner integral is the integral of the coordinate
  (`integral` commutes with continuous linear maps, `ContinuousLinearMap.integral_comp_comm`).
Also prove `IsPeriodicDatum.integrable_component` (each complex component `fun x ↦ ((z x i : ℝ) : ℂ)` lifted is integrable) as a reusable lemma.

## Deliverables
1. New module `formalization/NSFormalization/Section3/T10/DatumBasics.lean` (namespace `NSFormalization.Section3.T10`) with the theorems above;
   the probe `research/T10/probes/datum_basics_closes.lean`; conformance `research/T10/axioms_datum_basics.lean` (`#print axioms` of every theorem).
2. Records `research/T10/ATTEMPTS_DATUM_BASICS.md` (paths tried, exact error text of anything that failed, any residual named hypothesis with its exact
   statement and why it is true mathematically); report `research/T10/REPORT_285.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.DatumBasics` (0 errors), `lake env lean` on the module, the probe and
the axioms file (0 output apart from the `#print axioms` lines), `make check` from the worktree root.

## Report
Commit on your branch (`[285-T10] DatumBasics`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
