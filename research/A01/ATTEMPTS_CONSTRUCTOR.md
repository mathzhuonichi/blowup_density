# Lane 158 resumed — current result

The earlier notes below are historical. The resumed result supersedes their
`m≤q−2` restriction and their claim that no time-continuity rung is closable.

## Positive

- Reused `word_descent_ae_top` in the weak-derivative induction: every `m≤q+1`
  now yields the actual candidate slice datum. The zero-instance audit exercises
  the top order `q=6, m=7`.
- Chose a descended ordinary `L²` field per time and proved the resulting word path
  continuous by reflecting continuity through the isometric `ordinaryLift`.
  This does not require time smoothness or a jointly smooth representative.

## Negative / remaining

- Continuous derivative-word paths are not automatically the exact c8 statement:
  it uses the angular `RealVectorSobolev m` norm. The continuity norm bridge is not
  proved here. Neither are time derivatives, compatible all-order regularity on
  one horizon, or continuation from `Icc 0 S` to a strictly larger horizon.
- Corrected the horizon row (a larger numeric bound does not extend the solution),
  removed the unsupported `representative_ae` discharge of `hslice`, and retained
  all local-theory conclusions in the `CarrierConstructorFull` research target.
- Lean code is written by the assigned Astra low writer; all Lean execution is
  delegated to the Luna high compiler, with no Lean command run by this writer.

## Resumed verification

First Luna build (`tmp/compile_158_module_current_20260915.log`) failed in two
elaboration details: `Fin.cons` needed an explicit nondependent result type
`Fin (n+1) → Fin 3`, and the empty spatial word required a `Subsingleton.elim`
function equality before reducing to `value`. Both are corrected. Luna's repeat module build succeeded (exit 0, 9984 jobs;
`tmp/compile_158_module_fixed_20260915.log`). Axiom audit and both top-order consumers passed (exit 0;
`tmp/probe_158_axioms_current_20260915.log`): the four module exports and two
non-vacuity declarations use only `propext`, `Classical.choice`, `Quot.sound`.
The full-target consumer probe's first attempts stopped at missing
`SliceWiring.olean`, then `Horizon.olean`, before checking its source.
After Luna built those imports, both remaining probes passed:

- `tmp/probe_158_ctor_full_final_20260915.log`: exit 0;
  `rows_from_constructor_full` uses the standard three axioms.
- `tmp/probe_158_ctor_datum_final_20260915.log`: exit 0;
  both D01/A02 datum compatibility declarations use the standard three axioms.

All requested lane-158 checks have passed. No Lean command was executed by the
writer. The earlier missing-import failures are environment history, not
unresolved proof failures.

---

# Historical run — 2026-09-14, before the 2026-09-15 resume

# ATTEMPTS — lane 158 (constructor units B1/B2 split + first S piece)

Task: split the mild ⇒ classical carrier constructor `CarrierConstructor q ν S`
(`research/A01/probes/rev157_constructor_loop.lean:33-40`) field by field over `ClassicalSolutionR`,
and prove the cheapest closable S piece.  Split table = `research/A01/CONSTRUCTOR_SPLIT.md`.

## Proved (positive)

* **`ConstructorPieces.exists_isSobolevDatum_slice_of_cylinder`** (S, DONE, 3-axiom).  The
  datum-existence half of the `sobolev` field (c8/B2), supplied purely from the cylinder pair
  `(u, U, hu, hU)` and a candidate `velocity` with `hslice`, for every order `m ≤ q−2` and every
  `t ∈ Icc 0 S`.  One term: `exists_isSobolevDatum_m_of_ae m (U t) _ (hslice t)
  (hasWeakDerivsL2_of_cylinder (u t) (fun θ => hu θ t) (U t) (hU t) m hm)`.  Both the `A02.IsSobolevDatum`
  and `D01.IsSobolevDatum` targets close identically (defeq; probe `research/A01/probes/ctor158_datum.lean`).
  Non-vacuous on `u=U=velocity=0` (`research/A01/axioms_constructor_pieces.lean`,
  `nonvacuous_datum_slice`).

## Design decisions / what was tried

* **Chose c8-per-t-datum as the S piece, not c6 or the horizon.**  Candidate S pieces the brief listed:
  * *horizon `T := S+1` + c2 bookkeeping* — genuinely trivial (`by linarith`/`positivity`) but too
    content-free to stand as "the" first piece; folded into the table (T/horizon and c2 rows) instead
    of a standalone lemma (avoid over-engineering).
  * *c6 divergence a.e.* — **not closable**: C1b-c6 (`C1B_SPLIT.md`) is a real-analysis **gap** (descend
    `value 1 (u t) ∈ divergenceFreeSpace` through `ordinaryLift` to `spatialDivergence (⇑(U t)) = 0`);
    the pointwise `ClassicalSolutionR.divergence` additionally needs `velocity`'s continuity (c3). Not S.
  * *c8 per-t datum existence* — **closable**: the C1b-m-D chain is fully closed (lane 132/140), so the
    supply-side per-t datum is one `exact`. Picked this — it is the cheapest piece producing real
    content and is a true *constructor* obligation (supply side), unlike lane 157's consumer-side
    `isSobolevDatum_ordinary_of_hslice`.

* **`value 1 (0) = 0` in the non-vacuity.**  `simp` alone left `0 = value 1 0` (it reduced
  `ordinaryLift 0` but not `value 1 0`); `simp [value]` unfolds `value` to `(0).val (emptyWord q)` and
  closes it. Recorded because `value`/`ordinaryLift` have no bundled `map_zero` simp lemma exposed.

* **`hslice` for zeros.**  `(fun x => (0:SpaceTimeField)(↑t,x)) =ᵐ ⇑(0:L2)`: `simp` reduces the LHS to
  `fun x => 0` but does **not** rewrite `↑(0:L2)`; `simpa using (Lp.coeFn_zero …).symm` fails on a
  `0` vs `fun x => 0` normal-form mismatch. Working proof:
  `simp only [ContinuousMap.zero_apply]; filter_upwards [Lp.coeFn_zero …] with x hx; rw [hx]; rfl`.
  (`simp [hx]` closes it too but flags `hx` unused — the linter sees `Lp.coeFn_zero` as a simp lemma;
  `rw [hx]; rfl` is warning-free.)

## Negative / fidelity findings (recorded in the split table)

* **The `CarrierConstructor` interface is under-specified for its own proof.**  As written it takes only
  `hU` (lift compatibility) and quantifies over all `(u,U)`; but B2's datum needs **angle invariance**
  `hu` (`hasWeakDerivsL2_of_cylinder`'s hypothesis) and the momentum/pressure fields need the **Duhamel
  equation** — both output by `localTheory_on_prescribed_horizon` but absent from `CarrierConstructor`.
  So the constructor must be proved as a corollary consuming `localTheory_on_prescribed_horizon`
  directly (the shape `rows_from_constructor` destructures), not at the stated generality. Flagged in
  `CONSTRUCTOR_SPLIT.md` §0.

* **c3 (`velocity_smooth`) is not closable and has no cheap sub-piece.**  Neither vendor representative
  is jointly smooth: `EulerMeanSmoothRepresentative.representative (U t) hu_t` is spatially `C^∞` but
  `Classical.choose`-per-`t` (no joint continuity) and needs an unavailable `SmoothOrbit` witness;
  `EulerSobolevPointEvaluation.representative 1 (u t)` is only `C⁰` spatial, on the cylinder, with joint
  continuity but **no time derivative** (Paper1 `continuous_pointwise_representative` = `C⁰`-joint;
  `differentiated_path_pointwise_continuous` = `C¹`-joint from `H⁴`). The θ=0-slice of
  `representative 1 (u t)` is therefore **not jointly smooth**. Time-smoothness must come from the
  Duhamel bootstrap (T1) over A2/A2b/A3. Full analysis in `CONSTRUCTOR_SPLIT.md` §2.

## Commands

* `lake build NSFormalization.Section4.A01.ConstructorPieces` → `Built … (2.7s)`, exit 0 (only a
  replayed upstream `SchwartzMap.smul_apply` deprecation warning, not from this module).
* `lake env lean …/ConstructorPieces.lean` → silent, exit 0.
* `lake env lean ../research/A01/axioms_constructor_pieces.lean` → both decls
  `[propext, Classical.choice, Quot.sound]`, non-vacuity proved, no warnings.
* `grep sorry/admit/axiom/native_decide/maxHeartbeats/set_option` on module + conformance → no matches.
* `make check` → exit 0 (`test_contract_policy` 13 OK; `check_work_queue` 30 items consistent).
