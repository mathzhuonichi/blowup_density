# ATTEMPTS — lane 102, A04 unit G1, SL5 rows 5b / 5f / 5g

Module: `formalization/NSFormalization/Section4/A04/NonlinearColumns.lean`.
Axioms: `research/A04/axioms_sl5_columns.lean` (all 7 public decls = `[propext, Classical.choice, Quot.sound]`).

One bounded unit: three SL5 rows (column data 5b, gradient norm 5f, outer norm 5g), all rated S/S–M
and independent of 5a/5c/5h.  This worktree branched from `erenup/integration` **after** PR #94, so
lane 088's `LaplacianAssembly.lean` **is present** and reused directly (contrast lane 095's worktree,
where it was absent — see `REVIEW_SL5.md` §4).

## Route that worked

### 5b — column data (`exists_outerColumn_datum`, `exists_outerColumn_datum_succ`)

`outerColumn z z j = fun x => (z x j) • z x` is the `j`-th column `W_j = u_j·u`.  Existence of an
order-`s` datum is `A03.exists_sobolevDatum : sobolevENorm s z ≠ ⊤ → ∃ A, IsSobolevDatum s z A`; the
whole content is the finiteness `sobolevENorm s (outerColumn z z j) ≠ ⊤`.

Chosen bound: `A03.le_columnsSobolevENorm s (outerColumn z z) j` (each column ≤ the Frobenius
assembly `columnsSobolevENorm = outerSobolevENorm`) composed with `A03.outerProductTame`
(`outerSobolevENorm s z z ≤ C · ‖z‖_{H²} · ‖z‖_{H^s}`).  The RHS is `≠ ⊤` because both `sobolevENorm 2 z`
and `sobolevENorm s z` are, the former from `A03.sobolevENorm_two_le`, the latter from `hz.2`.

- Hypothesis stated exactly as the bound needs: `exists_outerColumn_datum` takes `MemHmVector m z`
  (= `MemLp z 2 ∧ sobolevENorm (m:ℝ) z ≠ ⊤`) plus `2 ≤ m`.  (The task named `tameProductVector` as the
  finiteness source; `outerProductTame` is cleaner because its RHS names only `‖z‖_{H²}` and `‖z‖_{H^m}`,
  whereas `tameProductVector` would also drag in the two scalar-component norms.  Both route through
  `sobolevENorm_two_le` for the `H²` factor, so no extra cost.)  The order-`m` version needs no order
  cast (`(m:ℝ) = ((m:ℕ):ℝ)` definitionally in these statements).

- **`_succ` is a two-line corollary (post-review simplification, review finding 3).**  Rather than
  re-run the finiteness chain at order `m+1`, `exists_outerColumn_datum_succ` calls
  `exists_outerColumn_datum (m+1) (by omega) hz j` — its class hypothesis is already `MemHmVector (m+1) z`
  — then transports the resulting order-`((m+1:ℕ):ℝ)` datum to `(m:ℝ)+1` (equal only up to `Nat.cast_succ`,
  not defeq) with lane 088's `A04.isSobolevDatum_castOrder (cast_mid_order m)`; witness
  `castOrder (cast_mid_order m) A`.  Because the only numeric need is `2 ≤ m+1`, the `_succ` hypothesis is
  **weakened to `1 ≤ m`** (a strictly stronger lemma than the SL5 regime `2 ≤ m`; 5c still consumes it
  under `2 ≤ m`).  The original stand-alone finiteness proof at `m+1` compiled fine too — this is a
  de-duplication, not a fix.

### 5f — gradient norm (`sqrt_sum_norm_sq_derivDatumStep_eq`, `…_slice`)

`A04.gradientSobolevENorm_toReal_sq_eq_datum_sum m hA'` (`LaplacianDatum.lean:130`) gives
`(gradientSobolevENorm (m:ℝ) Z.field).toReal ^ 2 = ∑ j, ‖WithLp.toLp 2 (fun i => angularDirectionalDerivativeReal ((m:ℝ)+1) e_j (A' i))‖²`.

- **`derivDatumStep` is the same term (checked).**  `derivDatumStep m j A'` unfolds to exactly the
  `WithLp.toLp 2 (fun i => angularDirectionalDerivativeReal ((m:ℝ)+1) e_j (A' i))` summand.  I did not
  restate 5f with the explicit `toLp` form: instead the `have hsum : ∑ ‖derivDatumStep m j A'‖² = (…).toReal²`
  is discharged by `(gradientSobolevENorm_toReal_sq_eq_datum_sum m hA').symm` **through defeq** — the fact
  that this `have` typechecks *is* the "check with a `rfl` example" the brief asked for.  Then
  `Real.sqrt_sq ENNReal.toReal_nonneg` strips the square.

- **Slice bridge is `rfl`, stated as a `have`.**  For the slice form, repackage the slice as
  `Z : SmoothL2Field Space := ⟨fun x => u (t,x), hsl.1, hsl.2⟩` (as `inner_datum_laplacian_le'` does), then
  `have hg : gradientSobolevNormAt (m:ℝ) u t = (gradientSobolevENorm (m:ℝ) Z.field).toReal := rfl`.
  `gradientSobolevNormAt s u t := (gradientSobolevENorm s (fun x => u (t,x))).toReal` and `Z.field` reduces
  to `fun x => u (t,x)`, so `rfl` holds.  Per lane 088's heartbeat warning, inlining this defeq into an
  `exact` would unfold `gradientSobolevENorm → columnsSobolevENorm → sobolevENorm` (an `⨅` over a subtype
  of data) and burn ~200000 heartbeats at `isDefEq`; the named `have` avoids it.  Build cost of the module
  was 2.9s, no `maxHeartbeats` bump.

### 5g — outer norm (`sqrt_sum_norm_sq_columnData_eq`, `columnsSobolevENorm_toReal_sq_eq_sum`, `outerSobolevENorm_toReal_sq_eq_sum`)

Mirror of `A04.gradientSobolevENorm_toReal_sq_eq_sum` (`LaplacianDatum.lean:96`) but for a **general**
column family `T : Fin 3 → Space → Space`: `columnsSobolevENorm_toReal_sq_eq_sum` proves
`(columnsSobolevENorm s T).toReal² = ∑ j, (sobolevENorm s (T j)).toReal²` under `∀ j, sobolevENorm s (T j) ≠ ⊤`,
by the identical `ENNReal.toReal_rpow` / `Real.rpow_mul` / `ENNReal.toReal_sum` / `ENNReal.toReal_pow`
arithmetic.  `outerSobolevENorm_toReal_sq_eq_sum` is the `outerColumn` specialization (`rfl`-level, since
`outerSobolevENorm s z z := columnsSobolevENorm s (outerColumn z z)`).

Then `sqrt_sum_norm_sq_columnData_eq`: given data `C_j` of the columns, `sobolevENorm_eq (hC j)`
identifies `sobolevENorm (m:ℝ) (outerColumn z z j) = ‖C_j‖ₑ`, so `(…).toReal = ‖C_j‖` (`toReal_enorm`) and
finiteness (`enorm_ne_top`) is **free** — no `tameProductVector m` needed once the data are supplied.
Delivered as **equality**, stronger than the `≤` the brief allows.

> **Name-resolution note (review finding 1).**  Inside `namespace NSFormalization.Section4.A04` the bare
> `sobolevENorm_eq` resolves to `A04.sobolevENorm_eq` (`Forcing.lean:126`, reachable transitively), **not**
> to the `A03.sobolevENorm_eq` I `open`ed — the two are statement- and proof-identical (`Forcing.lean:122`).
> So the `open A03 (…)` entry for `sobolevENorm_eq` was shadowed and unused; it has been dropped from the
> `open` list and the docstring attributions corrected to `A04.sobolevENorm_eq`.  No mathematical change.

## Failed / rejected approaches

1. **`tameProductVector` for 5b finiteness** (the brief's first suggestion).  Its RHS is
   `C · (‖z_j‖_{H²}·‖z‖_{H^s} + ‖z‖_{H²}·‖z_j‖_{H^s})`, four norms to prove `≠ ⊤` (two of them scalar
   component norms via `scalarSobolevENorm_component_le`).  `outerProductTame` + `le_columnsSobolevENorm`
   needs only two vector norms, so I used that.  Not a compile failure, a simplification choice.

2. **`rw [← gradientSobolevENorm_toReal_sq_eq_datum_sum …]` directly on the goal** (5f).  Rejected before
   trying: the goal carries `∑ ‖derivDatumStep m j A'‖²`, the lemma's RHS carries the `WithLp.toLp` form;
   `rw` matches up to reducible defeq and `derivDatumStep` is a plain `def` (not `@[reducible]`), so the
   rewrite is not guaranteed to fire.  Routing through a `have hsum := (…).symm` (which is checked at full
   defeq) and then `rw [hsum]` sidesteps the question entirely.

3. **Restating 5f with the literal `toLp 2 (fun i => angularDirectionalDerivativeReal … (A' i))` term**
   (the brief's fallback if `derivDatumStep` were a different term).  Unnecessary — see 5f "same term"
   above; `derivDatumStep` **is** that term, so the cleaner `derivDatumStep`-flavoured statement (which is
   what 5h will consume, matching `norm_sq_derivDatumStep`/`inner_datum_laplacian`) is the one delivered.

## MAINT note for the SIMP lane (review finding 2, do NOT move now)

`columnsSobolevENorm_toReal_sq_eq_sum` is a statement purely about `A03.columnsSobolevENorm` with no A04
content, and its ~10-line `ENNReal.toReal` body is copied verbatim from `LaplacianDatum.lean:96`
(`gradientSobolevENorm_toReal_sq_eq_sum`).  It is the strict generalization (096 = the `partialDeriv`
instance), but currently lives downstream, a mild layering inversion.  The SIMP lane should move it into
`A03/OuterTameProduct.lean` right after `le_columnsSobolevENorm`, collapse `gradientSobolevENorm_toReal_sq_eq_sum`'s
body to `columnsSobolevENorm_toReal_sq_eq_sum hfin` (one line), and have `NonlinearColumns` cite it from A03
(net ≈ −20 lines).  Left in place this lane to keep the diff to new files only.

## What is NOT closed here (out of scope for this lane)

5a (pointwise divergence form, M), 5c (`N = ∑_j derivDatumStep m j (castOrder … B_j)`, S–M), 5h (the calc
assembly, M).  5d/5e/5i are already DONE (lane 095, `NonlinearPairing.lean`).  This lane closes only the
three column/norm rows.
