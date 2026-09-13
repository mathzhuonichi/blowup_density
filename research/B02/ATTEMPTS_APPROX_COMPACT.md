# B02 `approxCompactHomogeneous` — attempts (lane 110)

Field 8 (`research/B02/REMAINING_SPLIT.md` row 8): `approxCompactHomogeneous`
(`Spec.lean:607`) + the export `SeparatedCompactHomogeneousDense` (`Spec.lean:653`).
All in **new** file `formalization/NSFormalization/Section4/B02/ApproxCompact.lean`.
Conformance: `research/B02/axioms_approx_compact.lean`.

## Route that worked

Three parts, each gating the next; all compiled.

* **Part 1 — `bochnerDatumENorm_separatedPath_sub_le`** (`04-whole-space.tex:253-255`,
  content on line 254 `Σ_j |E_j|^{1/q}‖b_j−h_j‖_X`: fixed time factors, differing
  spatial vectors — NOT `:257`, which is the display opening line 258's
  `‖1_E − φ‖·‖h‖` time-factor variant), realization-independent, no `MemBochnerDatum`:
  `bochnerDatumENorm q s (separatedPath φ A - separatedPath φ A') ≤ ∑ j, eLpNorm (φ j) q forceTimeMeasure * ‖A j - A' j‖ₑ`
  under only `1 ≤ q` and `∀ j, AEStronglyMeasurable (φ j) forceTimeMeasure`.
  - `bochnerDatumENorm q s G` unfolds (one `simp only [bochnerDatumENorm]`, the
    `def` from `B01/Compact.lean:75` = `D01`'s) to **`eLpNorm G q forceTimeMeasure`**;
    `forceTimeMeasure = positiveTimeMeasure = volume.restrict (Ioi 0)`. It is an
    `eLpNorm`, NOT an `∫⁻`.
  - `separatedPath φ A - separatedPath φ A' = fun t => ∑ j, φ j t • (A j - A' j)`
    (`funext`; `Pi.sub_apply`; `Finset.sum_sub_distrib`; `smul_sub`), then
    `= ∑ j, (fun t => φ j t • (A j - A' j))` (`Finset.sum_apply`).
  - `MeasureTheory.eLpNorm_sum_le` (`TriangleInequality.lean:127`) over `Fin J`
    with `AEStronglyMeasurable` summands via `(hφ j).smul_const _`
    (`AEStronglyMeasurable.smul_const`, `AEStronglyMeasurable.lean:371`).
  - The missing constant-vector shape is proved as a standalone lemma
    **`eLpNorm_smul_const`**: `eLpNorm (fun t => f t • v) q μ = eLpNorm f q μ * ‖v‖ₑ`
    for `f : ℝ → ℝ`, `v : E` a real normed space, **all `q` including `⊤`**.
    Route: `eLpNorm_congr_enorm_ae` (`LpSeminorm/Basic.lean:401`, allows different
    codomains) reduces to `‖f t • v‖ₑ = ‖((‖v‖ : ℝ) • f) t‖ₑ` pointwise, both
    equal `‖f t‖ₑ * ‖v‖ₑ` via `enorm_smul` (twice) + `enorm_norm`; then
    `MeasureTheory.eLpNorm_const_smul` (`SMul.lean:110`, equality for a scalar
    constant times a function) + `enorm_norm`.

* **Part 2 — `separatedCompactHomogeneousDense`** on `1 ≤ q`, `q ≠ ⊤`, `SplitRange s`:
  - **`ℝ≥0∞` bookkeeping.** Reduce the target `η` to `η'' := min η 1` (`≤ η`,
    `> 0`, `≠ ⊤`); prove `< η''`, then `lt_of_lt_of_le … hη''_le`. This removes the
    `η = ⊤` case entirely (no need to reason about a possibly-infinite target).
    Split `η'' = η₁ + η₁`, `η₁ := η''/2` (`ENNReal.half_pos`, `ENNReal.add_halves`,
    `η₁ ≠ ⊤` via `ENNReal.div_lt_top`).
  - `temporalApprox q hq1 hqt s b hb η₁ hη₁_pos` gives `J, φ, A'` and
    `bochnerDatumENorm q s (separatedPath φ A' - b) < η₁`.
  - `E_j := eLpNorm (φ j) q forceTimeMeasure` is **finite**:
    `Continuous.memLp_of_hasCompactSupport (p := q) (μ := forceTimeMeasure)`
    (`LpSpace/Indicator.lean:83`; `forceTimeMeasure` is `IsFiniteMeasureOnCompacts`
    via `instIsFiniteMeasureOnCompactsRestrict`), `.eLpNorm_lt_top.ne`. Hence
    `S := ∑ j, E_j ≠ ⊤` (`ENNReal.sum_lt_top`), `S + 1 ≠ ⊤`, `≠ 0`.
  - **Uniform per-fibre tolerance** `η' := η₁ / (S + 1) > 0` (`ENNReal.div_pos`,
    needs `S + 1 ≠ ⊤`, which is exactly why `E_j` finiteness matters — a `⊤`
    would force `η' = 0` and break `spatialApproxHomogeneous`'s `0 < η'`).
  - `choose h H hhs hhc hHdatum hHerr using fun j => spatialApproxHomogeneous s hs (A' j) η' hη'_pos`:
    each `‖H j - A' j‖ₑ < η'`, `H j` the homogeneous datum of the physical `h j`.
  - Part 1 + `Finset.sum_le_sum` (`gcongr` per term) + `Finset.sum_mul` bound the
    replacement error by `S * η' ≤ (S+1) * η' = η₁` (`gcongr` for `S ≤ S+1` via
    `le_self_add`; `ENNReal.mul_div_cancel'` for `(S+1)*(η₁/(S+1)) = η₁`).
  - Triangle: `separatedPath φ H - b = (separatedPath φ H - separatedPath φ A') + (separatedPath φ A' - b)`
    (`sub_add_sub_cancel`), `eLpNorm_add_le` (`1 ≤ q`, both parts
    `AEStronglyMeasurable` via `aestronglyMeasurable_separatedPath` and `hb.1`),
    then `≤ η₁ + … < η₁ + η₁ = η''`.
  - The three structural conjuncts (`MemForceCompact`, `IsHomogeneousPath`,
    `AEStronglyMeasurable`) from `separatedAssembly s hs.1 …` (`SplitRange.1 = -3/2 < s`),
    computed **once**.

* **Part 3 — `approxCompactHomogeneous`**: `CompletedDenseHomogeneous q s S =
  CompletedDenseVia q s (IsHomogeneousPath s) S` (`Data.lean:757`), whose body is
  `∀ b, MemBochnerDatum → ∀ r, 0 < r → ∃ f ∈ S, ∃ D, path f D ∧ AEStronglyMeasurable D … ∧ bochnerDatumENorm q s (D - b) < r`.
  The lane statement is **definitionally equal** to the spec field `Spec.lean:607`
  — NOT literally token-identical (`Spec.lean:607` writes `CompletedDenseHomogeneous`,
  the `Data.lean:752` `abbrev`, and the spec-local `SplitRange`, where the lane uses
  the `formalization/` `CompletedDenseVia` / `IsHomogeneousPath` / `forceClassCompact`
  / `SplitRange` restatements: three token diffs, all defeq). Confirmed by the kernel
  via `example : specApproxCompactHomogeneous = laneApproxCompactHomogeneous := rfl`
  in `research/B02/axioms_approx_compact.lean`.
  Discharged from Part 2 with `f := separatedField φ h`, `D := separatedPath φ H`;
  `hMem : MemForceCompact (separatedField φ h)` is directly the `∈ forceClassCompact`
  proof (`x ∈ {f | p f}` reduces to `p x`).

## Failed approaches / pitfalls (all fixed)

1. **`add_le_add_right hPe _` → non-terminating `whnf` (the big one).**
   In this Mathlib pin, `add_le_add_right (h : a ≤ b) (c)` elaborates to
   **`c + a ≤ c + b`** (addition on the *left*), not `a + c ≤ b + c`. Using it for
   the goal `eLpNorm X + eLpNorm Y ≤ η₁ + eLpNorm Y` forced Lean to unify
   `c + a ≤ c + b` against `a + c ≤ b + c`, i.e. to check `c + a =?= a + c` by
   `whnf`/`isDefEq` — which **unfolds the `eLpNorm` `∫⁻`/`essSup` bodies and does
   not terminate** (timeout even at `maxHeartbeats 2000000`; the whole theorem
   reported `whnf` timeout). Symptom: `(deterministic) timeout at whnf`/`isDefEq`
   at the calc step, plus a `timeout at whnf` at the declaration header.
   **Fix:** `add_le_add hPe le_rfl`, which produces `a + c ≤ b + c` in the exact
   goal orientation — no commutativity, no `eLpNorm` unfolding. Confirmed in
   isolation (`research/B02` scratch): the loop is entirely the orientation
   mismatch on `eLpNorm` terms; plain `ℝ≥0∞` variables just give a fast type
   mismatch, `eLpNorm` terms loop.
2. **`enorm_norm'` vs `enorm_norm`.** `enorm_norm'` is the `@[to_additive]`
   *multiplicative* lemma (`‖‖x‖‖ₑ` over a multiplicative norm); the additive one
   for `ℝ`/`RealVectorSobolev` is **`enorm_norm`**. `rw [enorm_norm']` failed with
   "pattern not found" on a goal that literally displayed `‖‖v‖‖ₑ`.
3. **`enorm_norm` obstruction mis-diagnosed as a `ring` limitation (CORRECTED,
   finding 4-A).** The original entry claimed `ring` "refused on `ℝ≥0∞`" to close
   `‖f t‖ₑ * ‖v‖ₑ = ‖v‖ₑ * ‖f t‖ₑ`. **That is wrong** — re-tested (`/tmp` probe):
   `ring` closes `‖f t‖ₑ * ‖v‖ₑ = ‖v‖ₑ * ‖f t‖ₑ` and `a * b = b * a` on `ℝ≥0∞`
   fine (EXIT 0). What actually failed was `ring` on
   `‖f t‖ₑ * ‖v‖ₑ = ‖f t‖ₑ * ‖‖v‖‖ₑ` — a goal still carrying the un-rewritten
   `‖‖v‖‖ₑ` (the `enorm_smul` on the real smul produced it; `enorm_norm` had not yet
   fired). `ring` correctly refuses (`ring_nf` made no progress): `‖v‖ₑ` and
   `‖‖v‖‖ₑ` are distinct ring atoms, equal only via `enorm_norm`, not a ring
   identity. Fix was pitfall 2 (`enorm_norm`, not `enorm_norm'`), after which the
   final `mul_comm` closes it; the merged proof uses an explicit
   `rw [Pi.smul_apply, enorm_smul, enorm_smul, enorm_norm, mul_comm]` chain. So:
   `ring` works on `ℝ≥0∞`; do not avoid it.
4. **`mul_le_mul_left'` / `mul_le_mul_right'` unknown identifiers** under this pin.
   Replaced by `gcongr` for `E_j * x ≤ E_j * η'` and `S * η' ≤ (S+1) * η'`.
5. **Mixing `bochnerDatumENorm` and `eLpNorm` in one `calc` with `rfl` bridges.**
   The initial version put `_ = bochnerDatumENorm … + bochnerDatumENorm … := rfl`
   between `eLpNorm` lines; combined with pitfall 1 this compounded the whnf cost.
   **Fix:** unfold once with `show eLpNorm … < η''` and keep the whole `calc` in
   `eLpNorm`; feed `hT`/`hP` in `eLpNorm` form by `have hTe … := hT` (one delta).
6. **`separatedAssembly` re-elaborated three times** (once per structural
   conjunct). Compute `have hasm := separatedAssembly …` once, then `hasm.1`,
   `hasm.2.1`, `hasm.2.2`.

## Reuse checks (grepped `formalization/NSFormalization` before restating)

* `separatedPath`, `separatedField`, `bochnerDatumENorm`, `MemBochnerDatum`,
  `CompletedDenseVia`, `forceClassCompact`, `aestronglyMeasurable_separatedPath`
  — `Section4/B01/{Separated,Compact}.lean`.
* `forceTimeMeasure`, `MemForceCompact` — `Section4/D01/ForceClass.lean`.
* `IsHomogeneousPath` — `Section4/D01/HomogeneousWitness.lean`.
* `IsHomogeneousSliceDatum`, `SplitRange` — `Section4/B02/Cutoff.lean`. Verified
  (scratch) that `B02.IsHomogeneousSliceDatum` (what `spatialApproxHomogeneous`
  returns) is **defeq** to `D01.Homogeneous.IsHomogeneousSliceDatum` (what
  `separatedAssembly` consumes): the witness feeds through directly.
* `temporalApprox` (`B02/Remaining.lean`), `spatialApproxHomogeneous`
  (`B02/AnnularReal.lean`), `separatedAssembly` (`B02/SeparatedAssembly.lean`).
* No homogeneous analogue of `Paper3.exists_angular_real_vector_positive_physical_approx`
  exists, so `B01.approxCompact` (monolithic) cannot be reused — confirmed by
  reading `B01/Compact.lean:155`.

## Commands

* `cd verification && lake build NSFormalization.Section4.B02.ApproxCompact` — success.
* `cd verification && lake env lean ../formalization/NSFormalization/Section4/B02/ApproxCompact.lean` — silent.
* `cd verification && lake env lean ../research/B02/axioms_approx_compact.lean` —
  both conformance `example`s typecheck; all 5 public decls print exactly
  `[propext, Classical.choice, Quot.sound]`.
