# B01 units 1–3 — attempts log (lane 035)

Scope: units 1, 2, 3 of `research/B01/COMPARISON.md` (the three units R46 actually consumes).
Modules produced:
`formalization/NSFormalization/Section4/B01/Compact.lean` (units 1, 2) and
`formalization/NSFormalization/Section4/B01/Completion.lean` (unit 3).
Conformance: `research/B01/axioms_u123.lean`.

## What was reused (not reproved)

- `Section4/D01/ForceClass.lean`: `IsSobolevPath`, `MemForceCompact`, `forceTimeMeasure`
  (all restatements of `Contracts/V1/Data.lean`), and `memForceCompact_of_smooth_support` —
  this is exactly the `MemForceCompact` half of unit 1, so it was reused verbatim, not reproved.
  (`ForceClass.lean` also already contains `contDiff_angularRealVectorSlice`, which is unit 4,
  out of this lane's scope.)
- `Section4/D01/SmoothDatum.lean`: `IsSobolevDatum` (restated verbatim, defeq to Data's).
- `Paper3/AngularRealVectorBochner.lean` (`ARVB`): `angularRealVectorSlice`,
  `angularRealVectorSlice_pairing` (:54), `memLp_angularRealVectorSlice` (:64),
  `exists_angular_real_vector_positive_physical_approx` (:120).
- Mathlib: `Lp.memLp`, `MemLp.toLp`/`MemLp.coeFn_toLp`, `Lp.coeFn_sub`, `Lp.eLpNorm_ne_top`,
  `Lp.norm_def`, `Lp.enorm_def`, `eLpNorm_congr_ae`, `ENNReal.toReal_lt_toReal`,
  `ENNReal.toReal_pos`, `norm_sub_rev`, `lt_top_iff_ne_top`.

## Positive path

- Unit 1 `IsSobolevPath`: `angularRealVectorSlice_pairing` rewrites the pairing to
  `∫ ψ·(f i (t,·))`; the linking hypothesis `(F z).ofLp i = f i z` closes the integrand equality.
  `AEStronglyMeasurable`: first component of `memLp_angularRealVectorSlice … 1`.
- Unit 2 `approxCompact`: lift `b` to `hb.toLp b`, feed it to
  `exists_angular_real_vector_positive_physical_approx`, package the output through unit 1 and
  `memForceCompact_of_smooth_support`. Norm bookkeeping isolated in `bochnerDatumENorm_toLp_sub`
  (a.e.-class equality of `eLpNorm (D-b)` with `‖hD.toLp D - hb.toLp b‖` + finiteness), then a
  `by_cases r = ⊤` split: `r = ⊤` uses only finiteness; `r ≠ ⊤` uses `ENNReal.toReal_lt_toReal`
  with `ε := min 1 r.toReal`.
- Unit 3: the four fields are one-liners over `Lp.memLp`, `MemLp.coeFn_toLp`, `Lp.enorm_def`,
  `eLpNorm_congr_ae`.

## Failures / dead-ends encountered and fixed

1. **`rw [← hFf (t, x) i]` in unit 1 failed** — "Did not find pattern `f i (t, x)`".
   After `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` the goal was an
   unreduced beta-redex `(fun x => ψ x * ↑(f i (t,x))) x = (fun x => ψ x * ↑(((fun x => F (t,x)) x).ofLp i)) x`;
   the `x` in `f i (t,x)` was the *lambda-bound* variable, not the introduced one, so `rw`'s
   syntactic pattern did not match. Fix: `simp only [hFf (t, x) i]`, which beta-reduces first and
   then rewrites (and closes the goal). `rw` was the wrong tool here.

2. **`haveI : Fact (1 ≤ q)` tripped `linter.style.haveILetI`.** Switched to `have : Fact (1 ≤ q)`;
   local hypotheses of a class type are still found by instance resolution in Lean 4, so the
   source theorem's `[Fact (1 ≤ q)]` and the `Lp` norm still resolve. (This linter is only a
   warning in `formalization/`, but the module is kept warning-free.)

3. **Defeq of the restated predicates vs `Contracts/V1/Data`.** No proof needed: the five
   restatements from `Data.lean` (`MemBochnerDatum`, `bochnerDatumENorm`, `CompletedDenseVia`,
   `CompletedDense`, `forceClassCompact`) are token-for-token the Data bodies over defeq sub-terms
   (`forceTimeMeasure = positiveTimeMeasure`, `SmoothDatum.IsSobolevDatum = Data.IsSobolevDatum`,
   D01 `MemForceCompact = Data.MemForceCompact`). `bochnerSpace` is **not** from `Data.lean` (there
   is no `Contracts.V1.Data.bochnerSpace`); it is restated from `research/B01/Spec.lean:158`, where
   it is byte-identical. The conformance file discharges each Data-typed `example` by the
   formalization theorem through this defeq with `:=` (no `by`/coercion), confirming it in the
   kernel.

## Verification hooks used

- `(F z).ofLp i` vs `F z i`: definitionally equal (`WithLp.ofLp`), so the source theorem's
  `hFi : ∀ z i, F z i = f i z` is passed straight into unit 1's `∀ z i, (F z).ofLp i = f i z`.
- `hmem.toLp D` vs `(memLp_angularRealVectorSlice …).toLp D`: proof-irrelevant (`MemLp` is a
  `Prop`), so `exact he` closes despite the differing proof term.

## Commands (all from `verification/`, after `. ../scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`)

- `lake build NSFormalization.Section4.B01.Compact` → `Build completed successfully`.
- `lake build NSFormalization.Section4.B01.Completion` → `Build completed successfully (9879 jobs)`.
- `lake env lean ../research/B01/axioms_u123.lean` → exit 0, no error/warning/sorry; every
  `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

## Review fixes (ACCEPT-WITH-NOTES, `research/B01/REVIEW_U123.md`)

All findings were documentation/hygiene; no proof, type, or `example` changed. The five
spec-field `example`s are untouched and still discharged by bare `:= …`.

- **Note 1 (finding 1) — `bochnerSpace` provenance.** `Contracts.V1.Data` has no `bochnerSpace`
  (`grep -rn bochnerSpace verification/Contracts/` is empty; `Data.lean:158` is inside the
  `IsSobolevDatum` docstring). Fixed the `bochnerSpace` docstring in `Compact.lean` to cite only
  `research/B01/Spec.lean:158`, dropped `158` from the `Data.lean:…` list in the module header and
  gave `bochnerSpace` its own sentence there, and corrected the ATTEMPTS "Failures" item 3 above.

- **Note 2 (finding 2) — token-for-token.** Added `abbrev SpaceTimeField := VelocityField`
  (`Data.lean:104`, mirroring `Section4/D01/HomogeneousWitness.lean:614`) to `Compact.lean` §0 and
  used `SpaceTimeField` in `CompletedDenseVia`, `CompletedDense`, `forceClassCompact`. Those three
  are now byte-identical to `Data.lean:732,743,563` (only the previously-substituted
  `VelocityField` differed).

- **Note 3 (finding 3) — duplicate `bochnerDatumENorm`.** Chose **keep the local copy + a `rfl`
  bridge** over reuse-by-import-and-open. Reason: `NSFormalization.Section4.D01.Homogeneous`
  (`HomogeneousWitness.lean`) also declares `forceTimeMeasure` and `IsHomogeneousPath`, and
  `open`ing it to reuse its `bochnerDatumENorm` would make `forceTimeMeasure`/`bochnerDatumENorm`
  ambiguous against the `ForceClass`/local copies — the reviewer flagged this as the worse trade.
  So `Compact.lean` now `import`s `HomogeneousWitness` **without** opening its namespace, keeps its
  own one-line `bochnerDatumENorm`, names the D01 copy canonical in a docstring, and adds the
  bridge `bochnerDatumENorm_eq_homogeneous : @bochnerDatumENorm = @…D01.Homogeneous.bochnerDatumENorm := rfl`.
  **Import cost measured:** `Compact.lean` build 3.6s → 4.0s, job count 9878 → 9880 (only two
  extra cached jobs — `HomogeneousWitness`'s closure is almost entirely shared with `ARVB`), so
  the import is cheap and acceptable. Unit 10 should hoist the shared completion vocabulary into
  one module and delete both copies.

### Commands (Review fixes)

- `lake build NSFormalization.Section4.B01.Compact` → `Built … (4.0s)`, `Build completed successfully (9880 jobs)`.
- `lake build NSFormalization.Section4.B01.Completion` → `Built … (2.6s)`, `Build completed successfully (9881 jobs)`.
- `lake env lean ../research/B01/axioms_u123.lean` → exit 0, no error/warning/sorry; all 8
  `#print axioms` = `[propext, Classical.choice, Quot.sound]`; all `example`s unchanged and passing.
- `make check` → exit 0 (`test_contract_policy` 13 tests OK, `check_work_queue` "30 work items … consistent").
