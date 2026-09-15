# ATTEMPTS — lane 136-C01-e2-vocabulary (row E2, carrier-B vocabulary bridge)

Deliverable `formalization/NSFormalization/Section4/C01/Vocabulary.lean`, namespace
`NSFormalization.Section4.C01` (same as `EnergyIdentity.lean`).  Audit
`research/C01/axioms_e2.lean`.

## What was proved (all standard 3 axioms)

| name | statement (as compiled) | nature |
|---|---|---|
| `field_normSq_integrable` | `Integrable (fun x => ‖A.field x‖^2) volume` | recast of `field_inner_integrable A A` via `real_inner_self_eq_norm_sq` |
| `l2Sq_eq_inner` (E2a) | `(∫ x, ‖A.field x‖^2) = ⟪A.toLp, A.toLp⟫` | `integral_congr_ae` + `field_inner` |
| `norm_toLp_sq_eq_l2Sq` | `‖A.toLp‖^2 = ∫ x, ‖A.field x‖^2` | `real_inner_self_eq_norm_sq` on `A.toLp` + E2a (finding 8) |
| `gradientSq_eq_sum` (E2b) | `∑ i:Fin 3, ‖(A.directionalField (axis i)).toLp‖^2 = ∫ x, ∑ i:Fin 3, ‖fderiv ℝ A.field x (axis i)‖^2` | per-`i` E2a-norm form + `directionalField_field` (rfl) + `integral_finsetSum` |
| `sqrt_dirSum_sq` | `Real.sqrt (∑ i, ‖(A.directionalField (axis i)).toLp‖^2)^2 = ∑ i, ‖…‖^2` | `Real.sq_sqrt` (the finding-4 adapter) |
| `pairing_eq_inner` (E2c) | `(∫ x, ⟪A.field x, B.field x⟫) = ⟪A.toLp, B.toLp⟫` | `(field_inner A B).symm` |
| `energyIdentity_of_carrierB` | `d = -2*ν*(∫ x, ∑ i, ‖fderiv ℝ u.field x (axis i)‖^2) + 2*(∫ x, ⟪u.field x, f.field x⟫)` from the five carrier-B inputs | E0 `inner_energy_identity_deriv` + `laplacian_pairing`/`advection_inner_zero`/`gradient_pairing_zero` + the three bridges |

## rfl vs real analysis (the brief's question)

- **No bridge is fully `rfl`.**  All three (E2a/E2b/E2c) reduce to
  `EulerOrdinarySobolev.field_inner`
  (`⟪A.toLp,B.toLp⟫ = ∫ x, ⟪A.field x, B.field x⟫`), whose proof is
  `MeasureTheory.L2.inner_def` + `integral_congr_ae` over `A.toLp_ae`/`B.toLp_ae`.
  That is the *only* analytic content, and it is **Plancherel-free**: the physical
  Bochner inner product of the `Lp` classes equals the integral of the a.e.
  representatives.  No Fourier/Parseval step anywhere (contrast the carrier-A
  order-0 route, which needs the open `OrderZeroDatum` norm identity).
- The one genuinely `rfl` fact used is `directionalField_field`
  (`(A.directionalField v).field x = fderiv ℝ A.field x v`, `@[simp]`, rfl); it lets
  the per-direction norm integral be re-spelled with `fderiv` under the integral
  (`simpa only [directionalField_field]`).
- `sqrt_dirSum_sq` is pure arithmetic (`Real.sq_sqrt` on a nonneg finite sum).

## Errors hit and fixes (exact text)

1. **`⟪…⟫_ℝ` subscript notation not in scope.**  First draft wrote the inner
   product as `⟪A.toLp, A.toLp⟫_ℝ` (copying the vendor `field_inner`).  Build:
   ```
   error: NSFormalization/Section4/C01/Vocabulary.lean:98:45: unexpected identifier; expected ':=', 'where' or '|'
   ```
   (same at the two other `⟫_ℝ` sites).  The `_ℝ` subscript form is scoped and the
   vendor gets it via `open InnerProductSpace`, which I did not open.  **Fix:** use
   the un-subscripted `⟪·,·⟫` from `open scoped RealInnerProductSpace` — it is the
   same `inner ℝ` term and is exactly the notation `EnergyIdentity.lean`'s E0 uses,
   so E0 applies without a notation mismatch.  (Did **not** add `open InnerProductSpace`;
   fewer opens = fewer ambiguities.)

2. **`integral_finset_sum` deprecated.**
   ```
   warning: `MeasureTheory.integral_finset_sum` has been deprecated: Use `MeasureTheory.integral_finsetSum` instead
   ```
   **Fix:** `integral_finsetSum`.  (A warning, not an error, but formalization
   modules should stay clean.)

3. **Audit file `Space` unknown.**  `axioms_e2.lean` first wrote
   `open NavierStokes.ProblemStatement (Space)` →
   `error: unknown namespace 'NavierStokes.ProblemStatement'` and
   `failed to synthesize NormedAddCommGroup Space`.  In this import context `Space`
   resolves as `EulerSmoothLimit.Space`.  **Fix:** `open EulerSmoothLimit`; the
   `#check`s then print `∫ (x : Space), …` cleanly.  (The `#print axioms` lines were
   already correct before this fix — they don't depend on `Space` being named.)

## Decisions

- **Module lives in `formalization/` (task-mandated) ⇒ cannot name the spec defs.**
  `l2Sq`/`gradientSq`/`pairing`/`gradientTensor` are `verification/Contracts/V1`
  objects, and `verification` *depends on* `formalization` (one-way, per the
  lakefiles).  So the bridges are stated with the **raw integrands** that are
  definitionally `l2Sq A.field`, `gradientSq A.field` (mod the `PiLp` reindex below)
  and `pairing A.field B.field`.  This is a **deviation from the review's suggested
  statements**, which named `Contracts.V1.gradientTensor` in a `formalization` module
  — that cannot compile.  Recorded so the assembly lane knows the final
  `energyIdentity` (a `HasDerivAt` about `l2Sq`/`gradientSq`/`pairing`) must be a
  **`verification`/`Bindings` module** that can see both sides.
- **The single remaining E2b step** `∑ i, ‖fderiv ℝ z x (axis i)‖^2 = ‖gradientTensor z x‖^2`
  is `PiLp.norm_sq_eq_of_L2` + `coordinateVector = axis` + `spatialDerivative = fderiv`.
  All three are `Contracts.V1`/`Data` facts, so it is a **one-line verification-side
  binding**, deferred (not provable here).  `gradientSq_eq_sum` already delivers the
  hard half (the `toLp`-norm ⇒ Frobenius-integral reindex).
- **Non-vacuity.**  Did **not** instantiate `energyIdentity_of_carrierB` on the zero
  field: `zeroField` exists (`LpSmoothFieldAlgebra.lean:72`) but discharging `hmom`
  needs `(laplacianField zeroField).toLp = 0` and `(advectionField zeroField zeroField).toLp = 0`
  sublemmas (each a few lines) — not cheap.  Instead the audit shows
  `Nonempty (SmoothL2Field Space)` via `zeroField` and `#check`s each hypothesis-free
  bridge instantiated on it, which suffices: the bridges are equalities over an
  inhabited carrier, not vacuous.

## Commands

- `lake build NSFormalization.Section4.C01.Vocabulary` → `Build completed successfully (4573 jobs)`.
- `lake env lean ../formalization/NSFormalization/Section4/C01/Vocabulary.lean` → silent, EXIT 0.
- `lake env lean ../research/C01/axioms_e2.lean` → all 7 decls `[propext, Classical.choice, Quot.sound]`; `#check`s print the instantiated bridges.
- `make check` → EXIT 0 (all four sub-checks pass).
