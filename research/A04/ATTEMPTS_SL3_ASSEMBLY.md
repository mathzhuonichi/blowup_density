# A04 unit G1 — sub-lemma SL3, step 3b: Laplacian datum assembly + dissipation identity `hlap`

Lane 088, task A04.  One new module
`formalization/NSFormalization/Section4/A04/LaplacianAssembly.lean`
(namespace `NSFormalization.Section4.A04`), importing `RealPairing` (082),
`D01.DerivativeDatum`, and A03 `VectorTameProduct`/`ScalarTameProduct`/`RealAngularProduct`.

**Both parts delivered and compiling, `sorry`-free, standard 3 axioms only.**

## What is proved (file:line in `LaplacianAssembly.lean`)

Part 1 (Laplacian datum):
| decl | line | statement |
|---|---|---|
| `isSobolevDatum_castOrder` | :76 | order-congruence transport of a datum |
| `castOrder` | :82 | `def`, datum transported along an order equality |
| `derivDatumStep` | :90 | `def`, one `D_j` lowering step (matches `isSobolevDatum_partialDeriv` output) |
| `cast_top_order`, `cast_mid_order` | :95, :98 | the two `Nat.cast` order equalities |
| `laplacianDatum` | :104 | `def`, `∑ⱼ D_j (D_j A)` at orders `m+2 → m+1 → m` |
| `spatialLaplacian_lift_eq_datumSum` | :115 | `rfl`: tree Laplacian of `lift Z.field` = `∑ⱼ ∂ⱼ∂ⱼ Z.field` |
| `isSobolevDatum_laplacian` | :~131 | **Part 1 target**: `IsSobolevDatum m (spatialLaplacian (lift Z.field) 0) (laplacianDatum m A)` |

Part 2 (dissipation identity + `hlap`):
| decl | statement |
|---|---|
| `angularMid_comm` | commutation of the two middle multiplication operators |
| `directionalDerivative_orderLowering_comm` | `D_σ ∘ Λ_{s→r} = Λ_{(s-1)→(r-1)} ∘ D_{σ'}` on `Lp ℂ 2 volume` |
| `isSobolevDatum_lowerVectorL` / `coe_lowerVectorL` | the in-tree `D01.lowerVectorL` (`HalfOrder.lean:103`) is a datum at the lower order (finding 2) |
| `castOrder_coe`, `coe_derivDatumStep` | `FourierData`-coercion of the transported / derivative-step components |
| `inner_component_reconcile` | ambient per-component `⟪Λ_{m+2→m}Ai, D(D Ai)⟫ = -‖D A'i‖²` |
| `norm_sq_derivDatumStep` | `‖derivDatumStep m j A'‖² = ∑ᵢ ‖D(A'ᵢ)‖²` (PiLp `L²` norm) |
| `inner_datum_laplacianDir` | per-direction `⟪G, D_j(D_j A)⟫_ℝ = -‖derivDatumStep m j A'‖²` |
| `inner_datum_laplacian` | **pairing identity** `⟪G, laplacianDatum m A⟫_ℝ = -∑ⱼ ‖D_j A'‖²` |
| `inner_datum_laplacian_le` | **`hlap`**: `⟪G, laplacianDatum m A⟫_ℝ ≤ -(gradientSobolevENorm m Z.field).toReal²` |
| `inner_datum_laplacian_le'` | **consumer-shaped `hlap`** (finding 1): arbitrary Laplacian datum `L`, RHS `gradientSobolevNormAt m u t²`, slice packaged from `A05.SmoothL2` |

`inner_datum_laplacian_le` is exactly the `hlap` hypothesis shape of
`A04.inner_energy_assembly` (`HighEnergy.lean:101`), with `L = laplacianDatum m A` (Part 1),
`G/A'/A` the order-`m`/`(m+1)`/`(m+2)` data of `Z.field`, and grad from
`gradientSobolevENorm_toReal_sq_eq_datum_sum` (`LaplacianDatum.lean:130`, `A'` at order `m+1`).
The inequality holds with equality (`0 ≤ ν` weakening not needed here; `inner_energy_assembly`
consumes the `≤`).

## Route as executed

**Part 1.**  For `Z : SmoothL2Field Space`, order-`(m+2)` datum `A`:
1. `isSobolevDatum_partialDeriv j (m+1)` on `Z` → order-`↑(m+1)` datum of `∂ⱼ(Z.field)`.
2. Order-transport `↑(m+1) → ↑m+1` (`isSobolevDatum_castOrder (cast_mid_order m)`), field
   repackaged as `(Z.directionalField (coordinateVector j)).field = partialDeriv j Z.field`
   (`rfl`), then `isSobolevDatum_partialDeriv j m` → order-`↑m` datum of `∂ⱼ∂ⱼ(Z.field)`.
3. `isSobolevDatum_add` folded over `Fin 3` (pairability from
   `schwartzPairable_of_isSobolevDatum` + smoothness of the second-partial field, `0 ≤ ↑m`).
4. Field reconciliation `spatialLaplacian (lift Z.field) 0 = ∑ⱼ ∂ⱼ∂ⱼ Z.field` is **`rfl`**
   (both unfold to `∑ⱼ fderiv ℝ (fun y => fderiv ℝ Z.field y eⱼ) x eⱼ`), and the folded datum is
   `laplacianDatum m A` via `Fin.sum_univ_three`.

**Part 2.**  Componentwise, moving everything to the ambient `Lp ℂ 2 volume` carrier
(`realSobolev_inner_eq_ambient`, `rfl`; subtype norm = ambient norm, `rfl`):
1. `laplacianDatum m A = ∑ⱼ …`, `inner_sum`, `PiLp.inner_apply`, `PiLp.norm_sq_eq_of_L2`.
2. Real skew-adjointness `real_inner_angularDirectionalDerivative` (082) peels one `D_j` onto `G`.
3. `G_i = Λ_{m+2→m}(A_i)` and `A'_i = Λ_{m+2→m+1}(A_i)` by `isSobolevDatum_unique` against the
   in-tree vector lowering `D01.lowerVectorL` (scalar `A03.IsScalarSobolevDatum.lower` through
   `isSobolevDatum_iff`; `isSobolevDatum_lowerVectorL`/`coe_lowerVectorL` are the datum and coe faces).
4. **New commutation** `directionalDerivative_orderLowering_comm` rewrites
   `D_j(Λ_{m+2→m}A_i) = Λ_{m+1→m-1}(D_j A_i)` and `D_j(Λ_{m+2→m+1}A_i) = Λ_{m+1→m}(D_j A_i)`.
5. Reviewer's reconciliation: `real_inner_lowering_pairing (m+1) (m-1) (m+1)` +
   `angularOrderLowering_self` + `simp only [show … from by ring]` on the midpoint (see
   `ATTEMPTS_SL3_REAL.md` §"Failed / adjusted approaches", the `rw`-on-dependent-index trap) gives
   `⟪Λ_{m+1→m-1} v, v⟫ = ‖Λ_{m+1→m} v‖²` with `v = D_j A_i`, i.e. `= ‖D_j A'_i‖²`.

The commutation (step 4) is the genuinely new analytic content the earlier notes flagged.  It is
`directionalDerivative_orderLowering_comm`, transported by `angularMid_comm` from the two middle
multiplication operators: they commute (`ring`), the lowering symbols coincide because
`lowering_mid_symbol_eq` collapses `W r · bessel(r-s) · W(-s)` to `bessel(r-s)(c•ξ)` (gap `r - s`
invariant under the `-1` shift, `(r-1)-(s-1) = r-s`), and the directional symbols coincide by
`mid_symbol_order_independent` (so the two `D` labels `↑m+1` and `↑(m+1)+1` need not agree).

## Failed / adjusted approaches (negative record)

* **`isSobolevDatum_partialDeriv j (m+1)` with a clean `(m:ℝ)+2` hypothesis — `isDefEq` TIMEOUT.**
  `(((m+1:ℕ):ℝ)+1) = (m:ℝ)+2` is **not** `rfl` (verified: `example … := rfl` fails), and feeding
  `hA : IsSobolevDatum ((m:ℝ)+2) Z.field A` directly makes the elaborator time out (200000
  heartbeats) trying to unify the orders while inferring the implicit `A`.  Fixed by the
  order-congruence transport `isSobolevDatum_castOrder` + the clean `def`s `castOrder`/`derivDatumStep`
  and cast lemmas `cast_top_order`/`cast_mid_order`: hypotheses are handed to
  `isSobolevDatum_partialDeriv` already in its native `↑n + 1` form, so the order match is syntactic
  (no hard defeq).  This is the central Part-1 hazard.
* **Same `isDefEq` timeout on the *consumer* side (finding 1).**  Applying `inner_datum_laplacian_le`
  straight into a goal whose grad is `gradientSobolevNormAt m u t` (rather than
  `(gradientSobolevENorm m Z.field).toReal`) makes `exact` unfold
  `gradientSobolevENorm → columnsSobolevENorm → sobolevENorm` (an `⨅` over a subtype of data) and
  blows the 200000-heartbeat budget — even though the two are `rfl`-equal.  Fix in
  `inner_datum_laplacian_le'`: state the norm bridge as its own `have hg : … := rfl` (which forces the
  single-step `gradientSobolevNormAt` def-unfold and stops there) and the datum bridge as its own
  `have hLeq := isSobolevDatum_unique …`, then `rw [hLeq, hg]`; inlining either into `exact`
  reproduces the timeout.  The slice must be packaged as `⟨fun x => u (t,x), hsl.1, hsl.2⟩` (anonymous
  constructor) so `Z.field` is *definitionally* the slice and `hg` is genuinely `rfl`.
* **The `+1-1` order arithmetic — a *type* equality by `rfl`, not a real-number equality.**  The
  **real** equation `((m:ℝ)+1-1) = (m:ℝ)` is **NOT** `rfl` (`example (m:ℕ) : ((m:ℝ)+1-1) = (m:ℝ) := rfl`
  errors, "expected `↑m + 1 - 1 = ↑m`").  What *is* `rfl` is the **type** equality
  `RealSobolevHilbert ((m:ℝ)+1-1) = RealSobolevHilbert (m:ℝ)`, because
  `Source.RealSobolev.realSubspace (_ : ℝ)` (`RealSobolev.lean:119`) **ignores its order argument** —
  the carrier is the same closed real subspace of `FourierData` at every order.  That is why
  `isSobolevDatum_partialDeriv`'s output (typed at `RealSobolevHilbert ((m:ℝ)+1-1)`) is accepted where
  `RealSobolevHilbert (m:ℝ)` is wanted, and why the composition's intermediate orders (`(m+2)-1` etc.)
  never need a real-number normalization.  (Corrected per review finding 3; the earlier draft
  over-claimed the real equation as `rfl`.)
* **`rw` on the dependent midpoint index `(r+t)/2`.**  Same trap as `ATTEMPTS_SL3_REAL.md` (F1):
  `angularOrderLowering`'s proof argument mentions `(r+t)/2`, so `rw [show (r+t)/2 = m …]` fails
  with "motive is not type correct".  Used `simp only [show … from by ring]` (works).
* **`congr 1` then an explicit norm-bridge `rw` in `inner_datum_laplacianDir` — "No goals".**  After
  `inner_component_reconcile`, LHS and RHS were already defeq (subtype norm = ambient coe norm =
  ambient), so the extra `congr 1`/`rw` had no goal.  Replaced by the helper `norm_sq_derivDatumStep`
  that pre-decomposes `‖derivDatumStep m j A'‖²` into the ambient component sum, so the per-component
  goal matches `inner_component_reconcile` by `exact` (no bridge step).
* **No in-tree operator commutation for `D_j ∘ Λ`.**  Confirmed by grep; had to build
  `angularMid_comm`/`directionalDerivative_orderLowering_comm` from the middle-operator `_coeFn`
  machinery (`LaplacianPairing.lean`) and the symbol lemmas.  The uniqueness-only route was rejected
  because identifying `D_j G_i` as an order-`(m-1)` datum via `isSobolevDatum_partialDeriv` would
  need `m ≥ 1` (ℕ order `m-1`); the commutation route works for all `m : ℕ`.

## Review revisions (ACCEPT-WITH-NOTES, `REVIEW_SL3_ASSEMBLY.md`)

* **Finding 1** — added the consumer-shaped corollary `inner_datum_laplacian_le'`
  (`gradientSobolevNormAt m u t` RHS, arbitrary Laplacian datum `L` pinned by `isSobolevDatum_unique`,
  slice packaged from `A05.SmoothL2`); the `isDefEq` timeout it avoids is recorded above.
* **Finding 2** — dropped the local `vectorLowerDatum`/`isSobolevDatum_vectorLower`/`coe_vectorLowerDatum`
  in favour of the in-tree `D01.lowerVectorL` (`HalfOrder.lean:103`, `lowerVectorL_apply` by `rfl`);
  kept only the three-line datum face `isSobolevDatum_lowerVectorL` (mirrors `D01.isSobolevPath_lower`)
  and `coe_lowerVectorL`, with a docstring pointer to the merged vector-datum lemma
  `D01.isSobolevDatum_lower` (lane 085, `LerayLowering.lean` — absent from this worktree, PR #89).
* **Finding 3** — corrected the `+1-1` bullet above: the *real* equation is not `rfl`, only the *type*
  equality is (because `realSubspace` ignores its order).
* **Finding 4** — added the explicit `import NSFormalization.Section4.A04.LaplacianDatum`.
* **Finding 5** — extended `axioms_sl3_assembly.lean` to all **20** current public declarations.

## Commands run

- `cd verification && lake build NSFormalization.Section4.A04.LaplacianAssembly` →
  `Built …LaplacianAssembly (3.0s)` / `Build completed successfully (9894 jobs)` (only pre-existing
  replayed upstream warnings: `if_pos`, an unused simp arg, `SchwartzMap.smul_apply`).
- `cd verification && lake env lean ../formalization/NSFormalization/Section4/A04/LaplacianAssembly.lean`
  → empty output, exit 0 (zero warnings, default heartbeat budget, no `set_option`).
- `cd verification && lake env lean ../research/A04/axioms_sl3_assembly.lean` → all **20** public
  declarations depend only on `[propext, Classical.choice, Quot.sound]`.
- `grep -nE 'sorry|admit|native_decide|maxHeartbeats|axiom|set_option' …/LaplacianAssembly.lean` →
  no match.
- `make check` (worktree root) → exit 0 (architecture, contract-policy, work-queue all pass).
