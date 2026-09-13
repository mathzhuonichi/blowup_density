# A04 unit G1, sub-lemma SL5 — split of the nonlinear pairing (lane 095)

SL5 (`research/A04/G1_SPLIT.md:157-165`, rated **L**) is the `hnl` input of
`A04.inner_energy_assembly` / `inner_energy_Rhigh` (`HighEnergy.lean:101,106`):

```
− ⟪G t, N⟫_ℝ ≤ gradientSobolevNormAt (m:ℝ) u t * (outerSobolevENorm (m:ℝ) (u t·) (u t·)).toReal
```

with `G t` = order-`m` datum of `u(t,·)` (`RealVectorSobolev (m:ℝ)`), and `N` the order-`m`
datum of the **advection slice** `advection u t = (u·∇)u(t,·)` (`MomentumDatum.lean:167-179`:
`hN : IsSobolevDatum (m:ℝ) (fun x => advection w.velocity t x) N`).

> **History note (2026-09-13).**  PR #94 (lane 088, `Section4/A04/LaplacianAssembly.lean`) closed SL3
> and supplies the order-transport machinery SL5 reuses (`derivDatumStep`,
> `isSobolevDatum_castOrder`/`castOrder`/`cast_mid_order`/`cast_top_order`, `coe_derivDatumStep`,
> `norm_sq_derivDatumStep`, `isSobolevDatum_lowerVectorL` + `coe_lowerVectorL`,
> `directionalDerivative_orderLowering_comm`, `angularMid_comm`, `isSobolevDatum_laplacian`).
> **Lane 095 branched before #94 merged**, so its worktree lacked `LaplacianAssembly.lean` and it could
> not import it (see `REVIEW_SL5.md` §4).  **Lanes ≥ 100 (incl. 102) branched after #94 and import
> `LaplacianAssembly` normally** — that is the current, standing situation on `erenup/integration`.
> The table sizes below are as of PR #94.

## Objects, verified against the tree (line numbers current on this branch)

* `advection u t x = spatialDerivative u t x (u (t,x)) = fderiv ℝ (fun y => u(t,y)) x (u(t,x))`
  (`vendor/.../ProblemStatement.lean:63`).  So `advection` is the **advection form**
  `(u·∇)u = ∑_j u_j ∂_j u`, *not* the divergence form; C01 already records
  `advection (lift z) 0 x = ∑_j (z x)_j • dirDeriv j z x` (`C01/Trilinear.lean:95`, `hmap`).
* `partialDeriv j v x = spatialDerivative (lift v) 0 x (coordinateVector j) = fderiv ℝ v x (e_j)`
  (`A03/OuterTameProduct.lean:59`); equals `A05.dirDeriv j v x`.
* `outerColumn u v j = fun x => (u x j) • v x` (`A03/OuterTameProduct.lean:68`), the `j`-th
  column `W_j := u_j·u` of `u⊗v`.
* `outerSobolevENorm s u v = columnsSobolevENorm s (outerColumn u v)
   = (∑_j sobolevENorm s (outerColumn u v j) ^ 2) ^ (1/2)` (`A03/OuterTameProduct.lean:79`,
  `columnsSobolevENorm` :75), the **ℓ²/Frobenius** assembly over the three columns — the answer to
  the task's open question: it is the ℓ² sum over columns `j` of `sobolevENorm s (u_j • v)`, not a
  separate tensor norm.
* `gradientSobolevNormAt s u t = (gradientSobolevENorm s (u t·)).toReal` (`A04/LaplacianDatum.lean:87`),
  `gradientSobolevENorm s v = columnsSobolevENorm s (fun j => partialDeriv j v)`
  (`A03/OuterTameProduct.lean:87`) — same ℓ² assembly over the three `∂_j`.
* `angularDirectionalDerivativeReal (m+1) e_j : RealSobolevHilbert (m+1) →L[ℝ] RealSobolevHilbert m`,
  the order-lowering datum multiplier (`D01/DerivativeDatum.lean:134`).
* `isSobolevDatum_partialDeriv j m hA` (`D01/DerivativeDatum.lean:245`): for `A` an order-`(m+1)`
  datum of `Z.field`, `WithLp.toLp 2 (fun i => angularDirectionalDerivativeReal (m+1) e_j (A i))`
  is the **order-`m`** datum of `partialDeriv j Z.field`.
* Datum existence and finiteness: `A03.exists_sobolevDatum` (`VectorTameProduct.lean:77`,
  `sobolevENorm s z ≠ ⊤ → ∃ A, IsSobolevDatum s z A`), `A03.sobolevENorm_eq` (`:71`,
  `sobolevENorm s z = ‖A‖ₑ`), `A03.tameProductVector m` (`:256`, the column enorm bound).
* Real skew-adjointness (082, `A04/RealPairing.lean`):
  `real_inner_angularDirectionalDerivative` (`:84`, ambient `Lp ℂ 2` carrier) and
  `real_inner_angularDirectionalDerivativeReal` (`:96`, subtype, common order); plus
  `realSobolev_inner_eq_ambient` (`:77`, `rfl`).
* Single-vector lowering pairing (082): `inner_loweringMid_pairing` (`:168`),
  `inner_lowering_pairing_complex` (`:199`), `real_inner_lowering_pairing` (`:218`) — all take one
  vector in both slots; the symbol identity `lowering_mid_symbol_eq` (`:172`) depends only on `r − s`.

## Sub-lemma table (sizes after PR #94)

| # | statement | Lean form | size | status | inputs / blocker |
|---|---|---|---|---|---|
| 5a | div-free pointwise divergence form `advection u t x = ∑_j partialDeriv j (outerColumn z z j) x`, hyps `DifferentiableAt ℝ z x` + `spatialDivergence u t x = 0` (`z := u(t·)`) | identity of `Space` fields | **M** | open (recorded, this lane) | `HasFDerivAt.smul` + `PiLp.proj` chain rule + `C01/Trilinear.lean:91-98` (`hadv`,`hbasis`,`hmap`) + `Fin.sum_univ_three`; unchanged by #94; no upstream gap |
| 5b | order-`(m+1)` datum of each column `W_j = u_j·u`: `∃ B_j, IsSobolevDatum ((m:ℝ)+1) W_j B_j` | `A03.exists_sobolevDatum` after enorm `≠ ⊤` | **S** | **DONE (102)** `A04.exists_outerColumn_datum_succ` (order `m+1`) and `A04.exists_outerColumn_datum` (order `m`), `NonlinearColumns.lean` | `A03.outerProductTame (m+1)` + `A03.le_columnsSobolevENorm` ⇒ `sobolevENorm ((m+1:ℕ):ℝ) (outerColumn z z j) ≠ ⊤` (low `H²` factor finite by `A03.sobolevENorm_two_le`), then `A03.exists_sobolevDatum`; hypothesis is `MemHmVector (m+1) z` + `2 ≤ m`. Order `((m+1:ℕ):ℝ) → (m:ℝ)+1` bridged by `A04.isSobolevDatum_castOrder (cast_mid_order m)`. **No `SmoothL2Field` here** (that is 5c's need) |
| 5c | `N = ∑_j (datum_m of ∂_j W_j)` | `N = ∑_j derivDatumStep m j (castOrder … B_j)`, via `isSobolevDatum_partialDeriv` + `isSobolevDatum_add` (over 3 j) + `isSobolevDatum_unique` against `hN` | **S–M** (~60–90 lines) | open — **only blocker now is 5a** (5b DONE) | `B_j` from **`A04.exists_outerColumn_datum_succ` (102, DONE)**; copy 088's `isSobolevDatum_laplacian` with **one** derivative step instead of two; `derivDatumStep`/`castOrder`/`isSobolevDatum_castOrder`/`isSobolevDatum_add`/`isSobolevDatum_unique` from #94 + D01; each `W_j` wrapped as a `SmoothL2Field` (088's `Z.directionalField` repackaging is the fiddly part); the field rewrite consumes 5a |
| 5d.amb | summed real skew-adjointness, ambient carrier: `∑_i ⟪f_i, D g_i⟫ = -∑_i ⟪D f_i, g_i⟫` | `sum_real_inner_angularDirectionalDerivative` | **S** | **DONE (this lane)** | 082 `real_inner_angularDirectionalDerivative` + `Finset.sum_neg_distrib`. This is the form the double-sum IBP consumes (`G_i` order `m`, `B_j i` order `m+1`, on the shared `FourierData`) |
| 5d.sub | vector lift of 082 on the datum carrier (common order `s`): `∑_i ⟪f_i, D g_i⟫ = -∑_i ⟪D f_i, g_i⟫` | `sum_real_inner_angularDirectionalDerivativeReal` | **S** | **DONE (this lane)** | 082 `real_inner_angularDirectionalDerivativeReal` + `Finset.sum_neg_distrib` |
| 5e | discrete Cauchy–Schwarz over a finset of inner products: `∑_j ⟪a_j,b_j⟫ ≤ √(∑‖a_j‖²)·√(∑‖b_j‖²)` (and the `\|·\|` form) | `sum_inner_le_sqrt_mul_sqrt`, `abs_sum_inner_le_sqrt_mul_sqrt`, generic `[InnerProductSpace ℝ E]` | **S** | **DONE (this lane)** | `real_inner_le_norm` / `abs_real_inner_le_norm` + `Real.sum_mul_le_sqrt_mul_sqrt` |
| **5i** | **two-vector, two-source-order lowering transfer**: `⟪Λ_{s→r} v, Λ_{s'→t} w⟫ = ⟪Λ_{s→r'} v, Λ_{s'→t'} w⟫` for `r + t = r' + t'` (mid / complex / real layers) | `inner_loweringMid_transfer`, `inner_lowering_transfer_complex`, `real_inner_lowering_transfer` | **S** | **DONE (this lane)** | generalizes 082's single-vector `inner_loweringMid_pairing`/`…_complex`/`real_inner_lowering_pairing` from one vector to two and from one source order to two; `lowering_mid_symbol_eq` + `sobolevBesselWeight_mul` + `angularFrequencyDilation.inner_map_map` + `real_inner_eq_re_complex`. **SL5's only genuinely new analytic content** |
| 5f.grad | `√(∑_j ‖D_j A'‖²) = gradientSobolevNormAt (m:ℝ) u t`, `A' = datum_{m+1}(u)` | `gradientSobolevENorm_toReal_sq_eq_datum_sum` (`LaplacianDatum.lean:130`) + `Real.sqrt_sq ENNReal.toReal_nonneg` | **S** | **DONE (102)** `A04.sqrt_sum_norm_sq_derivDatumStep_eq` (`Z.field` form) and `A04.sqrt_sum_norm_sq_derivDatumStep_eq_slice` (`gradientSobolevNormAt` form, explicit `rfl` bridge), `NonlinearColumns.lean` | **no order shift as stated**: the row uses `D_j` on `datum_{m+1}(u)`, exactly what `gradientSobolevENorm_toReal_sq_eq_datum_sum` gives; its RHS summand is defeq to `‖derivDatumStep m j A'‖²` (checked: the `have hsum` typechecks). The shift `D_j G` vs `D_j A'` is 5h/5i's concern, not this row's |
| 5g.outer | `√(∑_j ‖C_j‖²) = (outerSobolevENorm (m:ℝ) z z).toReal`, `C_j = datum_m(W_j)` (≤ suffices) | `columnsSobolevENorm` `.toReal` ℓ² arithmetic of `gradientSobolevENorm_toReal_sq_eq_sum` (`LaplacianDatum.lean:96`) with `outerColumn` for `partialDeriv` + `sobolevENorm_eq` on `C_j` | **S–M** | **DONE (102)** `A04.sqrt_sum_norm_sq_columnData_eq` (with the reusable `A04.columnsSobolevENorm_toReal_sq_eq_sum` / `A04.outerSobolevENorm_toReal_sq_eq_sum`), `NonlinearColumns.lean`; delivered as **`=`**, not just `≤` | `columnsSobolevENorm` ℓ² arithmetic (general column family, mirroring `LaplacianDatum.lean:96`) + `A03.sobolevENorm_eq` on each `C_j` + `Real.sqrt_sq`. Finiteness of each column is **free from the given data `C_j`** (`sobolevENorm = ‖C_j‖ₑ ≠ ⊤`); no `tameProductVector m` bound needed once the data are in hand |
| 5h | assembly: `inner_sum` → 5d.amb → **5i** → 5e at `E = RealVectorSobolev m` → 5f/5g → target | one calc | **M** (~100–150 lines; L overall) | open — **runs last**, needs 5c (5i/5e/5f/5g all DONE) | **the last two calc steps already close** (reviewer scratch, `REVIEW_SL5_COLUMNS.md` §2(d)): `5e (095)` then `rw [sqrt_sum_norm_sq_derivDatumStep_eq_slice, sqrt_sum_norm_sq_columnData_eq]` (both 102) produce literally the two SL5 factors.  What remains is the first step: substitute 5c, `inner_sum`, `sum_real_inner_angularDirectionalDerivativeReal`/5d.amb, the order reconciliations `G = Λ_{m+1→m} A'`, `C_j = Λ_{m+1→m} B_j` (`isSobolevDatum_lowerVectorL` + `isSobolevDatum_unique` + `coe_lowerVectorL`, #94) and `D_j G = Λ_{m→m-1}(D_j A')` (`directionalDerivative_orderLowering_comm`, #94), glued by **5i** (095); use `abs_sum_inner_le_sqrt_mul_sqrt` so the sign need not be tracked |

Overall SL5 stays **L**.  With 5d/5e/5i (095) and 5b/5f/5g (102) all DONE, the remaining critical path is
just **5a → 5c → 5h** (5h last).

## What this lane proves (the S items)

`formalization/NSFormalization/Section4/A04/NonlinearPairing.lean`:

* **5e** `sum_inner_le_sqrt_mul_sqrt` and `abs_sum_inner_le_sqrt_mul_sqrt` — abstract discrete
  Cauchy–Schwarz on any real inner product space, generic in the finset index.
* **5d.amb** `sum_real_inner_angularDirectionalDerivative` — summed real skew-adjointness on the
  ambient `Lp ℂ 2` carrier (the form the double-sum IBP consumes).
* **5d.sub** `sum_real_inner_angularDirectionalDerivativeReal` — the same on the datum-carrier
  subtype at a common order (direct vector lift of 082).
* **5i** `inner_loweringMid_transfer`, `inner_lowering_transfer_complex`,
  `real_inner_lowering_transfer` — the two-vector, two-source-order lowering transfer (mid /
  complex / real), SL5's only genuinely new analytic content.

## Remaining frontier (the L unit) — as of lane 102

DONE: 5d/5e/5i (095), **5b/5f/5g (102)**.  Still open, in dependency order (reviewer's endgame,
`REVIEW_SL5_COLUMNS.md` §5):

* **5a** — pointwise divergence form, **M, ~80–120 lines**.  No blocker; the only row with genuine
  analytic content still open on the non-`5i` side.  `C01/Trilinear.lean:91-98` supplies
  `hadv`/`hbasis`/`hmap`; advection-form ⇒ divergence-form is `HasFDerivAt.smul` + `PiLp.proj` chain rule
  + divergence-free cancellation + `Fin.sum_univ_three`.
* **5c** — the nonlinear datum, **S–M, ~60–90 lines**.  Needs 5a (field rewrite); `B_j` from
  `A04.exists_outerColumn_datum_succ` (102).  088's `isSobolevDatum_laplacian` with one derivative step;
  the per-column `SmoothL2Field` wrapping is the fiddly part.
* **5h** — the calc assembly, **M, ~100–150 lines**, **runs last**, needs 5c.  Its last two steps already
  close via 5f/5g (102) + 5e (095); only the summed-IBP first step and the #94 order reconciliations
  (glued by 5i) remain.

5a and 5c are **separable lanes that can start in parallel** (5c's datum algebra is independent; only its
field rewrite consumes 5a); 5h waits for 5c.  The seam past 5h — `outerNormAt_le` (`HighEnergy.lean:187`),
whose left side is exactly 5g's right side — needs no new lemma.
