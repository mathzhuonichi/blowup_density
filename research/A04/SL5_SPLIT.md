# A04 unit G1, sub-lemma SL5 — split of the nonlinear pairing (lane 095)

SL5 (`research/A04/G1_SPLIT.md:157-165`, rated **L**) is the `hnl` input of
`A04.inner_energy_assembly` / `inner_energy_Rhigh` (`HighEnergy.lean:100,136`):

```
− ⟪G t, N⟫_ℝ ≤ gradientSobolevNormAt (m:ℝ) u t * (outerSobolevENorm (m:ℝ) (u t·) (u t·)).toReal
```

with `G t` = order-`m` datum of `u(t,·)` (`RealVectorSobolev (m:ℝ)`), and `N` the order-`m`
datum of the **advection slice** `advection u t = (u·∇)u(t,·)` (`MomentumDatum.lean:167-179`:
`hN : IsSobolevDatum (m:ℝ) (fun x => advection w.velocity t x) N`).

> **Branch note.**  This lane branched from `erenup/integration` **before** PR #94 (lane 088,
> `Section4/A04/LaplacianAssembly.lean`) merged.  That PR closed SL3 and supplies the order-transport
> machinery SL5 reuses (`derivDatumStep`, `isSobolevDatum_castOrder`/`castOrder`/`cast_mid_order`/
> `cast_top_order`, `coe_derivDatumStep`, `norm_sq_derivDatumStep`, `isSobolevDatum_lowerVectorL` +
> `coe_lowerVectorL`, `directionalDerivative_orderLowering_comm`, `angularMid_comm`,
> `isSobolevDatum_laplacian`).  The module is **absent from this worktree**; read it with
> `git show origin/erenup/integration:formalization/NSFormalization/Section4/A04/LaplacianAssembly.lean`,
> do **not** import it here.  The table sizes below are as of PR #94.

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
| 5a | div-free pointwise divergence form `advection u t x = ∑_j partialDeriv j (outerColumn z z j) x`, hyps `DifferentiableAt ℝ z x` + `spatialDivergence u t x = 0` (`z := u(t·)`) | identity of `Space` fields | **M** | **DONE** (lane 100: `advection_eq_sum_partialDeriv_outerColumn`, slice form `advection_slice_eq_sum_partialDeriv_outerColumn`; the bridge `convectionDivergence_eq_sum_partialDeriv_outerColumn` is `rfl`; `Section4/A04/AdvectionDivergence.lean`) | `Section4/A04/AdvectionDivergence.lean`: `convectionDivergence_eq_sum_partialDeriv_outerColumn` (the bridge, `rfl`), `advection_eq_sum_partialDeriv_outerColumn` (row 5a, function identity), `advection_slice_eq_sum_partialDeriv_outerColumn` (`ClassicalSolutionR` corollary). Reused lane 093's `convectionDivergence_eq_advection` (no re-proof of Leibniz); step (i) was `rfl` (not `HasFDerivAt.smul`); axioms = the standard 3 |
| 5b | order-`(m+1)` datum of each column `W_j = u_j·u`: `∃ B_j, IsSobolevDatum ((m:ℝ)+1) W_j B_j` | `A03.exists_sobolevDatum` after enorm `≠ ⊤` | **S** | open | `A03.tameProductVector (m+1)` (`VectorTameProduct.lean:256`) ⇒ `sobolevENorm ((m+1:ℕ):ℝ) (outerColumn z z j) ≠ ⊤`, then `A03.exists_sobolevDatum`; needs `MemHmVector (m+1) (u t·)` from `velocity_smooth`. **No `SmoothL2Field` here** (that is 5c's need) |
| 5c | `N = ∑_j (datum_m of ∂_j W_j)` | `N = ∑_j derivDatumStep m j B_j`, via `isSobolevDatum_partialDeriv` (per column, `Z := outerColumnField`) + `isSobolevDatum_add` (over 3 j) + `isSobolevDatum_unique` against `hN` | **M** | **DONE** (lane 105, `Section4/A04/NonlinearDatum.lean`) | Part 1 `outerColumn_smoothL2` + `outerColumnField`/`_field` (each `W_j = u_j·u` is `A05.SmoothL2` from **`MemHInfty z` alone**, via the **datum route** — row 5b at order `max n 2` + lowering + `D01.memHInfty_jets`, **not** a Leibniz jet expansion; F3's `L^∞`-factor argument avoided). Part 2 `isSobolevDatum_advection_sum` (copies 088's `isSobolevDatum_laplacian` with **one** derivative step; field rewritten by lane 100's `advection_eq_sum_partialDeriv_outerColumn`) + `advection_slice_datum_eq` (`ClassicalSolutionR` corollary pinning any `N` to the sum by `isSobolevDatum_unique`). Axioms = standard 3. `B_j` at order `m+1` from row 5b's `exists_outerColumn_datum_succ`; no `castOrder` needed on the `B_j` side |
| 5d.amb | summed real skew-adjointness, ambient carrier: `∑_i ⟪f_i, D g_i⟫ = -∑_i ⟪D f_i, g_i⟫` | `sum_real_inner_angularDirectionalDerivative` | **S** | **DONE (this lane)** | 082 `real_inner_angularDirectionalDerivative` + `Finset.sum_neg_distrib`. This is the form the double-sum IBP consumes (`G_i` order `m`, `B_j i` order `m+1`, on the shared `FourierData`) |
| 5d.sub | vector lift of 082 on the datum carrier (common order `s`): `∑_i ⟪f_i, D g_i⟫ = -∑_i ⟪D f_i, g_i⟫` | `sum_real_inner_angularDirectionalDerivativeReal` | **S** | **DONE (this lane)** | 082 `real_inner_angularDirectionalDerivativeReal` + `Finset.sum_neg_distrib` |
| 5e | discrete Cauchy–Schwarz over a finset of inner products: `∑_j ⟪a_j,b_j⟫ ≤ √(∑‖a_j‖²)·√(∑‖b_j‖²)` (and the `\|·\|` form) | `sum_inner_le_sqrt_mul_sqrt`, `abs_sum_inner_le_sqrt_mul_sqrt`, generic `[InnerProductSpace ℝ E]` | **S** | **DONE (this lane)** | `real_inner_le_norm` / `abs_real_inner_le_norm` + `Real.sum_mul_le_sqrt_mul_sqrt` |
| **5i** | **two-vector, two-source-order lowering transfer**: `⟪Λ_{s→r} v, Λ_{s'→t} w⟫ = ⟪Λ_{s→r'} v, Λ_{s'→t'} w⟫` for `r + t = r' + t'` (mid / complex / real layers) | `inner_loweringMid_transfer`, `inner_lowering_transfer_complex`, `real_inner_lowering_transfer` | **S** | **DONE (this lane)** | generalizes 082's single-vector `inner_loweringMid_pairing`/`…_complex`/`real_inner_lowering_pairing` from one vector to two and from one source order to two; `lowering_mid_symbol_eq` + `sobolevBesselWeight_mul` + `angularFrequencyDilation.inner_map_map` + `real_inner_eq_re_complex`. **SL5's only genuinely new analytic content** |
| 5f.grad | `√(∑_j ‖D_j A'‖²) = gradientSobolevNormAt (m:ℝ) u t`, `A' = datum_{m+1}(u)` | `gradientSobolevENorm_toReal_sq_eq_datum_sum` (`LaplacianDatum.lean:130`) + `Real.sqrt_sq ENNReal.toReal_nonneg` | **S** | open | **no order shift as stated**: the row uses `D_j` on `datum_{m+1}(u)`, exactly what `gradientSobolevENorm_toReal_sq_eq_datum_sum` gives; the shift `D_j G` vs `D_j A'` is 5h/5i's concern, not this row's |
| 5g.outer | `√(∑_j ‖C_j‖²) = (outerSobolevENorm (m:ℝ) z z).toReal`, `C_j = datum_m(W_j)` (≤ suffices) | `columnsSobolevENorm` `.toReal` ℓ² arithmetic of `gradientSobolevENorm_toReal_sq_eq_sum` (`LaplacianDatum.lean:96`) with `outerColumn` for `partialDeriv` + `sobolevENorm_eq` on `C_j` | **S–M** | open | 5b at order `m` (same route, `tameProductVector m`) |
| 5h | assembly: `inner_sum` → 5d → **5i** → 5e at `E = RealVectorSobolev m` → 5f/5g → target | one calc | **S** (was M; reviewer-verified core ≈75 lines) | **DONE** (lane 105, `Section4/A04/NonlinearBound.lean`) | `inner_component_advection` / `inner_datum_advectionDir` / `inner_advection_bound` (reviewer-authored core) + `inner_advection_bound_slice` (`ClassicalSolutionR` corollary, the `hnl` of `inner_energy_assembly`). Order reconciliations `G = Λ_{m+1→m} A'`, `C_j = Λ_{m+1→m} B_j` (`isSobolevDatum_lowerVectorL` + `isSobolevDatum_unique` + `coe_lowerVectorL`) and `D_j(Λ A') = Λ(D_j A')` (`directionalDerivative_orderLowering_comm` + `real_inner_lowering_transfer`). Axioms = standard 3; conformance `example` in `axioms_sl5c.lean` feeds it into `inner_energy_assembly`'s `hnl` slot |

**SL5 is CLOSED.**  All nine rows (5a/5b/5c/5d/5e/5f/5g/5h/5i) are DONE.  The `hnl` of
`A04.inner_energy_assembly` is delivered by `inner_advection_bound_slice`
(`Section4/A04/NonlinearBound.lean`), matching the assembly's slot exactly (conformance `example`).
What G1 still lacks to reach `energyIdentityHigh` is **only `hpr`**, the D01 obligation **P2** (the
pressure datum / Leray-regularity gap) — that is `momentum_datum`'s explicit `hP` hypothesis, not part
of SL5.

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

## Frontier — SL5 CLOSED

**Nothing remains in SL5.**  5a (lane 100), 5b/5f/5g (lane 102), 5d/5e/5i (lane 095), 5c and 5h
(lane 105, `Section4/A04/NonlinearDatum.lean` + `NonlinearBound.lean`) are all **DONE**.  Row 5h's
`inner_advection_bound_slice` is `inner_energy_assembly`'s `hnl` (conformance `example` in
`research/A04/axioms_sl5c.lean` feeds it into the assembly and derives the full energy inequality).

The remaining G1 gap to `energyIdentityHigh` is **only `hpr`** — the pressure drop `⟪G, ∇p datum⟫ = 0`,
i.e. `momentum_datum`'s explicit `hP` hypothesis, which is the D01 obligation **P2** (Leray-regularity
gap).  `hlap` is 088 (`inner_datum_laplacian_le'`), `hnl` is this lane, and `hd`/`hmom`/`hG`/`hF` are
D1/D2/N1/momentum — none blocked.
