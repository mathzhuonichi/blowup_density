import NSFormalization.Section4.A04.LaplacianAssembly
import NSFormalization.Section4.A03.OuterTameProduct

/-!
# A04 unit G1, sub-lemma SL5 — column data and the two norm identifications (rows 5b, 5f, 5g)

`research/A04/SL5_SPLIT.md`, rows **5b**, **5f.grad** and **5g.outer** (all rated S / S–M,
independent of 5a/5c/5h).  SL5 is the `hnl` input of `A04.inner_energy_assembly` /
`inner_energy_Rhigh` (`HighEnergy.lean:100,136`):

`− ⟪G t, N⟫_ℝ ≤ gradientSobolevNormAt (m:ℝ) u t · (outerSobolevENorm (m:ℝ) (u t·) (u t·)).toReal`,

whose right-hand factors are `√(∑ⱼ ‖Dⱼ(datum_{m+1} u)‖²)` (the gradient norm, row 5f) and
`√(∑ⱼ ‖datum_m Wⱼ‖²)` (the outer norm over the columns `Wⱼ = uⱼ·u`, row 5g); the column data
`datum Wⱼ` themselves are furnished by row 5b.  This module supplies the three ingredients;
the calc assembly (5h) and the pointwise divergence form (5a) are elsewhere.

## Contents

* **5b** (`exists_outerColumn_datum_succ`, `exists_outerColumn_datum`) — for a field `z` in the
  admissible class `A03.MemHmVector`, each column `Wⱼ = outerColumn z z j` has an order-`(m+1)`
  (resp. order-`m`) Sobolev datum.  Route: `A03.outerProductTame` (or `tameProductVector`)
  ⇒ `sobolevENorm (outerColumn z z j) ≠ ⊤` (via `A03.le_columnsSobolevENorm`) ⇒
  `A03.exists_sobolevDatum`.  Finiteness of the low `H²` factor comes from
  `A03.sobolevENorm_two_le`; the `((m+1:ℕ):ℝ)` vs `(m:ℝ)+1` cast in the `succ` version is bridged
  by lane 088's `A04.isSobolevDatum_castOrder`/`castOrder` (`cast_mid_order`).

* **5f** (`sqrt_sum_norm_sq_derivDatumStep_eq`, `sqrt_sum_norm_sq_derivDatumStep_eq_slice`) — the
  gradient norm identification `√(∑ⱼ ‖Dⱼ A'‖²) = (gradientSobolevENorm (m:ℝ) Z.field).toReal` for
  `A' = datum_{m+1}(Z.field)`, from `A04.gradientSobolevENorm_toReal_sq_eq_datum_sum`
  (`LaplacianDatum.lean:130`) — whose right-hand summand is definitionally `‖derivDatumStep m j A'‖²`
  — and `Real.sqrt_sq`.  The slice corollary states the right-hand side as
  `gradientSobolevNormAt (m:ℝ) u t`; the bridge is an explicit `have … := rfl` (as lane 088 warns,
  a direct `exact` on this defeq unfolds `gradientSobolevENorm → columnsSobolevENorm → sobolevENorm`,
  an `⨅` over a subtype of data, and burns the heartbeat budget at `isDefEq`).

* **5g** (`columnsSobolevENorm_toReal_sq_eq_sum`, `outerSobolevENorm_toReal_sq_eq_sum`,
  `sqrt_sum_norm_sq_columnData_eq`) — the outer norm identification
  `√(∑ⱼ ‖Cⱼ‖²) = (outerSobolevENorm (m:ℝ) z z).toReal` for `Cⱼ = datum_m(Wⱼ)`.  The ℓ²/`.toReal`
  arithmetic of `columnsSobolevENorm` mirrors `A04.gradientSobolevENorm_toReal_sq_eq_sum`
  (`LaplacianDatum.lean:96`) with a general column family; each column norm is `‖Cⱼ‖` by
  `sobolevENorm_eq` (resolves to `A04.sobolevENorm_eq`, `Forcing.lean:126`, proof-identical to the
  `A03` one), and finiteness of the columns is free from the data `Cⱼ` (an `‖·‖ₑ` is never
  `⊤`), so no `tameProductVector` bound is needed once the data are in hand.
-/

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open scoped ENNReal

namespace NSFormalization.Section4.A04

open NSFormalization.Section4.D01 (sobolevENorm IsSobolevDatum)
open NSFormalization.Section4.A03
  (MemHmVector outerColumn outerSobolevENorm columnsSobolevENorm gradientSobolevENorm
    le_columnsSobolevENorm outerProductTame sobolevENorm_two_le exists_sobolevDatum)
open NSFormalization.Paper3 (RealVectorSobolev angularDirectionalDerivativeReal)
open EulerLpTranslation (SmoothL2Field)

/-! ## 1. Row 5b — Sobolev data of the outer-product columns -/

/-- **Row 5b, order `m`.**  For a field `z` in the admissible class `A03.MemHmVector m` and each
`j`, the column `Wⱼ = outerColumn z z j = uⱼ·u` has an order-`m` Sobolev datum.

The column norm is dominated by the Frobenius assembly (`A03.le_columnsSobolevENorm`), which is
`outerSobolevENorm (m:ℝ) z z` and is bounded by `A03.outerProductTame`; both bounding factors —
`sobolevENorm 2 z` (from `A03.sobolevENorm_two_le`) and `sobolevENorm (m:ℝ) z` (from `hz`) — are
finite, so the column norm is finite and `A03.exists_sobolevDatum` produces the datum. -/
theorem exists_outerColumn_datum (m : ℕ) (hm : 2 ≤ m) {z : Space → Space}
    (hz : MemHmVector m z) (j : Fin 3) :
    ∃ C : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) (outerColumn z z j) C := by
  have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hz2 : sobolevENorm 2 z ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hz.2)
      (sobolevENorm_two_le m h2 z)
  have hcol : sobolevENorm (m : ℝ) (outerColumn z z j) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hz2 hz.2))
      ((le_columnsSobolevENorm (m : ℝ) (outerColumn z z) j).trans (outerProductTame m hm hz))
  exact exists_sobolevDatum hcol

/-- **Row 5b, order `m+1`.**  The same at order `m+1`, needed on the column side of the SL5 IBP,
where `isSobolevDatum_partialDeriv` forces the order `m+1`.  Directly the order-`m` version at `m+1`
(whose class `MemHmVector (m+1) z` this lemma already assumes), transported from the natural-cast
order `((m+1:ℕ):ℝ)` to `(m:ℝ)+1` by `isSobolevDatum_castOrder` (`cast_mid_order`).  Only `1 ≤ m` is
needed (so that `2 ≤ m+1` for the order-`m` lemma): a strictly stronger statement than the SL5 regime
`2 ≤ m`, still consumed by 5c. -/
theorem exists_outerColumn_datum_succ (m : ℕ) (hm : 1 ≤ m) {z : Space → Space}
    (hz : MemHmVector (m + 1) z) (j : Fin 3) :
    ∃ B : RealVectorSobolev ((m : ℝ) + 1), IsSobolevDatum ((m : ℝ) + 1) (outerColumn z z j) B := by
  obtain ⟨A, hA⟩ := exists_outerColumn_datum (m + 1) (by omega) hz j
  exact ⟨castOrder (cast_mid_order m) A, isSobolevDatum_castOrder (cast_mid_order m) hA⟩

/-! ## 2. Row 5f — the gradient norm identification -/

/-- **Row 5f.grad.**  For a smooth square-integrable field `Z` with an order-`(m+1)` datum `A'` of
`Z.field`, the ℓ² norm of the three directional-derivative data equals the gradient norm:
`√(∑ⱼ ‖Dⱼ A'‖²) = (gradientSobolevENorm (m:ℝ) Z.field).toReal`.

`A04.gradientSobolevENorm_toReal_sq_eq_datum_sum` gives the squared identity, and its right-hand
summand is definitionally `‖derivDatumStep m j A'‖²` (both are the norm of
`WithLp.toLp 2 fun i => angularDirectionalDerivativeReal ((m:ℝ)+1) eⱼ (A' i)`); `Real.sqrt_sq`
strips the square. -/
theorem sqrt_sum_norm_sq_derivDatumStep_eq {Z : SmoothL2Field Space} (m : ℕ)
    {A' : RealVectorSobolev ((m : ℝ) + 1)} (hA' : IsSobolevDatum ((m : ℝ) + 1) Z.field A') :
    Real.sqrt (∑ j : Fin 3, ‖derivDatumStep m j A'‖ ^ 2)
      = (gradientSobolevENorm (m : ℝ) Z.field).toReal := by
  have hsum : (∑ j : Fin 3, ‖derivDatumStep m j A'‖ ^ 2)
      = (gradientSobolevENorm (m : ℝ) Z.field).toReal ^ 2 :=
    (gradientSobolevENorm_toReal_sq_eq_datum_sum m hA').symm
  rw [hsum, Real.sqrt_sq ENNReal.toReal_nonneg]

/-- **Row 5f.grad, slice form.**  For a smooth `L²` time-`t` slice `x ↦ u(t,x)` with an
order-`(m+1)` datum `A'`, the same identification with `gradientSobolevNormAt (m:ℝ) u t` on the
right.  The bridge `gradientSobolevNormAt (m:ℝ) u t = (gradientSobolevENorm (m:ℝ) Z.field).toReal`
is an explicit `have … := rfl` on the `SmoothL2Field` repackaging `Z` of the slice, as lane 088's
`inner_datum_laplacian_le'` records: inlining it into `exact` blows the heartbeat budget at
`isDefEq`. -/
theorem sqrt_sum_norm_sq_derivDatumStep_eq_slice (m : ℕ)
    {u : NSFormalization.Section4.A02.SpaceTimeField} {t : ℝ}
    (hsl : NSFormalization.Section4.A05.SmoothL2 (fun x => u (t, x)))
    {A' : RealVectorSobolev ((m : ℝ) + 1)}
    (hA' : IsSobolevDatum ((m : ℝ) + 1) (fun x => u (t, x)) A') :
    Real.sqrt (∑ j : Fin 3, ‖derivDatumStep m j A'‖ ^ 2) = gradientSobolevNormAt (m : ℝ) u t := by
  let Z : SmoothL2Field Space := ⟨fun x => u (t, x), hsl.1, hsl.2⟩
  have hg : gradientSobolevNormAt (m : ℝ) u t = (gradientSobolevENorm (m : ℝ) Z.field).toReal := rfl
  rw [hg]
  exact sqrt_sum_norm_sq_derivDatumStep_eq (Z := Z) m hA'

/-! ## 3. Row 5g — the outer norm identification -/

/-- The squared `.toReal` of a Frobenius column-assembly is the sum of the squared `.toReal` column
norms, whenever each column norm is finite.  Pure `ENNReal.toReal` arithmetic on the
`columnsSobolevENorm` definition; the general column family behind
`A04.gradientSobolevENorm_toReal_sq_eq_sum` (`LaplacianDatum.lean:96`). -/
theorem columnsSobolevENorm_toReal_sq_eq_sum {s : ℝ} {T : Fin 3 → Space → Space}
    (hfin : ∀ j : Fin 3, sobolevENorm s (T j) ≠ ⊤) :
    (columnsSobolevENorm s T).toReal ^ 2 = ∑ j : Fin 3, (sobolevENorm s (T j)).toReal ^ 2 := by
  unfold columnsSobolevENorm
  rw [← ENNReal.toReal_rpow,
    ← Real.rpow_natCast ((∑ j : Fin 3, sobolevENorm s (T j) ^ (2 : ℝ)).toReal ^ (2 : ℝ)⁻¹) 2,
    ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num
  rw [ENNReal.toReal_sum (fun j _ => ENNReal.pow_ne_top (hfin j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.toReal_pow]

/-- The outer-norm specialization of `columnsSobolevENorm_toReal_sq_eq_sum`:
`(outerSobolevENorm s z z).toReal² = ∑ⱼ (sobolevENorm s Wⱼ).toReal²`. -/
theorem outerSobolevENorm_toReal_sq_eq_sum {s : ℝ} {z : Space → Space}
    (hfin : ∀ j : Fin 3, sobolevENorm s (outerColumn z z j) ≠ ⊤) :
    (outerSobolevENorm s z z).toReal ^ 2
      = ∑ j : Fin 3, (sobolevENorm s (outerColumn z z j)).toReal ^ 2 :=
  columnsSobolevENorm_toReal_sq_eq_sum hfin

/-- **Row 5g.outer.**  For order-`m` data `Cⱼ` of the outer-product columns `Wⱼ = outerColumn z z j`,
the ℓ² norm of the column data equals the outer Sobolev norm:
`√(∑ⱼ ‖Cⱼ‖²) = (outerSobolevENorm (m:ℝ) z z).toReal`.

Each column norm is `‖Cⱼ‖` by `sobolevENorm_eq` (`A04.sobolevENorm_eq`, `Forcing.lean:126`), and is
`≠ ⊤` because an `‖·‖ₑ` never is — so
the finiteness needed by `outerSobolevENorm_toReal_sq_eq_sum` is free from the data, no
`tameProductVector` bound required.  `Real.sqrt_sq` strips the square. -/
theorem sqrt_sum_norm_sq_columnData_eq (m : ℕ) {z : Space → Space}
    {C : Fin 3 → RealVectorSobolev (m : ℝ)}
    (hC : ∀ j : Fin 3, IsSobolevDatum (m : ℝ) (outerColumn z z j) (C j)) :
    Real.sqrt (∑ j : Fin 3, ‖C j‖ ^ 2) = (outerSobolevENorm (m : ℝ) z z).toReal := by
  have hfin : ∀ j : Fin 3, sobolevENorm (m : ℝ) (outerColumn z z j) ≠ ⊤ := by
    intro j; rw [sobolevENorm_eq (hC j)]; exact enorm_ne_top
  have hsum : (∑ j : Fin 3, ‖C j‖ ^ 2) = (outerSobolevENorm (m : ℝ) z z).toReal ^ 2 := by
    rw [outerSobolevENorm_toReal_sq_eq_sum hfin]
    apply Finset.sum_congr rfl
    intro j _
    rw [sobolevENorm_eq (hC j), toReal_enorm]
  rw [hsum, Real.sqrt_sq ENNReal.toReal_nonneg]

end NSFormalization.Section4.A04
