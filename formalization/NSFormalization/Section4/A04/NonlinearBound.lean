import NSFormalization.Section4.A04.NonlinearDatum
import NSFormalization.Section4.A04.NonlinearPairing

/-!
# A04 unit G1, sub-lemma SL5 row 5h: the nonlinear pairing bound (`hnl`)

Task `A04` (graph node `formalization/blueprint/DEPENDENCY_GRAPH.md`), the force-density energy
estimate `eq:Rhigh` (`paper/sections/appendix-a-local-theory.tex:132`).  Row 5h of the SL5 split
(`research/A04/SL5_SPLIT.md`) is the final assembly: it delivers the `hnl` hypothesis of
`A04.inner_energy_assembly` / `inner_energy_Rhigh` (`HighEnergy.lean:100,136`),

`− ⟪G, N⟫_ℝ ≤ gradientSobolevNormAt (m:ℝ) u t · (outerSobolevENorm (m:ℝ) (u t·) (u t·)).toReal`,

with `G` the order-`m` datum of `u(t,·)` and `N` the order-`m` datum of the advection slice
`(u·∇)u(t,·)` (the `hN` shape of `A04.momentum_datum`).

## Provenance

The analytic core (`inner_component_advection`, `inner_datum_advectionDir` and the general slice bound
`inner_advection_bound`, the reviewer's `sl5h_full`) was written and compiled by the lane-105
reviewer (`research/A04/REVIEW_SL5C.md` §5–6) on top of lane 105's row-5c results.  This module
reproduces it verbatim, adds the `ClassicalSolutionR` slice corollary `inner_advection_bound_slice`,
and folds in the reviewer's notes (`Ioo → Ico` glue, the exact `Paper3` namespaces).

## Route

Componentwise integration by parts on the ambient `Lp ℂ 2` carrier, then discrete Cauchy–Schwarz, then
the two ℓ² norm identifications (rows 5f/5g, lane 102):

* `inner_component_advection` — per component `i`: skew-adjointness `real_inner_angularDirectionalDerivative`
  (5d, `Paper3`) peels one `D_j` onto `Gᵢ`, `directionalDerivative_orderLowering_comm` (088) commutes
  `D_j` past the lowering, and `real_inner_lowering_transfer` (5i, `Paper3`) with `angularOrderLowering_self`
  closes it as `⟪Gᵢ, D_j Bᵢ⟫ = −⟪D_j A'ᵢ, Λ Bᵢ⟫`.  The only `(m:ℝ)+1−1 = (m:ℝ)` normalisation is an
  explicit `simp only [show … from by ring]`.
* `inner_datum_advectionDir` — sums the components on the datum carrier via `realSobolev_inner_eq_ambient`,
  `coe_derivDatumStep` (088) and `coe_lowerVectorL` (088).
* `inner_advection_bound` — the three order reconciliations `G = Λ_{m+1→m} A'`,
  `Cⱼ = Λ_{m+1→m} Bⱼ` (`isSobolevDatum_lowerVectorL` + `isSobolevDatum_unique`), the integration by
  parts `−⟪G,N⟫ = ∑ⱼ ⟪D_j A', Cⱼ⟫`, then `sum_inner_le_sqrt_mul_sqrt` (5e) and the two identifications
  `sqrt_sum_norm_sq_derivDatumStep_eq_slice` (5f), `sqrt_sum_norm_sq_columnData_eq` (5g).
* `inner_advection_bound_slice` — the `ClassicalSolutionR` corollary: `hsl`/`MemHInfty` of the slice
  from `C01.velocity_slice_smoothL2` / `C01.velocity_slice_memHInfty`, the order-`(m+1)` slice datum
  `A'` from the slice's `MemHInfty` (cast by `cast_mid_order`), the per-column data `B` from
  `exists_outerColumn_datum_succ` (row 5b), and `N = ∑ⱼ D_j Bⱼ` from row 5c's `advection_slice_datum_eq`.
  `t ∈ Ioo 0 T` (the `momentum_datum` regime) is glued to the `Ico` sources by `⟨le_of_lt ht.1, ht.2⟩`.

## Reuse

Nothing here restates a definition.  `real_inner_angularDirectionalDerivative`,
`real_inner_lowering_transfer`, `angularOrderLowering_self`, `realSobolev_inner_eq_ambient`,
`angularDirectionalDerivative`, `angularOrderLowering` are `NSFormalization.Paper3`'s;
`directionalDerivative_orderLowering_comm`, `coe_derivDatumStep`, `coe_lowerVectorL`, `derivDatumStep`,
`isSobolevDatum_lowerVectorL`, `castOrder`, `cast_mid_order`, `isSobolevDatum_castOrder`,
`sum_inner_le_sqrt_mul_sqrt`, `sqrt_sum_norm_sq_derivDatumStep_eq_slice`,
`sqrt_sum_norm_sq_columnData_eq`, `gradientSobolevNormAt`, `outerColumnField`,
`advection_slice_datum_eq`, `exists_outerColumn_datum_succ` are `NSFormalization.Section4.A04`'s (this
namespace); `isSobolevDatum_unique`, `lowerVectorL` are D01's; `velocity_slice_smoothL2`,
`velocity_slice_memHInfty` are C01's.
-/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement

namespace NSFormalization.Section4.A04

open NSFormalization.Section4.D01 (IsSobolevDatum isSobolevDatum_unique lowerVectorL)
open NSFormalization.Section4.A03 (outerColumn outerSobolevENorm)
open NSFormalization.Section4.A02 (SpaceTimeField ClassicalSolutionR SpatialField)
open NSFormalization.Paper3 (RealVectorSobolev angularDirectionalDerivative angularOrderLowering
  real_inner_angularDirectionalDerivative real_inner_lowering_transfer angularOrderLowering_self
  realSobolev_inner_eq_ambient)
open NSFormalization.Source.RealSobolev (RealSobolevHilbert)

/-! ## 1. Per-component and per-direction integration by parts

Reviewer-authored (`research/A04/REVIEW_SL5C.md` §5), reproduced verbatim. -/

/-- **Per component (reviewer-authored, REVIEW_SL5C §5).**  With `Gᵢ = Λ_{m+1→m}(A'ᵢ)`,
`⟪Gᵢ, D_j Bᵢ⟫_ℝ = −⟪D_j A'ᵢ, Λ_{m+1→m}(Bᵢ)⟫_ℝ`: skew-adjointness peels `D_j` onto `Gᵢ`, the
commutation turns `D_j(Λ A'ᵢ)` into `Λ(D_j A'ᵢ)`, and the two-vector lowering transfer closes it. -/
theorem inner_component_advection (m : ℕ) (e : Space)
    (Gi A'i Bi : Lp ℂ 2 (volume : Measure Space))
    (hG : Gi = angularOrderLowering ((m : ℝ) + 1) (m : ℝ) (by linarith) A'i) :
    (inner ℝ Gi (angularDirectionalDerivative ((m : ℝ) + 1) e Bi) : ℝ)
      = - (inner ℝ (angularDirectionalDerivative ((m : ℝ) + 1) e A'i)
            (angularOrderLowering ((m : ℝ) + 1) (m : ℝ) (by linarith) Bi) : ℝ) := by
  rw [real_inner_angularDirectionalDerivative ((m : ℝ) + 1) e Gi Bi]
  congr 1
  rw [hG, directionalDerivative_orderLowering_comm ((m : ℝ) + 1) ((m : ℝ) + 1) ((m : ℝ) + 1)
    (m : ℝ) e (by linarith) (by linarith) A'i]
  have htr := real_inner_lowering_transfer ((m : ℝ) + 1 - 1) ((m : ℝ) + 1) ((m : ℝ) - 1)
    ((m : ℝ) + 1) (m : ℝ) (m : ℝ) (by ring) (by linarith) (le_refl _) (by linarith) (by linarith)
    (angularDirectionalDerivative ((m : ℝ) + 1) e A'i) Bi
  rw [angularOrderLowering_self] at htr
  simp only [show (m : ℝ) + 1 - 1 = (m : ℝ) from by ring] at htr ⊢
  rw [angularOrderLowering_self] at htr
  exact htr

/-- **Per direction (reviewer-authored, REVIEW_SL5C §5).**  `⟪G, D_j B⟫_ℝ = −⟪D_j A', Λ_{m+1→m} B⟫_ℝ`
on the datum carrier, from `inner_component_advection` summed over the three components. -/
theorem inner_datum_advectionDir (m : ℕ) (j : Fin 3)
    {G : RealVectorSobolev (m : ℝ)} {A' B : RealVectorSobolev ((m : ℝ) + 1)}
    (hGA' : ∀ i, ((G i : RealSobolevHilbert (m : ℝ)) : Lp ℂ 2 (volume : Measure Space))
      = angularOrderLowering ((m : ℝ) + 1) (m : ℝ) (by linarith)
          ((A' i : Lp ℂ 2 (volume : Measure Space)))) :
    (inner ℝ G (derivDatumStep m j B) : ℝ)
      = - (inner ℝ (derivDatumStep m j A')
            (lowerVectorL ((m : ℝ) + 1) (m : ℝ) (by linarith) B) : ℝ) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [realSobolev_inner_eq_ambient, realSobolev_inner_eq_ambient, coe_derivDatumStep,
    coe_derivDatumStep, coe_lowerVectorL, hGA']
  exact inner_component_advection m (coordinateVector j) _ _ _ rfl

/-! ## 2. The nonlinear pairing bound -/

/-- **SL5 row 5h, general slice form (reviewer-authored core, REVIEW_SL5C §5).**  For a smooth
`L²` slice `x ↦ u(t,x)` with order-`m` datum `G`, order-`(m+1)` datum `A'`, per-column order-`(m+1)`
data `B` of `Wⱼ = uⱼ·u`, and `N = ∑ⱼ derivDatumStep m j Bⱼ` (row 5c's identification of the advection
datum):

`− ⟪G, N⟫_ℝ ≤ gradientSobolevNormAt (m:ℝ) u t · (outerSobolevENorm (m:ℝ) (u t·) (u t·)).toReal`.

The datum lowering `Cⱼ := Λ_{m+1→m} Bⱼ` is the order-`m` column datum (`isSobolevDatum_lowerVectorL`);
`G = Λ_{m+1→m} A'` (`isSobolevDatum_unique`); the integration by parts is
`inner_datum_advectionDir`; the Cauchy–Schwarz step is `sum_inner_le_sqrt_mul_sqrt`; the two factors
are identified by `sqrt_sum_norm_sq_derivDatumStep_eq_slice` (5f) and `sqrt_sum_norm_sq_columnData_eq`
(5g). -/
theorem inner_advection_bound {u : SpaceTimeField} {t : ℝ} (m : ℕ)
    (hsl : NSFormalization.Section4.A05.SmoothL2 (fun x => u (t, x)))
    {G : RealVectorSobolev (m : ℝ)} {A' : RealVectorSobolev ((m : ℝ) + 1)}
    (hG : IsSobolevDatum (m : ℝ) (fun x => u (t, x)) G)
    (hA' : IsSobolevDatum ((m : ℝ) + 1) (fun x => u (t, x)) A')
    {B : Fin 3 → RealVectorSobolev ((m : ℝ) + 1)}
    (hB : ∀ j, IsSobolevDatum ((m : ℝ) + 1)
      (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) j) (B j))
    {N : RealVectorSobolev (m : ℝ)}
    (hN : N = ∑ j : Fin 3, derivDatumStep m j (B j)) :
    - (inner ℝ G N : ℝ)
      ≤ gradientSobolevNormAt (m : ℝ) u t
        * (outerSobolevENorm (m : ℝ) (fun y => u (t, y)) (fun y => u (t, y))).toReal := by
  have hle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  set C : Fin 3 → RealVectorSobolev (m : ℝ) :=
    fun j => lowerVectorL ((m : ℝ) + 1) (m : ℝ) hle (B j) with hCdef
  have hC : ∀ j, IsSobolevDatum (m : ℝ)
      (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) j) (C j) :=
    fun j => isSobolevDatum_lowerVectorL ((m : ℝ) + 1) (m : ℝ) hle (hB j)
  have hGeq : G = lowerVectorL ((m : ℝ) + 1) (m : ℝ) hle A' :=
    isSobolevDatum_unique hG (isSobolevDatum_lowerVectorL ((m : ℝ) + 1) (m : ℝ) hle hA')
  have hGA' : ∀ i, ((G i : RealSobolevHilbert (m : ℝ)) : Lp ℂ 2 (volume : Measure Space))
      = angularOrderLowering ((m : ℝ) + 1) (m : ℝ) hle
          ((A' i : Lp ℂ 2 (volume : Measure Space))) := by
    intro i; rw [hGeq, coe_lowerVectorL]
  have hIBP : - (inner ℝ G N : ℝ)
      = ∑ j : Fin 3, (inner ℝ (derivDatumStep m j A') (C j) : ℝ) := by
    rw [hN, inner_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [inner_datum_advectionDir m j hGA', neg_neg]
  calc - (inner ℝ G N : ℝ)
      = ∑ j : Fin 3, (inner ℝ (derivDatumStep m j A') (C j) : ℝ) := hIBP
    _ ≤ Real.sqrt (∑ j : Fin 3, ‖derivDatumStep m j A'‖ ^ 2)
          * Real.sqrt (∑ j : Fin 3, ‖C j‖ ^ 2) :=
        sum_inner_le_sqrt_mul_sqrt Finset.univ _ _
    _ = gradientSobolevNormAt (m : ℝ) u t
          * (outerSobolevENorm (m : ℝ) (fun y => u (t, y)) (fun y => u (t, y))).toReal := by
        rw [sqrt_sum_norm_sq_derivDatumStep_eq_slice m hsl hA',
          sqrt_sum_norm_sq_columnData_eq m hC]

/-- **SL5 row 5h, the `ClassicalSolutionR` slice corollary — the `hnl` of `inner_energy_assembly`.**
For a classical whole-space solution `w`, `t ∈ (0,T)` (the `momentum_datum` regime) and `2 ≤ m`, with
`G` the order-`m` datum of the velocity slice and `N` **any** order-`m` datum of the advection slice
(the `hN` shape of `momentum_datum`),

`− ⟪G, N⟫_ℝ ≤ gradientSobolevNormAt (m:ℝ) w.velocity t
              · (outerSobolevENorm (m:ℝ) (w.velocity t·) (w.velocity t·)).toReal`.

Discharges `inner_advection_bound`'s hypotheses from the solution: the slice is smooth `L²` and in
`MemHInfty` (`C01.velocity_slice_smoothL2` / `C01.velocity_slice_memHInfty`), its order-`(m+1)` datum
`A'` comes from the `MemHInfty` conjunct (integer order `m+1` cast to `(m:ℝ)+1` by `cast_mid_order`),
the per-column order-`(m+1)` data `B` from `exists_outerColumn_datum_succ` (row 5b, needing
`MemHmVector (m+1)` from the slice's jets), and `N = ∑ⱼ D_j Bⱼ` from row 5c's
`advection_slice_datum_eq`.  `Ioo 0 T` is glued to the `Ico`-stated sources by `⟨le_of_lt ht.1, ht.2⟩`. -/
theorem inner_advection_bound_slice
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {G N : RealVectorSobolev (m : ℝ)}
    (hG : IsSobolevDatum (m : ℝ) (fun x => w.velocity (t, x)) G)
    (hN : IsSobolevDatum (m : ℝ) (fun x => advection w.velocity t x) N) :
    - (inner ℝ G N : ℝ)
      ≤ gradientSobolevNormAt (m : ℝ) w.velocity t
        * (outerSobolevENorm (m : ℝ)
            (fun x => w.velocity (t, x)) (fun x => w.velocity (t, x))).toReal := by
  have ht' : t ∈ Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  have hsl := NSFormalization.Section4.C01.velocity_slice_smoothL2 w ht'
  -- the per-column order-`(m+1)` data (row 5b)
  have hmv : NSFormalization.Section4.A03.MemHmVector (m + 1) (fun x => w.velocity (t, x)) :=
    NSFormalization.Section4.A03.SmoothL2.memHmVector hsl (m + 1)
  choose B hB using fun j => exists_outerColumn_datum_succ m (by omega) hmv j
  -- the order-`(m+1)` slice datum, cast from the integer order
  obtain ⟨A0, hA0⟩ := (NSFormalization.Section4.C01.velocity_slice_memHInfty w ht').2 (m + 1)
  have hA' := isSobolevDatum_castOrder (cast_mid_order m) hA0
  -- `N` is the column-derivative sum (row 5c)
  have hNsum := advection_slice_datum_eq w m ht' hN hB
  exact inner_advection_bound m hsl hG hA' hB hNsum

end NSFormalization.Section4.A04
