import NSFormalization.Section3.T20.CriticalRegularity
import NSFormalization.Section3.T12.CriticalL3Density
import NSFormalization.Section3.T12.GradientLambdaL3

/-!
# T20 unit U7 — the mean-zero critical trilinear estimate (`03-torus.tex:425-431`)

For a smooth periodic mean-zero field `v` on the unit three-torus and a physical
representative `Lv` of `Λv`, the article's displayed estimate

`|⟪(v·∇)v, Λv⟫| ≤ ‖v‖₃ ‖∇v‖₃ ‖Λv‖₃ ≤ C₀ y z²`,  `y = ‖v‖_{Ḣ^{1/2}}`, `z = ‖v‖_{Ḣ^{3/2}}`

is proved here with the explicit constant

`criticalTrilinearConst = CcriticalHalf * CcriticalThreeHalves ^ 2 = 16 * CcriticalHalf ^ 3`.

## Route (`research/T20/T20_SPLIT.md` U7)

1. **§2, pointwise.** `(v·∇)v = advection (lift v) 0` is bounded by
   `‖v x‖ * ‖gradientTensor v x‖` (`Section4.C01.advection_norm_le`, a
   Cauchy–Schwarz over the three columns), so Cauchy–Schwarz for the Euclidean
   inner product gives
   `‖⟪(v·∇)v(x), Lv x⟫‖ₑ ≤ ‖v x‖ₑ ‖∇v x‖ₑ ‖Lv x‖ₑ`.
   This mirrors the whole-space `Section4/R43/Trilinear.lean:228
   criticalAdvectionHolder`.
2. **§1, Hölder.** Three-factor Hölder with exponents `3,3,3`, taken **directly
   against normalized Haar measure on `T³`** rather than through the
   `HaarCube` chart: `periodicLpENorm p w` is *definitionally*
   `eLpNorm (torusLift w) p periodicTorusMeasure`
   (`T12.periodicLpENorm_eq_eLpNorm_torusLift`) and the target integral is itself
   a Haar integral, so no cube transfer is needed.  The measure-general engine is
   Mathlib's `ENNReal.lintegral_prod_norm_pow_le`; §1 repeats the `volume`-bound
   `R43.lintegral_enorm_mul_three_le` for `periodicTorusMeasure`.
   §0 supplies the one missing measurability fact: `torusLift w` is
   a.e.-strongly measurable for continuous `w` with an *arbitrary* normed target
   (`Paper1.measurable_torusLift` covers only `ℂ`, and the gradient tensor lands
   in `WithLp 2 (Fin 3 → Space)`).
3. **§3, embeddings.** `T12.velocityCriticalL3` (lane 401, verbatim U4 field)
   for `‖v‖₃ ≤ CcriticalHalf · y`, and `T12.gradientLambdaCriticalL3` (lane 405,
   verbatim U6 field) for `‖∇v‖₃ + ‖Λv‖₃ ≤ CcriticalThreeHalves · z`, each
   summand being bounded by the sum.

The `ℝ≥0∞` form `criticalTrilinear_enorm` carries no finiteness hypothesis; the
`toReal` form `criticalTrilinear` — the shape U8 consumes at each time — needs
`y, z ≠ ⊤`, which `MemPeriodicHomogeneous (1/2) v` and
`MemPeriodicHomogeneous (3/2) v` already provide (they are the third and fourth
conjuncts of `CriticalRegularityTAPI.reductionRegular`, so U8 gets them for free).
§4 records the two `rfl` bridges U8 needs: the pairing spelling
(`periodicPairing` ↔ the raw Haar integral of the lifted inner product) and the
time-slice spelling (`advection u t · = advection (lift (u (t, ·))) 0 ·`).

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `maxHeartbeats`
override, no named goal input.  Every declaration reduces to
`[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

namespace NSFormalization.Section3.T20

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (Coords toSpace)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section4.A05 (dirDeriv gradTensor)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T12
open scoped ContDiff ENNReal BigOperators

/-! ## §0  Measurability of the canonical torus lift -/

/-- The fundamental-domain chart `T³ → Space` underlying `torusLift` is
measurable.  (`T12/HaarCube.lean` proves the stronger
`MeasurableEmbedding torusChart`, but both it and `torusChart` are `private`
there.) -/
private theorem measurable_torusChart :
    Measurable (fun z : PeriodicTorus ↦
      toSpace ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).val)) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable.comp
    (measurable_subtype_coe.comp (UnitAddTorus.measurableEquivPiIoc (0 : Coords)).measurable)

/-- For a continuous field with an **arbitrary** normed target, the canonical
torus lift is a.e.-strongly measurable against Haar measure.  `Paper1`'s
`measurable_torusLift` is stated only for `ℂ`-valued fields and T10's
`memLp_torusLift_vector` only for `SpatialField`; the gradient tensor takes
values in `WithLp 2 (Fin 3 → Space)`. -/
theorem aestronglyMeasurable_torusLift {E : Type*} [NormedAddCommGroup E]
    {w : Space → E} (hw : Continuous w) :
    AEStronglyMeasurable (torusLift w) periodicTorusMeasure :=
  hw.comp_aestronglyMeasurable measurable_torusChart.aestronglyMeasurable

/-- Continuity of the gradient tensor of a smooth field, in the exact
`WithLp 2 (Fin 3 → Space)` carrier of the registered `gradientTensor` spelling. -/
theorem continuous_gradientTensor {v : SpatialField} (hv : ContDiff ℝ ∞ v) :
    Continuous (gradientTensor v) := by
  show Continuous (fun x ↦
    (WithLp.toLp 2 (fun j : Fin 3 ↦ dirDeriv j v x) : WithLp 2 (Fin 3 → Space)))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ Space)).comp
    (continuous_pi fun j ↦ (contDiff_dirDeriv hv j).continuous)

/-! ## §1  Three-factor Hölder on the probability torus -/

/-- Three-factor Hölder with exponents `3,3,3` against normalized Haar measure on
`T³`, stated for the `ℝ≥0∞` norms of the datum layer.  This is the torus copy of
`Section4/R43/Trilinear.lean:176 lintegral_enorm_mul_three_le`, which is fixed to
`volume` on `Space`; the engine `ENNReal.lintegral_prod_norm_pow_le` is
measure-general. -/
theorem lintegral_enorm_mul_three_le_torus
    {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G]
    {f : PeriodicTorus → E} {g : PeriodicTorus → F} {h : PeriodicTorus → G}
    (hf : AEStronglyMeasurable f periodicTorusMeasure)
    (hg : AEStronglyMeasurable g periodicTorusMeasure)
    (hh : AEStronglyMeasurable h periodicTorusMeasure) :
    ∫⁻ y, ‖f y‖ₑ * ‖g y‖ₑ * ‖h y‖ₑ ∂periodicTorusMeasure ≤
      eLpNorm f 3 periodicTorusMeasure * eLpNorm g 3 periodicTorusMeasure *
        eLpNorm h 3 periodicTorusMeasure := by
  have hpow (a : ℝ≥0∞) : (a ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = a := by
    rw [← ENNReal.rpow_mul]
    norm_num
  have he (q : PeriodicTorus → ℝ≥0∞) :
      (∫⁻ y, q y ^ (3 : ℝ) ∂periodicTorusMeasure) ^ ((1 : ℝ) / 3) =
        eLpNorm q 3 periodicTorusMeasure := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, enorm_eq_self]
  calc
    ∫⁻ y, ‖f y‖ₑ * ‖g y‖ₑ * ‖h y‖ₑ ∂periodicTorusMeasure
        = ∫⁻ y, ∏ i : Fin 3,
            (![fun y ↦ ‖f y‖ₑ ^ (3 : ℝ),
               fun y ↦ ‖g y‖ₑ ^ (3 : ℝ),
               fun y ↦ ‖h y‖ₑ ^ (3 : ℝ)] i y) ^ ((1 : ℝ) / 3)
              ∂periodicTorusMeasure := by
          refine lintegral_congr fun y ↦ ?_
          rw [Fin.prod_univ_three]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons, hpow]
    _ ≤ ∏ i : Fin 3,
          (∫⁻ y, (![fun y ↦ ‖f y‖ₑ ^ (3 : ℝ),
                    fun y ↦ ‖g y‖ₑ ^ (3 : ℝ),
                    fun y ↦ ‖h y‖ₑ ^ (3 : ℝ)] i y) ∂periodicTorusMeasure) ^
            ((1 : ℝ) / 3) := by
          refine ENNReal.lintegral_prod_norm_pow_le (Finset.univ) ?_ ?_ ?_
          · intro i _
            fin_cases i
            · exact hf.enorm.pow_const _
            · exact hg.enorm.pow_const _
            · exact hh.enorm.pow_const _
          · norm_num [Fin.sum_univ_three]
          · intro i _
            norm_num
    _ = eLpNorm f 3 periodicTorusMeasure * eLpNorm g 3 periodicTorusMeasure *
          eLpNorm h 3 periodicTorusMeasure := by
          rw [Fin.prod_univ_three]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons]
          rw [he, he, he]
          rw [eLpNorm_enorm, eLpNorm_enorm, eLpNorm_enorm]

/-! ## §2  The pointwise advection bound -/

/-- `03-torus.tex:427`, pointwise: Cauchy–Schwarz for the Euclidean inner product
followed by the column Cauchy–Schwarz `‖(v·∇)v‖ ≤ ‖v‖ ‖∇v‖`
(`Section4.C01.advection_norm_le`). -/
theorem enorm_inner_advection_le (v Lv : SpatialField) (x : Space) :
    ‖(inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)‖ₑ ≤
      ‖v x‖ₑ * ‖gradientTensor v x‖ₑ * ‖Lv x‖ₑ := by
  have hreal : |(inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)| ≤
      ‖v x‖ * ‖gradientTensor v x‖ * ‖Lv x‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right
        (NSFormalization.Section4.C01.advection_norm_le v x) (norm_nonneg _))
  calc ‖(inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)‖ₑ
      = ENNReal.ofReal |(inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)| :=
        Real.enorm_eq_ofReal_abs _
    _ ≤ ENNReal.ofReal (‖v x‖ * ‖gradientTensor v x‖ * ‖Lv x‖) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ‖v x‖ₑ * ‖gradientTensor v x‖ₑ * ‖Lv x‖ₑ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (norm_nonneg _),
          ofReal_norm, ofReal_norm, ofReal_norm]

/-- The physical Hölder step, on the torus:
`|⟪(v·∇)v, Λv⟫_{L²(T³)}| ≤ ‖v‖₃ ‖∇v‖₃ ‖Λv‖₃`.
Kept in `ℝ≥0∞`, so no integrability premise is needed. -/
theorem criticalAdvectionHolderT (v Lv : SpatialField)
    (hv : SmoothPeriodicT v) (hLv : Continuous Lv) :
    ENNReal.ofReal
        |∫ y : PeriodicTorus,
            torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)) y
              ∂periodicTorusMeasure| ≤
      periodicLpENorm 3 v * periodicLpENorm 3 (gradientTensor v) *
        periodicLpENorm 3 Lv := by
  rw [← Real.enorm_eq_ofReal_abs]
  calc ‖∫ y : PeriodicTorus,
          torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)) y
            ∂periodicTorusMeasure‖ₑ
      ≤ ∫⁻ y, ‖torusLift
            (fun x ↦ (inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)) y‖ₑ
              ∂periodicTorusMeasure := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, ‖torusLift v y‖ₑ * ‖torusLift (gradientTensor v) y‖ₑ *
            ‖torusLift Lv y‖ₑ ∂periodicTorusMeasure :=
        lintegral_mono fun _ ↦ enorm_inner_advection_le v Lv _
    _ ≤ _ :=
        lintegral_enorm_mul_three_le_torus
          (aestronglyMeasurable_torusLift hv.1.continuous)
          (aestronglyMeasurable_torusLift (continuous_gradientTensor hv.1))
          (aestronglyMeasurable_torusLift hLv)

/-! ## §3  The explicit constant and the U7 target -/

/-- `03-torus.tex:426-431`: the explicit `C₀` of the critical trilinear estimate,
the product of the T12 order-`1/2` critical constant with the square of the
order-`3/2` one. -/
def criticalTrilinearConst : ℝ := CcriticalHalf * CcriticalThreeHalves ^ 2

/-- Expanded form of the explicit constant (`CcriticalThreeHalves = 4·CcriticalHalf`). -/
theorem criticalTrilinearConst_eq :
    criticalTrilinearConst = 16 * CcriticalHalf ^ 3 := by
  simp only [criticalTrilinearConst, CcriticalThreeHalves]
  ring

theorem criticalTrilinearConst_pos : 0 < criticalTrilinearConst :=
  mul_pos CcriticalHalf_pos (pow_pos CcriticalThreeHalves_pos 2)

/-- **T20 U7, `03-torus.tex:425-431`, `ℝ≥0∞` form.**
For a smooth periodic field `v` in `Ḣ^{1/2}(T³) ∩ Ḣ^{3/2}(T³)` with a physical
representative `Lv` of `Λv`,
`|⟪(v·∇)v, Λv⟫| ≤ criticalTrilinearConst · y · z²`,
`y = ‖v‖_{Ḣ^{1/2}}`, `z = ‖v‖_{Ḣ^{3/2}}`.  No finiteness hypothesis is needed in
this form. -/
theorem criticalTrilinear_enorm (v Lv : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v)
    (hthree : MemPeriodicHomogeneous (3 / 2) v)
    (hL : IsPeriodicLambda v Lv) :
    ENNReal.ofReal
        |∫ y : PeriodicTorus,
            torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)) y
              ∂periodicTorusMeasure| ≤
      ENNReal.ofReal criticalTrilinearConst *
        periodicHomogeneousENorm (1 / 2) v *
          periodicHomogeneousENorm (3 / 2) v ^ 2 := by
  set Y : ℝ≥0∞ := periodicHomogeneousENorm (1 / 2) v with hY
  set Z : ℝ≥0∞ := periodicHomogeneousENorm (3 / 2) v with hZ
  have hsum : periodicLpENorm 3 (gradientTensor v) + periodicLpENorm 3 Lv ≤
      ENNReal.ofReal CcriticalThreeHalves * Z :=
    gradientLambdaCriticalL3 v Lv hv hthree hL
  have hgrad : periodicLpENorm 3 (gradientTensor v) ≤
      ENNReal.ofReal CcriticalThreeHalves * Z :=
    le_trans le_self_add hsum
  have hlam : periodicLpENorm 3 Lv ≤ ENNReal.ofReal CcriticalThreeHalves * Z :=
    le_trans le_add_self hsum
  have hvel : periodicLpENorm 3 v ≤ ENNReal.ofReal CcriticalHalf * Y :=
    velocityCriticalL3 v hhalf
  have hconst : ENNReal.ofReal criticalTrilinearConst =
      ENNReal.ofReal CcriticalHalf * ENNReal.ofReal CcriticalThreeHalves *
        ENNReal.ofReal CcriticalThreeHalves := by
    have h1 : (0 : ℝ) ≤ CcriticalHalf := CcriticalHalf_pos.le
    have h2 : (0 : ℝ) ≤ CcriticalThreeHalves := CcriticalThreeHalves_pos.le
    rw [criticalTrilinearConst, pow_two, ← mul_assoc,
      ENNReal.ofReal_mul (mul_nonneg h1 h2), ENNReal.ofReal_mul h1]
  calc ENNReal.ofReal
        |∫ y : PeriodicTorus,
            torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)) y
              ∂periodicTorusMeasure|
      ≤ periodicLpENorm 3 v * periodicLpENorm 3 (gradientTensor v) *
          periodicLpENorm 3 Lv :=
        criticalAdvectionHolderT v Lv hv hL.1.1.continuous
    _ ≤ ENNReal.ofReal CcriticalHalf * Y *
          (ENNReal.ofReal CcriticalThreeHalves * Z) *
            (ENNReal.ofReal CcriticalThreeHalves * Z) :=
        mul_le_mul' (mul_le_mul' hvel hgrad) hlam
    _ = ENNReal.ofReal criticalTrilinearConst * Y * Z ^ 2 := by
        rw [hconst, pow_two]; ring

/-- **T20 U7, `03-torus.tex:425-431`, real form — the shape U8 applies at each
interior time to `v = meanFreeVelocity g w.velocity (t, ·)`.**

`|⟪(v·∇)v, Λv⟫| ≤ criticalTrilinearConst · y · z²` with
`y = (criticalY …).toReal` and `z = (criticalZ …).toReal`.  The two finiteness
facts are the fourth conjuncts of `hhalf`/`hthree`, which the
`reductionRegular` field of `CriticalRegularityTAPI` supplies verbatim. -/
theorem criticalTrilinear (v Lv : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v)
    (hthree : MemPeriodicHomogeneous (3 / 2) v)
    (hL : IsPeriodicLambda v Lv) :
    |∫ y : PeriodicTorus,
        torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)) y
          ∂periodicTorusMeasure| ≤
      criticalTrilinearConst * (periodicHomogeneousENorm (1 / 2) v).toReal *
        (periodicHomogeneousENorm (3 / 2) v).toReal ^ 2 := by
  have hYtop : periodicHomogeneousENorm (1 / 2) v ≠ ⊤ := hhalf.2.2.2
  have hZtop : periodicHomogeneousENorm (3 / 2) v ≠ ⊤ := hthree.2.2.2
  have hfin : ENNReal.ofReal criticalTrilinearConst *
      periodicHomogeneousENorm (1 / 2) v *
        periodicHomogeneousENorm (3 / 2) v ^ 2 ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYtop) ?_
    exact ENNReal.pow_ne_top hZtop
  have hmono := ENNReal.toReal_mono hfin
    (criticalTrilinear_enorm v Lv hv hhalf hthree hL)
  rwa [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal criticalTrilinearConst_pos.le] at hmono

/-! ## §4  Spelling bridges for the U8 consumer -/

/-- The canonical T20 pairing `periodicPairing` is the Haar integral of the lifted
pointwise inner product: both sides are the same term. -/
theorem periodicPairing_eq_integral_torusLift_inner (a b : SpatialField) :
    periodicPairing a b =
      ∫ y : PeriodicTorus, torusLift (fun x ↦ (inner ℝ (a x) (b x) : ℝ)) y
        ∂periodicTorusMeasure := rfl

/-- The `periodicPairing` form of U7, for the U8 energy computation. -/
theorem criticalTrilinear_pairing (v Lv : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v)
    (hthree : MemPeriodicHomogeneous (3 / 2) v)
    (hL : IsPeriodicLambda v Lv) :
    |periodicPairing (fun x ↦ advection (lift v) 0 x) Lv| ≤
      criticalTrilinearConst * (periodicHomogeneousENorm (1 / 2) v).toReal *
        (periodicHomogeneousENorm (3 / 2) v).toReal ^ 2 :=
  criticalTrilinear v Lv hv hhalf hthree hL

/-- The time-slice bridge: the space-time advection of `u` at time `t` is the
spatial advection of the slice.  `meanFreeEquation` (U6) produces the left side,
U7 consumes the right side. -/
theorem advection_eq_slice (u : SpaceTimeField) (t : ℝ) (x : Space) :
    advection u t x = advection (lift (fun y ↦ u (t, y))) 0 x := rfl

end NSFormalization.Section3.T20
