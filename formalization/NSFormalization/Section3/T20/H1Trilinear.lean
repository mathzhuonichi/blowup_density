import NSFormalization.Section3.T20.CriticalRegularity
import NSFormalization.Section3.T12.CriticalL3Density
import NSFormalization.Section3.T12.GradientLSix

/-!
# T20 unit U10a — the mean-zero `H¹` trilinear estimate (`03-torus.tex:467-477`)

For a smooth periodic mean-zero field `v` on the unit three-torus the article's
displayed estimate inside the `H¹` energy computation

`|⟪(v·∇)v, Δv⟫| ≤ ‖v‖₃ ‖∇v‖₆ ‖Δv‖₂ ≤ C₁ y ‖Δv‖₂²`,  `y = ‖v‖_{Ḣ^{1/2}}`

is proved here with the explicit constant

`h1TrilinearConst = CcriticalHalf * Csix`.

## Route (`research/T20/T20_SPLIT.md` U10a)

1. **§0, pointwise.**  `(v·∇)v = advection (lift v) 0` is bounded by
   `‖v x‖ * ‖gradientTensor v x‖` (`Section4.C01.advection_norm_le`, a
   Cauchy–Schwarz over the three columns), so Cauchy–Schwarz for the Euclidean
   inner product gives
   `‖⟪(v·∇)v(x), Δv x⟫‖ₑ ≤ ‖v x‖ₑ ‖∇v x‖ₑ ‖Δv x‖ₑ`.
2. **§1, Hölder.**  Three-factor Hölder with the U10a exponents `(3, 6, 2)` —
   `1/3 + 1/6 + 1/2 = 1` — taken **directly against normalized Haar measure on
   `T³`** rather than through the `HaarCube` chart: `periodicLpENorm p w` is
   *definitionally* `eLpNorm (torusLift w) p periodicTorusMeasure` and the
   estimated quantity is itself a Haar integral, so no cube transfer is needed.
   The engine is Mathlib's `ENNReal.lintegral_prod_norm_pow_le`, which is
   general in the measure **and** in the exponent vector, so only the exponent
   vector changes relative to lane 413's `(3,3,3)` U7 lemma
   `Section3/T20/CriticalTrilinear.lean lintegral_enorm_mul_three_le_torus`.
3. **§2, embeddings.**  `T12.velocityCriticalL3` (lane 401, verbatim T12 U4
   field) for `‖v‖₃ ≤ CcriticalHalf · y`, and `T12.gradientLSix` (lane 400,
   verbatim T12 U5 field) for `‖∇v‖₆ ≤ Csix · ‖Δv‖₂`.  Both are already stated
   in exactly the spellings §1 produces — `periodicLpENorm 3 v`,
   `periodicLpENorm 6 (gradientTensor v)`, `periodicLpENorm 2 (laplacian v)` —
   so the article's auxiliary Fourier remark `‖∇(∂ⱼv)‖₂ ≤ ‖Δv‖₂`
   (`03-torus.tex:475-477`) is internal to `gradientLSix` and is not re-derived
   here.

## Why §0 restates three lane-413 helpers instead of importing them

`Section3/T12/GradientLSix.lean:184` and `Section3/T12/GradientLambdaL3.lean:210`
**both** declare `NSFormalization.Section3.T12.contDiff_dirDeriv` (the first for
an arbitrary normed target, the second for `SpatialField`; same proof).  Lean
therefore refuses any module importing both, and
`Section3/T20/CriticalTrilinear.lean` imports `GradientLambdaL3`:

```
error: import NSFormalization.Section3.T12.GradientLSix failed, environment
already contains 'NSFormalization.Section3.T12.contDiff_dirDeriv'
from NSFormalization.Section3.T12.GradientLambdaL3
```

U10a needs `gradientLSix`, so it must sit on the `GradientLSix` side, and the
three small U7 helpers it also needs (`measurable_torusChart`,
`aestronglyMeasurable_torusLift`, `continuous_gradientTensor`,
`enorm_inner_advection_le`) are repeated in §0 under `…H1`-suffixed names — the
names are distinct from lane 413's, so this module stays importable next to
`CriticalTrilinear` once the duplicate `contDiff_dirDeriv` is removed upstream,
and every declaration remains individually axiom-auditable.  The Hölder engine
itself is *not* copied: §1 is a fresh exponent instance, not a re-proof.

## Forms delivered

The `ℝ≥0∞` form `h1Trilinear_enorm` carries no finiteness hypothesis.  The
`toReal` form `h1Trilinear` is written in the exact spelling the U10b consumer
applies — `laplacianSqT` of `CriticalRegularity.lean:98`, i.e.
`(periodicLpENorm 2 (laplacian v)).toReal ^ 2` — and needs `y ≠ ⊤`, the fourth
conjunct of `MemPeriodicHomogeneous (1/2) v` (supplied verbatim by the
`reductionRegular` field of `CriticalRegularityTAPI`), together with
`‖Δv‖₂ ≠ ⊤`, which is automatic for a smooth field on the probability torus.
§4 records the `periodicPairing` and time-slice spellings.

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

/-! ## §0  Lane 413 helpers, repeated under `…H1` names (see the header) -/

/-- The fundamental-domain chart `T³ → Space` underlying `torusLift` is
measurable.  Copy of `CriticalTrilinear.measurable_torusChart`. -/
theorem measurable_torusChartH1 :
    Measurable (fun z : PeriodicTorus ↦
      toSpace ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).val)) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable.comp
    (measurable_subtype_coe.comp (UnitAddTorus.measurableEquivPiIoc (0 : Coords)).measurable)

/-- For a continuous field with an arbitrary normed target, the canonical torus
lift is a.e.-strongly measurable against Haar measure.  Copy of
`CriticalTrilinear.aestronglyMeasurable_torusLift`. -/
theorem aestronglyMeasurable_torusLiftH1 {E : Type*} [NormedAddCommGroup E]
    {w : Space → E} (hw : Continuous w) :
    AEStronglyMeasurable (torusLift w) periodicTorusMeasure :=
  hw.comp_aestronglyMeasurable measurable_torusChartH1.aestronglyMeasurable

/-- Continuity of the gradient tensor in the registered `gradientTensor`
carrier.  Copy of `CriticalTrilinear.continuous_gradientTensor`. -/
theorem continuous_gradientTensorH1 {v : SpatialField} (hv : ContDiff ℝ ∞ v) :
    Continuous (gradientTensor v) := by
  show Continuous (fun x ↦
    (WithLp.toLp 2 (fun j : Fin 3 ↦ dirDeriv j v x) : WithLp 2 (Fin 3 → Space)))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ Space)).comp
    (continuous_pi fun j ↦ (contDiff_dirDeriv hv j).continuous)

/-- `03-torus.tex:470`, pointwise: Cauchy–Schwarz for the Euclidean inner
product followed by the column Cauchy–Schwarz `‖(v·∇)v‖ ≤ ‖v‖ ‖∇v‖`
(`Section4.C01.advection_norm_le`).  Copy of
`CriticalTrilinear.enorm_inner_advection_le`. -/
theorem enorm_inner_advection_leH1 (v Lv : SpatialField) (x : Space) :
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

/-! ## §1  Three-factor Hölder `(3, 6, 2)` on the probability torus -/

/-- Three-factor Hölder with the U10a exponents `3, 6, 2` (`1/3+1/6+1/2 = 1`)
against normalized Haar measure on `T³`, stated for the `ℝ≥0∞` norms of the
datum layer.  Same scheme as lane 413's `(3,3,3)` U7 lemma
`lintegral_enorm_mul_three_le_torus`; the engine
`ENNReal.lintegral_prod_norm_pow_le` is general in both the measure and the
exponent vector, so only the exponent vector changes. -/
theorem lintegral_enorm_mul_three_le_torus_three_six_two
    {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G]
    {f : PeriodicTorus → E} {g : PeriodicTorus → F} {h : PeriodicTorus → G}
    (hf : AEStronglyMeasurable f periodicTorusMeasure)
    (hg : AEStronglyMeasurable g periodicTorusMeasure)
    (hh : AEStronglyMeasurable h periodicTorusMeasure) :
    ∫⁻ y, ‖f y‖ₑ * ‖g y‖ₑ * ‖h y‖ₑ ∂periodicTorusMeasure ≤
      eLpNorm f 3 periodicTorusMeasure * eLpNorm g 6 periodicTorusMeasure *
        eLpNorm h 2 periodicTorusMeasure := by
  have hpow3 (a : ℝ≥0∞) : (a ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = a := by
    rw [← ENNReal.rpow_mul]
    norm_num
  have hpow6 (a : ℝ≥0∞) : (a ^ (6 : ℝ)) ^ ((1 : ℝ) / 6) = a := by
    rw [← ENNReal.rpow_mul]
    norm_num
  have hpow2 (a : ℝ≥0∞) : (a ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = a := by
    rw [← ENNReal.rpow_mul]
    norm_num
  have he3 (q : PeriodicTorus → ℝ≥0∞) :
      (∫⁻ y, q y ^ (3 : ℝ) ∂periodicTorusMeasure) ^ ((1 : ℝ) / 3) =
        eLpNorm q 3 periodicTorusMeasure := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, enorm_eq_self]
  have he6 (q : PeriodicTorus → ℝ≥0∞) :
      (∫⁻ y, q y ^ (6 : ℝ) ∂periodicTorusMeasure) ^ ((1 : ℝ) / 6) =
        eLpNorm q 6 periodicTorusMeasure := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, enorm_eq_self]
  have he2 (q : PeriodicTorus → ℝ≥0∞) :
      (∫⁻ y, q y ^ (2 : ℝ) ∂periodicTorusMeasure) ^ ((1 : ℝ) / 2) =
        eLpNorm q 2 periodicTorusMeasure := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, enorm_eq_self]
  calc
    ∫⁻ y, ‖f y‖ₑ * ‖g y‖ₑ * ‖h y‖ₑ ∂periodicTorusMeasure
        = ∫⁻ y, ∏ i : Fin 3,
            (![fun y ↦ ‖f y‖ₑ ^ (3 : ℝ),
               fun y ↦ ‖g y‖ₑ ^ (6 : ℝ),
               fun y ↦ ‖h y‖ₑ ^ (2 : ℝ)] i y) ^
              (![(1 : ℝ) / 3, (1 : ℝ) / 6, (1 : ℝ) / 2] i)
              ∂periodicTorusMeasure := by
          refine lintegral_congr fun y ↦ ?_
          rw [Fin.prod_univ_three]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons, hpow3, hpow6, hpow2]
    _ ≤ ∏ i : Fin 3,
          (∫⁻ y, (![fun y ↦ ‖f y‖ₑ ^ (3 : ℝ),
                    fun y ↦ ‖g y‖ₑ ^ (6 : ℝ),
                    fun y ↦ ‖h y‖ₑ ^ (2 : ℝ)] i y) ∂periodicTorusMeasure) ^
            (![(1 : ℝ) / 3, (1 : ℝ) / 6, (1 : ℝ) / 2] i) := by
          refine ENNReal.lintegral_prod_norm_pow_le (Finset.univ) ?_ ?_ ?_
          · intro i _
            fin_cases i
            · exact hf.enorm.pow_const _
            · exact hg.enorm.pow_const _
            · exact hh.enorm.pow_const _
          · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
            norm_num
          · intro i _
            fin_cases i <;> norm_num
    _ = eLpNorm f 3 periodicTorusMeasure * eLpNorm g 6 periodicTorusMeasure *
          eLpNorm h 2 periodicTorusMeasure := by
          rw [Fin.prod_univ_three]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons]
          rw [he3, he6, he2]
          rw [eLpNorm_enorm, eLpNorm_enorm, eLpNorm_enorm]

/-! ## §2  The physical Hölder step `≤ ‖v‖₃ ‖∇v‖₆ ‖Δv‖₂` -/

/-- `03-torus.tex:470-471`, first inequality:
`|⟪(v·∇)v, Δv⟫_{L²(T³)}| ≤ ‖v‖₃ ‖∇v‖₆ ‖Δv‖₂`.
Kept in `ℝ≥0∞`, so no integrability premise is needed. -/
theorem h1AdvectionHolderT (v : SpatialField) (hv : SmoothPeriodicT v) :
    ENNReal.ofReal
        |∫ y : PeriodicTorus,
            torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (laplacian v x) : ℝ)) y
              ∂periodicTorusMeasure| ≤
      periodicLpENorm 3 v * periodicLpENorm 6 (gradientTensor v) *
        periodicLpENorm 2 (laplacian v) := by
  rw [← Real.enorm_eq_ofReal_abs]
  calc ‖∫ y : PeriodicTorus,
          torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (laplacian v x) : ℝ)) y
            ∂periodicTorusMeasure‖ₑ
      ≤ ∫⁻ y, ‖torusLift
            (fun x ↦ (inner ℝ (advection (lift v) 0 x) (laplacian v x) : ℝ)) y‖ₑ
              ∂periodicTorusMeasure := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, ‖torusLift v y‖ₑ * ‖torusLift (gradientTensor v) y‖ₑ *
            ‖torusLift (laplacian v) y‖ₑ ∂periodicTorusMeasure :=
        lintegral_mono fun _ ↦ enorm_inner_advection_leH1 v (laplacian v) _
    _ ≤ _ :=
        lintegral_enorm_mul_three_le_torus_three_six_two
          (aestronglyMeasurable_torusLiftH1 hv.1.continuous)
          (aestronglyMeasurable_torusLiftH1 (continuous_gradientTensorH1 hv.1))
          (aestronglyMeasurable_torusLiftH1 (contDiff_laplacian hv.1).continuous)

/-! ## §3  The explicit constant and the U10a target -/

/-- `03-torus.tex:470-473`: the explicit `C₁` of the `H¹` trilinear estimate,
the product of the T12 order-`1/2` critical constant `CcriticalHalf`
(`‖v‖₃ ≤ CcriticalHalf ‖v‖_{Ḣ^{1/2}}`, T12 U4) with the T12 `L⁶` gradient
constant `Csix` (`‖∇v‖₆ ≤ Csix ‖Δv‖₂`, T12 U5). -/
def h1TrilinearConst : ℝ := CcriticalHalf * Csix

theorem h1TrilinearConst_pos : 0 < h1TrilinearConst :=
  mul_pos CcriticalHalf_pos Csix_pos

/-- **T20 U10a, `03-torus.tex:467-477`, `ℝ≥0∞` form.**
For a smooth periodic mean-zero field `v` on `T³` with finite `Ḣ^{1/2}` norm,
`|⟪(v·∇)v, Δv⟫| ≤ h1TrilinearConst · y · ‖Δv‖₂²`, `y = ‖v‖_{Ḣ^{1/2}}`.
No finiteness hypothesis is needed in this form. -/
theorem h1Trilinear_enorm (v : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v) :
    ENNReal.ofReal
        |∫ y : PeriodicTorus,
            torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (laplacian v x) : ℝ)) y
              ∂periodicTorusMeasure| ≤
      ENNReal.ofReal h1TrilinearConst *
        periodicHomogeneousENorm (1 / 2) v *
          periodicLpENorm 2 (laplacian v) ^ 2 := by
  have hvel : periodicLpENorm 3 v ≤
      ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v :=
    velocityCriticalL3 v hhalf
  have hgrad : periodicLpENorm 6 (gradientTensor v) ≤
      ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian v) :=
    gradientLSix v hv hhalf.2.2.1
  have hconst : ENNReal.ofReal h1TrilinearConst =
      ENNReal.ofReal CcriticalHalf * ENNReal.ofReal Csix := by
    rw [h1TrilinearConst, ENNReal.ofReal_mul CcriticalHalf_pos.le]
  calc ENNReal.ofReal
        |∫ y : PeriodicTorus,
            torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (laplacian v x) : ℝ)) y
              ∂periodicTorusMeasure|
      ≤ periodicLpENorm 3 v * periodicLpENorm 6 (gradientTensor v) *
          periodicLpENorm 2 (laplacian v) := h1AdvectionHolderT v hv
    _ ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v *
          (ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian v)) *
            periodicLpENorm 2 (laplacian v) :=
        mul_le_mul' (mul_le_mul' hvel hgrad) le_rfl
    _ = ENNReal.ofReal h1TrilinearConst * periodicHomogeneousENorm (1 / 2) v *
          periodicLpENorm 2 (laplacian v) ^ 2 := by
        rw [hconst, pow_two]; ring

/-- `‖Δv‖_{L²(T³)} ≠ ⊤` for a smooth field: the torus carries a probability
measure and `Δv` is continuous. -/
theorem periodicLpENorm_two_laplacian_ne_top (v : SpatialField)
    (hv : SmoothPeriodicT v) : periodicLpENorm 2 (laplacian v) ≠ ⊤ :=
  (memLp_torusLift_vector (contDiff_laplacian hv.1).continuous 2).2.ne

/-- **T20 U10a, `03-torus.tex:467-477`, real form with `‖Δv‖₂²` written out.**
`|⟪(v·∇)v, Δv⟫| ≤ h1TrilinearConst · y · ‖Δv‖₂²` with
`y = (periodicHomogeneousENorm (1/2) v).toReal`. -/
theorem h1Trilinear_toReal (v : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v) :
    |∫ y : PeriodicTorus,
        torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (laplacian v x) : ℝ)) y
          ∂periodicTorusMeasure| ≤
      h1TrilinearConst * (periodicHomogeneousENorm (1 / 2) v).toReal *
        (periodicLpENorm 2 (laplacian v)).toReal ^ 2 := by
  have hYtop : periodicHomogeneousENorm (1 / 2) v ≠ ⊤ := hhalf.2.2.2
  have hLtop : periodicLpENorm 2 (laplacian v) ≠ ⊤ :=
    periodicLpENorm_two_laplacian_ne_top v hv
  have hfin : ENNReal.ofReal h1TrilinearConst *
      periodicHomogeneousENorm (1 / 2) v *
        periodicLpENorm 2 (laplacian v) ^ 2 ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYtop) ?_
    exact ENNReal.pow_ne_top hLtop
  have hmono := ENNReal.toReal_mono hfin (h1Trilinear_enorm v hv hhalf)
  rwa [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal h1TrilinearConst_pos.le] at hmono

/-- **T20 U10a in the exact spelling the U10b consumer applies**
(`CriticalRegularity.lean:330-342`, field `hOneEnergy`): the right-hand square is
`laplacianSqT`, i.e. `(periodicLpENorm 2 (laplacian v)).toReal ^ 2`.

`|⟪(v·∇)v, Δv⟫| ≤ C₁ · y · ‖Δv‖₂²`,
`C₁ = h1TrilinearConst = CcriticalHalf · Csix`. -/
theorem h1Trilinear (v : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v) :
    |∫ y : PeriodicTorus,
        torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (laplacian v x) : ℝ)) y
          ∂periodicTorusMeasure| ≤
      h1TrilinearConst * (periodicHomogeneousENorm (1 / 2) v).toReal *
        laplacianSqT v :=
  h1Trilinear_toReal v hv hhalf

/-! ## §4  Spelling bridges for the U10b consumer -/

/-- The canonical T20 pairing `periodicPairing` is the Haar integral of the
lifted pointwise inner product: both sides are the same term. -/
theorem periodicPairing_eq_integral_torusLift_innerH1 (a b : SpatialField) :
    periodicPairing a b =
      ∫ y : PeriodicTorus, torusLift (fun x ↦ (inner ℝ (a x) (b x) : ℝ)) y
        ∂periodicTorusMeasure := rfl

/-- The `periodicPairing` form of U10a, for the `H¹` energy computation. -/
theorem h1Trilinear_pairing (v : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v) :
    |periodicPairing (fun x ↦ advection (lift v) 0 x) (laplacian v)| ≤
      h1TrilinearConst * (periodicHomogeneousENorm (1 / 2) v).toReal *
        laplacianSqT v :=
  h1Trilinear v hv hhalf

/-- The time-slice bridge: the space-time advection of `u` at time `t` is the
spatial advection of the slice.  `meanFreeEquation` (U6) produces the left side,
U10a consumes the right side. -/
theorem advection_eq_sliceH1 (u : SpaceTimeField) (t : ℝ) (x : Space) :
    advection u t x = advection (lift (fun y ↦ u (t, y))) 0 x := rfl

/-- **The U10b slice form.**  At a fixed time the estimate is written against
`criticalY` and `laplacianSqT` of the mean-free velocity slice — exactly the
nonlinear term `hOneEnergy` (`CriticalRegularity.lean:330-342`) must absorb. -/
theorem h1Trilinear_slice (g u : SpaceTimeField) (t : ℝ)
    (hv : SmoothPeriodicT (fun x ↦ meanFreeVelocity g u (t, x)))
    (hhalf : MemPeriodicHomogeneous (1 / 2) (fun x ↦ meanFreeVelocity g u (t, x))) :
    |periodicPairing (fun x ↦ advection (meanFreeVelocity g u) t x)
        (laplacian (fun x ↦ meanFreeVelocity g u (t, x)))| ≤
      h1TrilinearConst * (criticalY (meanFreeVelocity g u) t).toReal *
        laplacianSqT (fun x ↦ meanFreeVelocity g u (t, x)) :=
  h1Trilinear_pairing (fun x ↦ meanFreeVelocity g u (t, x)) hv hhalf

end NSFormalization.Section3.T20
