import NSFormalization.Section4.R43.CriticalPairing
import NSFormalization.Section4.A05.CriticalL3
import NSFormalization.Section4.C01.Trilinear
import NSFormalization.Section4.C01.VelocityJets

/-!
# R43 row S1b: the critical trilinear estimate

This module proves the three-`L³` Hölder step and packages the critical
embedding at shifted homogeneous data.  `CriticalDatumPath` does not yet carry
physical realizations of `Λu` or the three half-order derivative data, nor the
Parseval identity identifying its datum pairing with the physical integral.
Those carrier facts are isolated, without an estimate, in
`CriticalAdvectionLpBridge`.

The resulting constant is completely explicit in terms of lane A05's
three-component Riesz-potential constant.
-/

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open scoped ENNReal RealInnerProductSpace

namespace NSFormalization.Section4.R43

open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField ClassicalSolutionR MemForceR MemHInfty)
open NSFormalization.Section4.D01.Homogeneous
  (IsHomogeneousSliceDatum)

/-! ## 1. The shifted critical embedding -/

/-- The constant for the simultaneous `L³` estimates of `∇v` and `Λv`.
The factor four is three derivative columns plus the Riesz-power field. -/
def derivativeCriticalConst : ℝ :=
  4 * NSFormalization.Section4.A05.criticalL3Const

/-- The shifted embedding constant is positive. -/
theorem derivativeCriticalConst_pos : 0 < derivativeCriticalConst := by
  exact mul_pos (by norm_num) NSFormalization.Section4.A05.criticalL3Const_pos

/-- The bounded angular Riesz symbol which turns the order-`3/2` datum of
`v` into the order-`1/2` datum of `∂ⱼv`. -/
def rieszCoordinateSymbol (j : Fin 3) (ξ : Space) : ℂ :=
  if ξ = 0 then 0 else Complex.I * ((ξ j / ‖ξ‖ : ℝ) : ℂ)

/-- Each coordinate Riesz symbol has modulus at most one. -/
theorem rieszCoordinateSymbol_norm_le (j : Fin 3) (ξ : Space) :
    ‖rieszCoordinateSymbol j ξ‖ ≤ 1 := by
  by_cases hξ : ξ = 0
  · simp [rieszCoordinateSymbol, hξ]
  · have hnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hcoord : |ξ j| ≤ ‖ξ‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ j
    simpa [rieszCoordinateSymbol, hξ, abs_of_pos hnorm] using
      (div_le_one hnorm).mpr hcoord

/-- Datum-level content of the order shift used by the derived critical
embedding.  `lambda` is the physical `Λv` realization whose half-order datum is
the supplied order-`3/2` datum `Z`; `derivativeHalf j` is the half-order datum
of `∂ⱼv`.  The last field is the exact coordinate Riesz-multiplier symbol for
the three derivative columns; its norm bound is proved below.

No `L³` estimate or trilinear inequality is a field of this structure. -/
structure ShiftedCriticalData (v : SpatialField)
    (Z : RealVectorSobolev (3 / 2)) where
  lambda : SpatialField
  lambda_memHInfty : MemHInfty lambda
  lambdaHalf_isDatum :
    IsHomogeneousSliceDatum (1 / 2) lambda Z
  derivativeHalf : Fin 3 → RealVectorSobolev (1 / 2)
  derivativeHalf_isDatum : ∀ j : Fin 3,
    IsHomogeneousSliceDatum (1 / 2)
      (NSFormalization.Section4.A05.dirDeriv j v) (derivativeHalf j)
  derivativeHalf_symbol : ∀ j i : Fin 3,
    ((((derivativeHalf j) i : RealSobolevHilbert (1 / 2)) : FourierData) :
        Space → ℂ) =ᵐ[volume]
      fun ξ => rieszCoordinateSymbol j ξ * (Z i : FourierData) ξ

/-- Differentiating a datum-form `H^∞` field preserves the same class. -/
theorem memHInfty_dirDeriv {v : SpatialField} (hv : MemHInfty v) (j : Fin 3) :
    MemHInfty (NSFormalization.Section4.A05.dirDeriv j v) := by
  have hv' : NSFormalization.Section4.A05.SmoothL2 v :=
    NSFormalization.Section4.D01.memHInfty_iff_smoothSquareIntegrableJets.mp hv
  exact NSFormalization.Section4.D01.memHInfty_iff_smoothSquareIntegrableJets.mpr
    (hv'.dir j)

/-- **Shifted critical `L³` embedding.**  Given the actual half-order data of
the three derivative columns and of `Λv`,

`‖∇v‖₃ + ‖Λv‖₃ ≤ (4 C_{1/2}) ‖Z‖₂`.

The proof applies A05's scalar/vector Riesz realization to each shifted datum;
the only loss is the finite-dimensional `l² ≤ l¹` packaging already used by
A05. -/
theorem derivativeCriticalL3 {v : SpatialField}
    (hv : MemHInfty v) {Z : RealVectorSobolev (3 / 2)}
    (hshift : ShiftedCriticalData v Z) :
    eLpNorm (NSFormalization.Section4.A05.gradTensor v) 3 volume +
        eLpNorm hshift.lambda 3 volume ≤
      ENNReal.ofReal derivativeCriticalConst * ‖Z‖ₑ := by
  let C : ℝ≥0∞ :=
    ENNReal.ofReal NSFormalization.Section4.A05.criticalL3Const
  have hv' : NSFormalization.Section4.A05.SmoothL2 v :=
    NSFormalization.Section4.D01.memHInfty_iff_smoothSquareIntegrableJets.mp hv
  have hgrad :
      eLpNorm (NSFormalization.Section4.A05.gradTensor v) 3 volume ≤
        ∑ j : Fin 3,
          eLpNorm (NSFormalization.Section4.A05.dirDeriv j v) 3 volume :=
    NSFormalization.Section4.A05.eLpNorm_le_sum_of_norm_le (by norm_num)
      (fun j => (hv'.dir j).contDiff.continuous.aestronglyMeasurable)
      (fun x => NSFormalization.Section4.A05.norm_toLp_le_sum
        (fun j => NSFormalization.Section4.A05.dirDeriv j v x))
  have hcolumns : ∀ j : Fin 3,
      eLpNorm (NSFormalization.Section4.A05.dirDeriv j v) 3 volume ≤
        C * ‖hshift.derivativeHalf j‖ₑ := by
    intro j
    exact NSFormalization.Section4.A05.u7_vector_eLpNorm_le_of_datum
      (memHInfty_dirDeriv hv j) (hshift.derivativeHalf_isDatum j)
  have hdatumNorm : ∀ j : Fin 3, ‖hshift.derivativeHalf j‖ₑ ≤ ‖Z‖ₑ := by
    intro j
    have hreal : ‖hshift.derivativeHalf j‖ ≤ ‖Z‖ := by
      rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _)
          (show ‖(hshift.derivativeHalf j) i‖ ≤ ‖Z i‖ by
            change ‖((hshift.derivativeHalf j) i : FourierData)‖ ≤
              ‖(Z i : FourierData)‖
            apply Lp.norm_le_norm_of_ae_le
            filter_upwards [hshift.derivativeHalf_symbol j i] with ξ hξ
            rw [hξ, norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _)
              (rieszCoordinateSymbol_norm_le j ξ)) 2
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hreal
  have hdatumSum :
      ∑ j : Fin 3, ‖hshift.derivativeHalf j‖ₑ ≤ 3 * ‖Z‖ₑ := by
    calc
      ∑ j : Fin 3, ‖hshift.derivativeHalf j‖ₑ
          ≤ ∑ _j : Fin 3, ‖Z‖ₑ := Finset.sum_le_sum fun j _ => hdatumNorm j
      _ = 3 * ‖Z‖ₑ := by simp [Finset.sum_const]
  have hgrad' :
      eLpNorm (NSFormalization.Section4.A05.gradTensor v) 3 volume ≤
        C * (3 * ‖Z‖ₑ) := by
    refine hgrad.trans ?_
    calc
      ∑ j : Fin 3, eLpNorm (NSFormalization.Section4.A05.dirDeriv j v) 3 volume
          ≤ ∑ j : Fin 3, C * ‖hshift.derivativeHalf j‖ₑ :=
        Finset.sum_le_sum fun j _ => hcolumns j
      _ = C * ∑ j : Fin 3, ‖hshift.derivativeHalf j‖ₑ := by
        rw [Finset.mul_sum]
      _ ≤ C * (3 * ‖Z‖ₑ) :=
        mul_le_mul' le_rfl hdatumSum
  have hlambda : eLpNorm hshift.lambda 3 volume ≤ C * ‖Z‖ₑ :=
    NSFormalization.Section4.A05.u7_vector_eLpNorm_le_of_datum
      hshift.lambda_memHInfty hshift.lambdaHalf_isDatum
  calc
    eLpNorm (NSFormalization.Section4.A05.gradTensor v) 3 volume +
          eLpNorm hshift.lambda 3 volume
        ≤ C * (3 * ‖Z‖ₑ) + C * ‖Z‖ₑ := add_le_add hgrad' hlambda
    _ = ENNReal.ofReal derivativeCriticalConst * ‖Z‖ₑ := by
      rw [derivativeCriticalConst,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      simp only [ENNReal.ofReal_ofNat]
      change C * (3 * ‖Z‖ₑ) + C * ‖Z‖ₑ = 4 * C * ‖Z‖ₑ
      ring

/-! ## 2. Three-factor Hölder at the `eLpNorm` level -/

/-- Three-factor Hölder with exponents `3,3,3`, stated directly for the
`ℝ≥0∞` norms used in the datum layer. -/
theorem lintegral_enorm_mul_three_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G]
    {f : Space → E} {g : Space → F} {h : Space → G}
    (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume)
    (hh : AEStronglyMeasurable h volume) :
    ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ * ‖h x‖ₑ ∂volume ≤
      eLpNorm f 3 volume * eLpNorm g 3 volume * eLpNorm h 3 volume := by
  have hpow (a : ℝ≥0∞) : (a ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = a := by
    rw [← ENNReal.rpow_mul]
    norm_num
  have he (q : Space → ℝ≥0∞) :
      (∫⁻ x, q x ^ (3 : ℝ) ∂volume) ^ ((1 : ℝ) / 3) =
        eLpNorm q 3 volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, enorm_eq_self]
  calc
    ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ * ‖h x‖ₑ ∂volume
        = ∫⁻ x, ∏ i : Fin 3,
            (![fun x => ‖f x‖ₑ ^ (3 : ℝ),
               fun x => ‖g x‖ₑ ^ (3 : ℝ),
               fun x => ‖h x‖ₑ ^ (3 : ℝ)] i x) ^ ((1 : ℝ) / 3) ∂volume := by
          refine lintegral_congr fun x => ?_
          rw [Fin.prod_univ_three]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons, hpow]
    _ ≤ ∏ i : Fin 3,
          (∫⁻ x, (![fun x => ‖f x‖ₑ ^ (3 : ℝ),
                    fun x => ‖g x‖ₑ ^ (3 : ℝ),
                    fun x => ‖h x‖ₑ ^ (3 : ℝ)] i x) ∂volume) ^ ((1 : ℝ) / 3) := by
          refine ENNReal.lintegral_prod_norm_pow_le (Finset.univ) ?_ ?_ ?_
          · intro i _
            fin_cases i
            · exact hf.enorm.pow_const _
            · exact hg.enorm.pow_const _
            · exact hh.enorm.pow_const _
          · norm_num [Fin.sum_univ_three]
          · intro i _
            norm_num
    _ = eLpNorm f 3 volume * eLpNorm g 3 volume * eLpNorm h 3 volume := by
          rw [Fin.prod_univ_three]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons]
          rw [he, he, he]
          rw [eLpNorm_enorm, eLpNorm_enorm, eLpNorm_enorm]

/-- The physical Hölder step for the nonlinear critical pairing:

`|∫ (v·∇)v · λ| ≤ ‖v‖₃ ‖∇v‖₃ ‖λ‖₃`.

It is kept in `ℝ≥0∞`, so no separate integrability premise is needed. -/
theorem criticalAdvectionHolder (v lambda : SpatialField)
    (hv : NSFormalization.Section4.A05.SmoothL2 v)
    (hlambda : MemHInfty lambda) :
    ENNReal.ofReal
        |∫ x : Space, (inner ℝ
          (advection (NSFormalization.Section4.C01.lift v) 0 x) (lambda x) : ℝ)| ≤
      eLpNorm v 3 volume *
        eLpNorm (NSFormalization.Section4.A05.gradTensor v) 3 volume *
          eLpNorm lambda 3 volume := by
  have hcg : Continuous (NSFormalization.Section4.A05.gradTensor v) := by
    show Continuous (fun x =>
      (WithLp.toLp 2
        (fun j : Fin 3 => NSFormalization.Section4.A05.dirDeriv j v x) :
          WithLp 2 (Fin 3 → Space)))
    exact Continuous.comp (PiLp.continuous_toLp 2 (fun _ : Fin 3 => Space))
      (continuous_pi fun j => (hv.dir j).contDiff.continuous)
  have hpoint : ∀ x : Space,
      ‖(inner ℝ (advection (NSFormalization.Section4.C01.lift v) 0 x)
          (lambda x) : ℝ)‖ₑ ≤
        ‖v x‖ₑ *
          ‖NSFormalization.Section4.A05.gradTensor v x‖ₑ * ‖lambda x‖ₑ := by
    intro x
    have hinner :
        |(inner ℝ (advection (NSFormalization.Section4.C01.lift v) 0 x)
            (lambda x) : ℝ)| ≤
          ‖advection (NSFormalization.Section4.C01.lift v) 0 x‖ * ‖lambda x‖ :=
      abs_real_inner_le_norm _ _
    have hreal :
        |(inner ℝ (advection (NSFormalization.Section4.C01.lift v) 0 x)
            (lambda x) : ℝ)| ≤
          ‖v x‖ * ‖NSFormalization.Section4.A05.gradTensor v x‖ * ‖lambda x‖ :=
      hinner.trans (mul_le_mul_of_nonneg_right
        (NSFormalization.Section4.C01.advection_norm_le v x) (norm_nonneg _))
    calc
      ‖(inner ℝ (advection (NSFormalization.Section4.C01.lift v) 0 x)
          (lambda x) : ℝ)‖ₑ
          = ENNReal.ofReal |(inner ℝ
              (advection (NSFormalization.Section4.C01.lift v) 0 x)
              (lambda x) : ℝ)| := Real.enorm_eq_ofReal_abs _
      _ ≤ ENNReal.ofReal
          (‖v x‖ * ‖NSFormalization.Section4.A05.gradTensor v x‖ * ‖lambda x‖) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ‖v x‖ₑ * ‖NSFormalization.Section4.A05.gradTensor v x‖ₑ *
          ‖lambda x‖ₑ := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm, ofReal_norm]
  rw [← Real.enorm_eq_ofReal_abs]
  calc
    ‖∫ x : Space, (inner ℝ
        (advection (NSFormalization.Section4.C01.lift v) 0 x) (lambda x) : ℝ)‖ₑ
        ≤ ∫⁻ x, ‖(inner ℝ
          (advection (NSFormalization.Section4.C01.lift v) 0 x)
          (lambda x) : ℝ)‖ₑ ∂volume := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, ‖v x‖ₑ *
          ‖NSFormalization.Section4.A05.gradTensor v x‖ₑ * ‖lambda x‖ₑ ∂volume :=
      lintegral_mono hpoint
    _ ≤ _ := lintegral_enorm_mul_three_le
      hv.contDiff.continuous.aestronglyMeasurable hcg.aestronglyMeasurable
      hlambda.1.continuous.aestronglyMeasurable

/-! ## 3. The exact carrier boundary and assembly -/

/-- The sole remaining S1b carrier hypothesis.

For each interior time it supplies the shifted data used by
`derivativeCriticalL3` and the exact Parseval identity

`⟪Λ^{1/2}((u·∇)u), Λ^{1/2}u⟫ = ∫ (u·∇)u · Λu`.

It contains no inequality.  Constructing `shifted` requires the unexported A05 U4/U8 carriers (plus `MemHInfty` closure for `Λu`), while `pairing_identity` is a separate fractional Parseval/duality obligation. -/
structure CriticalAdvectionLpBridge
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) where
  shifted : ∀ t ∈ Ioo (0 : ℝ) T,
    ShiftedCriticalData (fun x => w.velocity (t, x))
      (hcrit.velocityThreeHalf t)
  pairing_identity : ∀ t (ht : t ∈ Ioo (0 : ℝ) T),
    ⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫ =
      ∫ x : Space, (inner ℝ
        (advection (NSFormalization.Section4.C01.lift
          (fun y => w.velocity (t, y))) 0 x)
        ((shifted t ht).lambda x) : ℝ)

/-- The explicit constant in
`|⟨(u·∇)u,Λu⟩| ≤ C₀ ‖u‖_{Ḣ^{1/2}} ‖u‖²_{Ḣ^{3/2}}`. -/
def trilinearConst : ℝ :=
  NSFormalization.Section4.A05.criticalL3Const *
    derivativeCriticalConst * derivativeCriticalConst

/-- Expanded form of the explicit constant. -/
theorem trilinearConst_eq :
    trilinearConst =
      16 * NSFormalization.Section4.A05.criticalL3Const ^ 3 := by
  simp only [trilinearConst, derivativeCriticalConst]
  ring

/-- The explicit trilinear constant is positive. -/
theorem trilinearConst_pos : 0 < trilinearConst := by
  exact mul_pos
    (mul_pos NSFormalization.Section4.A05.criticalL3Const_pos
      derivativeCriticalConst_pos)
    derivativeCriticalConst_pos

/-- S1b assembled from the datum path and the exact carrier/Parseval bridge.
All inequalities—including three-factor Hölder and both critical embeddings—
are proved in this module. -/
theorem criticalTrilinearEstimate_of_hcrit
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf)
    (hbridge : CriticalAdvectionLpBridge hcrit) :
    CriticalTrilinearEstimate (C₀ := trilinearConst) hcrit := by
  intro t ht
  let v : SpatialField := fun x => w.velocity (t, x)
  let hs := hbridge.shifted t ht
  have hv := NSFormalization.Section4.C01.velocity_slice_memHInfty_and_smoothL2 w
    (Ioo_subset_Ico_self ht)
  have hvelocity : eLpNorm v 3 volume ≤
      ENNReal.ofReal NSFormalization.Section4.A05.criticalL3Const *
        ‖hcrit.velocityHalf t‖ₑ :=
    NSFormalization.Section4.A05.u7_vector_eLpNorm_le_of_datum hv.1
      (hcrit.velocityHalf_isDatum t (Ioo_subset_Ico_self ht))
  have hderivative :
      eLpNorm (NSFormalization.Section4.A05.gradTensor v) 3 volume +
          eLpNorm hs.lambda 3 volume ≤
        ENNReal.ofReal derivativeCriticalConst *
          ‖hcrit.velocityThreeHalf t‖ₑ :=
    derivativeCriticalL3 hv.1 hs
  have hgrad : eLpNorm (NSFormalization.Section4.A05.gradTensor v) 3 volume ≤
      ENNReal.ofReal derivativeCriticalConst * ‖hcrit.velocityThreeHalf t‖ₑ :=
    (le_add_right le_rfl).trans hderivative
  have hlambda : eLpNorm hs.lambda 3 volume ≤
      ENNReal.ofReal derivativeCriticalConst * ‖hcrit.velocityThreeHalf t‖ₑ :=
    (le_add_left le_rfl).trans hderivative
  have hholder := criticalAdvectionHolder v hs.lambda hv.2 hs.lambda_memHInfty
  have hENN : ENNReal.ofReal
      |⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫| ≤
      ENNReal.ofReal trilinearConst * ‖hcrit.velocityHalf t‖ₑ *
        ‖hcrit.velocityThreeHalf t‖ₑ ^ (2 : ℕ) := by
    rw [hbridge.pairing_identity t ht]
    change ENNReal.ofReal
        |∫ x : Space, (inner ℝ
          (advection (NSFormalization.Section4.C01.lift v) 0 x)
          (hs.lambda x) : ℝ)| ≤ _
    refine hholder.trans ?_
    calc
      eLpNorm v 3 volume *
            eLpNorm (NSFormalization.Section4.A05.gradTensor v) 3 volume *
              eLpNorm hs.lambda 3 volume
          ≤ (ENNReal.ofReal NSFormalization.Section4.A05.criticalL3Const *
                ‖hcrit.velocityHalf t‖ₑ) *
              (ENNReal.ofReal derivativeCriticalConst *
                ‖hcrit.velocityThreeHalf t‖ₑ) *
              (ENNReal.ofReal derivativeCriticalConst *
                ‖hcrit.velocityThreeHalf t‖ₑ) := by gcongr
      _ = ENNReal.ofReal trilinearConst * ‖hcrit.velocityHalf t‖ₑ *
            ‖hcrit.velocityThreeHalf t‖ₑ ^ (2 : ℕ) := by
        rw [trilinearConst,
          ENNReal.ofReal_mul
            (mul_pos NSFormalization.Section4.A05.criticalL3Const_pos
              derivativeCriticalConst_pos).le,
          ENNReal.ofReal_mul
            NSFormalization.Section4.A05.criticalL3Const_pos.le]
        ring
  have htop :
      ENNReal.ofReal trilinearConst * ‖hcrit.velocityHalf t‖ₑ *
          ‖hcrit.velocityThreeHalf t‖ₑ ^ (2 : ℕ) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp))
      (ENNReal.pow_ne_top (by simp))
  have hreal := ENNReal.toReal_mono htop hENN
  simpa [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_pow, toReal_enorm, trilinearConst_pos.le] using hreal

/-- eq:Rcritical1, with S1b discharged once the exact carrier bridge is
available. -/
theorem rcritical1_of_hcrit
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} (hf : MemForceR f)
    (hcrit : CriticalDatumPath w hf)
    (hbridge : CriticalAdvectionLpBridge hcrit) :
    (∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun r => criticalNormAt w.velocity r ^ 2)
        (criticalEnergyDerivative hcrit t) t) ∧
      ∀ t ∈ Ioo (0 : ℝ) T,
        criticalEnergyDerivative hcrit t / 2 +
            (ν - trilinearConst * criticalNormAt w.velocity t) *
              criticalDissipationAt w.velocity t ^ 2
          ≤ criticalForceAt f t * criticalNormAt w.velocity t :=
  rcritical1_of_trilinear hf hcrit
    (criticalTrilinearEstimate_of_hcrit hcrit hbridge)

end NSFormalization.Section4.R43
