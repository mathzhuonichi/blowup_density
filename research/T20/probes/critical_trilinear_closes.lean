import NSFormalization.Section3.T20.CriticalTrilinear

/-!
# U7 closure probe (lane 413)

The mean-zero critical trilinear estimate (`03-torus.tex:425-431`,
`|⟪(v·∇)v,Λv⟫| ≤ C₀ y z²`) is proved in
`formalization/NSFormalization/Section3/T20/CriticalTrilinear.lean`.  This probe:

* **§1** records the explicit constant
  `criticalTrilinearConst = CcriticalHalf * CcriticalThreeHalves ^ 2
   = 16 * CcriticalHalf ^ 3` and its positivity, and the three inputs the
  estimate is assembled from (pointwise Cauchy–Schwarz, three-factor Hölder on
  `T³`, and the physical Hölder step `≤ ‖v‖₃‖∇v‖₃‖Λv‖₃`);
* **§2** reproduces lane 377/396/405's genuine nonzero smooth mean-zero periodic
  witness `probeMZ = meanZeroPartT (x ↦ cos(2π x₀)·e₀)` (research probes cannot
  import one another) and instantiates the estimate there, with `Lv` supplied by
  `T12.lambda_exists` — so neither the hypotheses nor the conclusion is vacuous;
* **§3** is the shape check for the U8 consumer: the estimate written out at a
  spatial slice of `meanFreeVelocity g w.velocity`, with the left side in the
  `advection u t x` spelling that `meanFreeEquation` produces and the right side
  in the `criticalY` / `criticalZ` spelling of
  `Section3/T20/CriticalRegularity.lean:70-90` — exactly the term U8's
  `criticalEnergy` field must absorb.
-/

noncomputable section

namespace NSFormalization.Section3.T20

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T12
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open scoped ContDiff ENNReal BigOperators Real

/-! ## 1. The U7 target and its explicit constant -/

example : criticalTrilinearConst = CcriticalHalf * CcriticalThreeHalves ^ 2 := rfl

example : criticalTrilinearConst = 16 * CcriticalHalf ^ 3 := criticalTrilinearConst_eq

example : 0 < criticalTrilinearConst := criticalTrilinearConst_pos

/-- The `ℝ≥0∞` form: no finiteness hypothesis. -/
example (v Lv : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v)
    (hthree : MemPeriodicHomogeneous (3 / 2) v) (hL : IsPeriodicLambda v Lv) :
    ENNReal.ofReal
        |∫ y : PeriodicTorus,
            torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)) y
              ∂periodicTorusMeasure| ≤
      ENNReal.ofReal criticalTrilinearConst *
        periodicHomogeneousENorm (1 / 2) v *
          periodicHomogeneousENorm (3 / 2) v ^ 2 :=
  criticalTrilinear_enorm v Lv hv hhalf hthree hL

/-- The real form, with `.toReal` on both norms. -/
example (v Lv : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v)
    (hthree : MemPeriodicHomogeneous (3 / 2) v) (hL : IsPeriodicLambda v Lv) :
    |∫ y : PeriodicTorus,
        torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)) y
          ∂periodicTorusMeasure| ≤
      criticalTrilinearConst * (periodicHomogeneousENorm (1 / 2) v).toReal *
        (periodicHomogeneousENorm (3 / 2) v).toReal ^ 2 :=
  criticalTrilinear v Lv hv hhalf hthree hL

/-- The `periodicPairing` form (the canonical T20 `L²(T³)` pairing). -/
example (v Lv : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v)
    (hthree : MemPeriodicHomogeneous (3 / 2) v) (hL : IsPeriodicLambda v Lv) :
    |periodicPairing (fun x ↦ advection (lift v) 0 x) Lv| ≤
      criticalTrilinearConst * (periodicHomogeneousENorm (1 / 2) v).toReal *
        (periodicHomogeneousENorm (3 / 2) v).toReal ^ 2 :=
  criticalTrilinear_pairing v Lv hv hhalf hthree hL

/-- The intermediate Hölder line `|⟪(v·∇)v,Λv⟫| ≤ ‖v‖₃‖∇v‖₃‖Λv‖₃`
(`03-torus.tex:427`, first inequality). -/
example (v Lv : SpatialField) (hv : SmoothPeriodicT v) (hLv : Continuous Lv) :
    ENNReal.ofReal
        |∫ y : PeriodicTorus,
            torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)) y
              ∂periodicTorusMeasure| ≤
      periodicLpENorm 3 v * periodicLpENorm 3 (gradientTensor v) *
        periodicLpENorm 3 Lv :=
  criticalAdvectionHolderT v Lv hv hLv

/-- The pointwise input. -/
example (v Lv : SpatialField) (x : Space) :
    ‖(inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)‖ₑ ≤
      ‖v x‖ₑ * ‖gradientTensor v x‖ₑ * ‖Lv x‖ₑ :=
  enorm_inner_advection_le v Lv x

/-- Three-factor Hölder `3,3,3` on the probability torus. -/
example {f g h : PeriodicTorus → ℝ}
    (hf : AEStronglyMeasurable f periodicTorusMeasure)
    (hg : AEStronglyMeasurable g periodicTorusMeasure)
    (hh : AEStronglyMeasurable h periodicTorusMeasure) :
    ∫⁻ y, ‖f y‖ₑ * ‖g y‖ₑ * ‖h y‖ₑ ∂periodicTorusMeasure ≤
      eLpNorm f 3 periodicTorusMeasure * eLpNorm g 3 periodicTorusMeasure *
        eLpNorm h 3 periodicTorusMeasure :=
  lintegral_enorm_mul_three_le_torus hf hg hh

/-! ## 2. A genuine nonzero smooth mean-zero periodic witness -/

/-- A single-mode cosine vector field, `x ↦ cos(2π x₀)·e₀` (lane 377's `probeZ`). -/
def probeZ : SpatialField := fun x ↦ Real.cos (2 * Real.pi * x 0) • coordinateVector 0

theorem probeZ_contDiff : ContDiff ℝ ∞ probeZ := by
  unfold probeZ
  have hproj : ContDiff ℝ ∞ (fun x : Space ↦ x 0) := contDiff_piLp_apply 2
  exact (Real.contDiff_cos.comp (contDiff_const.mul hproj)).smul contDiff_const

theorem coordinateVector_apply (i j : Fin 3) :
    (coordinateVector i) j = (if j = i then (1 : ℝ) else 0) := by
  simp [coordinateVector, PiLp.single_apply]

theorem probeZ_periodic : IsPeriodicSpatial probeZ := by
  intro x i
  show Real.cos (2 * Real.pi * (x + coordinateVector i) 0) • coordinateVector 0
      = Real.cos (2 * Real.pi * x 0) • coordinateVector 0
  have hadd : (x + coordinateVector i) 0 = x 0 + (if (0 : Fin 3) = i then 1 else 0) := by
    show x 0 + (coordinateVector i) 0 = _
    rw [coordinateVector_apply]
  rcases eq_or_ne (0 : Fin 3) i with hi | hi
  · subst hi
    have hx : (x + coordinateVector (0 : Fin 3)) 0 = x 0 + 1 := by rw [hadd]; norm_num
    have heq : 2 * Real.pi * (x 0 + 1) = 2 * Real.pi * x 0 + 2 * Real.pi := by ring
    rw [hx, heq, Real.cos_add_two_pi]
  · have hx : (x + coordinateVector i) 0 = x 0 := by rw [hadd]; simp [hi]
    rw [hx]

theorem probeZ_integrable : Integrable (torusLift probeZ) periodicTorusMeasure :=
  integrable_torusLift_space probeZ_contDiff.continuous

/-- The non-vacuity witness: a nonzero smooth mean-zero periodic field. -/
def probeMZ : SpatialField := meanZeroPartT probeZ

theorem probeMZ_smoothPeriodic : SmoothPeriodicT probeMZ := by
  refine ⟨probeZ_contDiff.sub contDiff_const, ?_⟩
  intro x i
  show probeZ (x + coordinateVector i) - meanT probeZ = probeZ x - meanT probeZ
  rw [probeZ_periodic x i]

theorem probeMZ_meanZero : IsMeanZeroT probeMZ :=
  (mean_decomposition probeZ probeZ_periodic probeZ_integrable).2

theorem probeMZ_ne_zero : probeMZ ≠ (0 : SpatialField) := by
  intro h
  set p1 : Space := (2⁻¹ : ℝ) • coordinateVector (0 : Fin 3) with hp1
  have hp1coord : p1 0 = (2⁻¹ : ℝ) := by
    show (2⁻¹ : ℝ) • (coordinateVector (0 : Fin 3)) 0 = (2⁻¹ : ℝ)
    rw [coordinateVector_apply]; simp
  have hp0coord : (0 : Space) 0 = (0 : ℝ) := by simp
  have hzero : probeZ (0 : Space) - probeZ p1 = 0 := by
    have e0 : probeMZ (0 : Space) = 0 := by rw [h]; rfl
    have e1 : probeMZ p1 = 0 := by rw [h]; rfl
    have hd : probeMZ (0 : Space) - probeMZ p1 = probeZ (0 : Space) - probeZ p1 := by
      simp only [probeMZ, meanZeroPartT]; abel
    rw [e0, e1, sub_zero] at hd
    exact hd.symm
  have hz0 : probeZ (0 : Space) = coordinateVector 0 := by
    show Real.cos (2 * Real.pi * (0 : Space) 0) • coordinateVector 0 = coordinateVector 0
    rw [hp0coord]; simp
  have hz1 : probeZ p1 = (-1 : ℝ) • coordinateVector 0 := by
    show Real.cos (2 * Real.pi * p1 0) • coordinateVector 0 = (-1 : ℝ) • coordinateVector 0
    rw [hp1coord]
    have hpi : 2 * Real.pi * (2⁻¹ : ℝ) = Real.pi := by ring
    rw [hpi, Real.cos_pi]
  rw [hz0, hz1, neg_one_smul, sub_neg_eq_add] at hzero
  have hcv : coordinateVector (0 : Fin 3) ≠ 0 := by
    intro hc
    have hca := coordinateVector_apply 0 0
    rw [hc] at hca
    simp at hca
  have hs : (2 : ℝ) • coordinateVector (0 : Fin 3) = 0 := by rw [two_smul]; exact hzero
  exact hcv ((smul_eq_zero.mp hs).resolve_left (by norm_num))

theorem probeMZ_memHalf : MemPeriodicHomogeneous (1 / 2) probeMZ :=
  ⟨probeMZ_smoothPeriodic.2,
    memLp_torusLift_vector probeMZ_smoothPeriodic.1.continuous 2,
    probeMZ_meanZero,
    ne_of_lt (periodicHomogeneousENorm_lt_top (by norm_num) probeZ_periodic probeZ_contDiff)⟩

theorem probeMZ_memThreeHalves : MemPeriodicHomogeneous (3 / 2) probeMZ :=
  ⟨probeMZ_smoothPeriodic.2,
    memLp_torusLift_vector probeMZ_smoothPeriodic.1.continuous 2,
    probeMZ_meanZero,
    ne_of_lt (periodicHomogeneousENorm_lt_top (by norm_num) probeZ_periodic probeZ_contDiff)⟩

/-- The U7 estimate at the nonzero witness: the hypotheses are all satisfiable
and the conclusion is not vacuous. -/
example : probeMZ ≠ (0 : SpatialField) ∧
    ∃ Lv : SpatialField, IsPeriodicLambda probeMZ Lv ∧
      |periodicPairing (fun x ↦ advection (lift probeMZ) 0 x) Lv| ≤
        criticalTrilinearConst *
          (periodicHomogeneousENorm (1 / 2) probeMZ).toReal *
            (periodicHomogeneousENorm (3 / 2) probeMZ).toReal ^ 2 := by
  obtain ⟨Lv, hLv⟩ := lambda_exists probeMZ probeMZ_smoothPeriodic
  exact ⟨probeMZ_ne_zero, Lv, hLv,
    criticalTrilinear_pairing probeMZ Lv probeMZ_smoothPeriodic probeMZ_memHalf
      probeMZ_memThreeHalves hLv⟩

/-! ## 3. Shape check: exactly what U8 (`criticalEnergy`) consumes -/

/-- The time-slice bridge, `rfl`: `meanFreeEquation`'s `advection u t x` is the
spatial advection of the slice that U7 estimates. -/
example (u : SpaceTimeField) (t : ℝ) (x : Space) :
    advection u t x = advection (lift (fun y ↦ u (t, y))) 0 x :=
  advection_eq_slice u t x

/-- **The U8 slice spelling.**  For the mean-free velocity of a classical
solution at an interior time `t`, with the regularity `reductionRegular`
supplies and `Lv` the `Λ`-representative of the slice, the nonlinear term of
`eq:criticalenergy` obeys
`|⟪(v·∇)v, Λv⟫| ≤ C₀ · y(t) · z(t)²`
with `y = criticalY …`, `z = criticalZ …` and `C₀ = criticalTrilinearConst`. -/
example (g : SpaceTimeField) (u : SpaceTimeField) (t : ℝ) (Lv : SpatialField)
    (hv : SmoothPeriodicT (fun x ↦ meanFreeVelocity g u (t, x)))
    (hhalf : MemPeriodicHomogeneous (1 / 2) (fun x ↦ meanFreeVelocity g u (t, x)))
    (hthree : MemPeriodicHomogeneous (3 / 2) (fun x ↦ meanFreeVelocity g u (t, x)))
    (hL : IsPeriodicLambda (fun x ↦ meanFreeVelocity g u (t, x)) Lv) :
    |periodicPairing (fun x ↦ advection (meanFreeVelocity g u) t x) Lv| ≤
      criticalTrilinearConst * (criticalY (meanFreeVelocity g u) t).toReal *
        (criticalZ (meanFreeVelocity g u) t).toReal ^ 2 :=
  criticalTrilinear_pairing (fun x ↦ meanFreeVelocity g u (t, x)) Lv hv hhalf hthree hL

end NSFormalization.Section3.T20
