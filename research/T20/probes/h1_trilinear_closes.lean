import NSFormalization.Section3.T20.H1Trilinear

/-!
# U10a closure probe (lane 429)

The mean-zero `H¹` trilinear estimate (`03-torus.tex:467-477`,
`|⟪(v·∇)v,Δv⟫| ≤ C₁ y ‖Δv‖₂²`) is proved in
`formalization/NSFormalization/Section3/T20/H1Trilinear.lean`.  This probe:

* **§1** records the explicit constant `h1TrilinearConst = CcriticalHalf * Csix`
  and its positivity, and the three inputs the estimate is assembled from
  (pointwise Cauchy–Schwarz, three-factor `(3,6,2)` Hölder on `T³`, and the
  physical Hölder line `≤ ‖v‖₃‖∇v‖₆‖Δv‖₂`);
* **§2** reproduces lane 377/396/405/413's genuine nonzero smooth mean-zero
  periodic witness `probeMZ = meanZeroPartT (x ↦ cos(2π x₀)·e₀)` (research
  probes cannot import one another) and instantiates the estimate there — so
  neither the hypotheses nor the conclusion is vacuous;
* **§3** is the shape check for the U10b consumer: the estimate written out at a
  spatial slice `fun x ↦ meanFreeVelocity g w.velocity (t, x)`, with the right
  side in the `criticalY` / `laplacianSqT` spelling of
  `Section3/T20/CriticalRegularity.lean:67-100` — exactly the term U10b's
  `hOneEnergy` field must absorb.

Run: `cd verification && lake env lean ../research/T20/probes/h1_trilinear_closes.lean`
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

/-! ## 1. The U10a target and its explicit constant -/

example : h1TrilinearConst = CcriticalHalf * Csix := rfl

example : 0 < h1TrilinearConst := h1TrilinearConst_pos

/-- The `ℝ≥0∞` form: no finiteness hypothesis. -/
example (v : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v) :
    ENNReal.ofReal
        |∫ y : PeriodicTorus,
            torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (laplacian v x) : ℝ)) y
              ∂periodicTorusMeasure| ≤
      ENNReal.ofReal h1TrilinearConst * periodicHomogeneousENorm (1 / 2) v *
        periodicLpENorm 2 (laplacian v) ^ 2 :=
  h1Trilinear_enorm v hv hhalf

/-- The real form in the U10b spelling (`laplacianSqT`). -/
example (v : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v) :
    |∫ y : PeriodicTorus,
        torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (laplacian v x) : ℝ)) y
          ∂periodicTorusMeasure| ≤
      h1TrilinearConst * (periodicHomogeneousENorm (1 / 2) v).toReal * laplacianSqT v :=
  h1Trilinear v hv hhalf

/-- `laplacianSqT` really is `‖Δv‖₂²` (`CriticalRegularity.lean:98`). -/
example (v : SpatialField) :
    laplacianSqT v = (periodicLpENorm 2 (laplacian v)).toReal ^ 2 := rfl

/-- The `periodicPairing` form (the canonical T20 `L²(T³)` pairing). -/
example (v : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v) :
    |periodicPairing (fun x ↦ advection (lift v) 0 x) (laplacian v)| ≤
      h1TrilinearConst * (periodicHomogeneousENorm (1 / 2) v).toReal * laplacianSqT v :=
  h1Trilinear_pairing v hv hhalf

/-- The intermediate Hölder line `|⟪(v·∇)v,Δv⟫| ≤ ‖v‖₃‖∇v‖₆‖Δv‖₂`
(`03-torus.tex:470-471`, first inequality). -/
example (v : SpatialField) (hv : SmoothPeriodicT v) :
    ENNReal.ofReal
        |∫ y : PeriodicTorus,
            torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (laplacian v x) : ℝ)) y
              ∂periodicTorusMeasure| ≤
      periodicLpENorm 3 v * periodicLpENorm 6 (gradientTensor v) *
        periodicLpENorm 2 (laplacian v) :=
  h1AdvectionHolderT v hv

/-- The pointwise input. -/
example (v Lv : SpatialField) (x : Space) :
    ‖(inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)‖ₑ ≤
      ‖v x‖ₑ * ‖gradientTensor v x‖ₑ * ‖Lv x‖ₑ :=
  enorm_inner_advection_leH1 v Lv x

/-- Three-factor Hölder `(3, 6, 2)` on the probability torus. -/
example {f g h : PeriodicTorus → ℝ}
    (hf : AEStronglyMeasurable f periodicTorusMeasure)
    (hg : AEStronglyMeasurable g periodicTorusMeasure)
    (hh : AEStronglyMeasurable h periodicTorusMeasure) :
    ∫⁻ y, ‖f y‖ₑ * ‖g y‖ₑ * ‖h y‖ₑ ∂periodicTorusMeasure ≤
      eLpNorm f 3 periodicTorusMeasure * eLpNorm g 6 periodicTorusMeasure *
        eLpNorm h 2 periodicTorusMeasure :=
  lintegral_enorm_mul_three_le_torus_three_six_two hf hg hh

/-- The two T12 embeddings the constant is assembled from, in the exact
spellings §1 of the module produces. -/
example (v : SpatialField) (hhalf : MemPeriodicHomogeneous (1 / 2) v) :
    periodicLpENorm 3 v ≤
      ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v :=
  velocityCriticalL3 v hhalf

example (v : SpatialField) (hv : SmoothPeriodicT v) (hm : IsMeanZeroT v) :
    periodicLpENorm 6 (gradientTensor v) ≤
      ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian v) :=
  gradientLSix v hv hm

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

/-- The U10a estimate at the nonzero witness: the hypotheses are all satisfiable
and the conclusion is not vacuous. -/
example : probeMZ ≠ (0 : SpatialField) ∧
    |periodicPairing (fun x ↦ advection (lift probeMZ) 0 x) (laplacian probeMZ)| ≤
      h1TrilinearConst * (periodicHomogeneousENorm (1 / 2) probeMZ).toReal *
        laplacianSqT probeMZ :=
  ⟨probeMZ_ne_zero,
    h1Trilinear_pairing probeMZ probeMZ_smoothPeriodic probeMZ_memHalf⟩

/-- `‖Δv‖₂` is genuinely finite at the witness, so the `.toReal` on the right of
the estimate is not a junk zero coming from `⊤`. -/
example : periodicLpENorm 2 (laplacian probeMZ) ≠ ⊤ :=
  periodicLpENorm_two_laplacian_ne_top probeMZ probeMZ_smoothPeriodic

/-! ## 3. Shape check: exactly what U10b (`hOneEnergy`) consumes -/

/-- The time-slice bridge, `rfl`: `meanFreeEquation`'s `advection u t x` is the
spatial advection of the slice that U10a estimates. -/
example (u : SpaceTimeField) (t : ℝ) (x : Space) :
    advection u t x = advection (lift (fun y ↦ u (t, y))) 0 x :=
  advection_eq_sliceH1 u t x

/-- **The U10b slice spelling.**  For the mean-free velocity of a classical
solution at an interior time `t`, with the regularity `reductionRegular`
supplies, the nonlinear term of `eq:H1energy` obeys
`|⟪(v·∇)v, Δv⟫| ≤ C₁ · y(t) · ‖Δv(t)‖₂²`
with `y = criticalY …`, `‖Δv‖₂² = laplacianSqT …`, `C₁ = h1TrilinearConst` —
exactly the term U10b must absorb into `(ν/4)‖Δv‖₂²` via `yBound` (U9). -/
example (g u : SpaceTimeField) (t : ℝ)
    (hv : SmoothPeriodicT (fun x ↦ meanFreeVelocity g u (t, x)))
    (hhalf : MemPeriodicHomogeneous (1 / 2) (fun x ↦ meanFreeVelocity g u (t, x))) :
    |periodicPairing (fun x ↦ advection (meanFreeVelocity g u) t x)
        (laplacian (fun x ↦ meanFreeVelocity g u (t, x)))| ≤
      h1TrilinearConst * (criticalY (meanFreeVelocity g u) t).toReal *
        laplacianSqT (fun x ↦ meanFreeVelocity g u (t, x)) :=
  h1Trilinear_slice g u t hv hhalf

end NSFormalization.Section3.T20
