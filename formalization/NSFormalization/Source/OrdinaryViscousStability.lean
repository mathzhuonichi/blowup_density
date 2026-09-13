import Euler.OrdinaryEulerL2Stability

/-! Viscous stability reusing the established noncompact ordinary L2 cancellations. -/
noncomputable section
namespace NSFormalization.Source.OrdinaryViscousStability
open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap
  EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSolenoidal EulerMeanClassical EulerVolterraConvolution EulerOrdinarySobolev
open scoped ContDiff Topology

/-- The three actual second directional derivatives form the Laplacian field. -/
def laplacianField (W : SmoothL2Field Space) : SmoothL2Field Space :=
  sumField Finset.univ (fun i : Fin 3 => (W.directionalField (axis i)).directionalField (axis i))

/-- This field is the actual Euclidean Laplacian of its smooth representative. -/
theorem laplacianField_field (W : SmoothL2Field Space) :
    (laplacianField W).field = Laplacian.laplacian W.field := by
  rw [EulerMeanVectorIdentities.vector_laplacian_eq_sum W.field W.smooth]
  funext x
  simp only [laplacianField, sumField_field]
  apply Finset.sum_congr rfl
  intro i _
  rw [directionalField_field]
  have he : (W.directionalField (axis i)).field =
      EulerMeanVectorIdentities.vectorPartial W.field i := by
    funext y
    rw [directionalField_field]
    rfl
  rw [he]
  rfl

theorem laplacian_pairing (W : SmoothL2Field Space) :
    ⟪W.toLp, (laplacianField W).toLp⟫_ℝ =
      -∑ i : Fin 3, ‖(W.directionalField (axis i)).toLp‖ ^ 2 := by
  have hp (i : Fin 3) :
      ⟪W.toLp, ((W.directionalField (axis i)).directionalField (axis i)).toLp⟫_ℝ =
        -‖(W.directionalField (axis i)).toLp‖ ^ 2 := by
    have h := field_directional_inner W (W.directionalField (axis i)) (axis i)
    rw [real_inner_self_eq_norm_sq] at h
    linarith
  simp only [laplacianField, toLp_sumField, inner_sum, hp,
    Finset.sum_neg_distrib]

theorem laplacian_pairing_nonpos (W : SmoothL2Field Space) :
    ⟪W.toLp, (laplacianField W).toLp⟫_ℝ ≤ 0 := by
  rw [laplacian_pairing]
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- The forcing has already canceled in the exact difference equation.
Transport and gradient pressure use the existing ordinary Euler cancellation;
only the nonpositive viscous term is added here. -/
theorem viscous_difference_pairing {ν : ℝ} (hν : 0 ≤ ν)
    (U W P D : SmoothL2Field Space) (K : ℝ)
    (hK : ∀ x, ‖fderiv ℝ U.field x‖ ≤ K)
    (hdiv : ∀ x, divergence (addField U W).field x = 0)
    (hW : W.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace)
    (hD : ∀ x, D.field x = (differenceRhs U W P).field x + ν • (laplacianField W).field x) :
    2 * ⟪W.toLp, D.toLp⟫_ℝ ≤ 2 * K * ‖W.toLp‖ ^ 2 := by
  have he : ⟪W.toLp, D.toLp⟫_ℝ =
      ⟪W.toLp, (differenceRhs U W P).toLp⟫_ℝ + ν * ⟪W.toLp, (laplacianField W).toLp⟫_ℝ := by
    simp_rw [field_inner, hD, inner_add_right, real_inner_smul_right]
    rw [integral_add (field_inner_integrable W (differenceRhs U W P))
      ((field_inner_integrable W (laplacianField W)).const_mul ν), integral_const_mul]
  rw [he]
  have hb := differenceRhs_l2_bound U W P K hK hdiv hW hP
  have hd := mul_nonpos_of_nonneg_of_nonpos hν (laplacian_pairing_nonpos W)
  nlinarith

/-- A genuine L2-jet evolution satisfying the viscous difference equation has
Gronwall stability. No support premise or assumed energy inequality is used. -/
theorem difference_energy_bound {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 ≤ ν)
    (U W P D : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hWc : ∀ n, Continuous (fun t => (W t).jetLp n))
    (hDc : ∀ n, Continuous (fun t => (D t).jetLp n))
    (hTime : ∀ t (ht : t ∈ Ioo 0 T) x,
      HasDerivAt (fun r => (W (projIcc 0 T hT r)).field x) ((D ⟨t, ht.1.le, ht.2.le⟩).field x) t)
    (K : ℝ) (hK : ∀ t x, ‖fderiv ℝ (U t).field x‖ ≤ K)
    (hdiv : ∀ t x, divergence (addField (U t) (W t)).field x = 0)
    (hW : ∀ t, (W t).toLp ∈ solenoidalSpace)
    (hP : ∀ t, (P t).toLp ∈ gradientSpace)
    (hD : ∀ t x, (D t).field x = (differenceRhs (U t) (W t) (P t)).field x +
      ν • (laplacianField (W t)).field x) (t : Icc (0 : ℝ) T) :
    ‖(W t).toLp‖ ^ 2 ≤ ‖(W ⟨0, le_rfl, hT⟩).toLp‖ ^ 2 * Real.exp (2 * K * t) := by
  let X := fun r : ℝ => ‖(W (projIcc 0 T hT r)).toLp‖ ^ 2
  let X' := fun r : ℝ => 2 * ⟪(W (projIcc 0 T hT r)).toLp, (D (projIcc 0 T hT r)).toLp⟫_ℝ
  have hc : ContinuousOn X (Icc (0 : ℝ) T) := by
    have h' := EulerLpTranslation.SmoothL2Field.continuous_toLp W (hWc 0)
    exact ((h'.comp continuous_projIcc).norm.pow 2).continuousOn
  have hd : ∀ r ∈ Ico (0 : ℝ) T, HasDerivWithinAt X (X' r) (Icc (0 : ℝ) T) r := by
    intro r hr
    have h := (ordinaryWord_hasDerivWithinAt T hT W D hWc hDc hTime
      (Fin.elim0 : Fin 0 → Fin 3) ⟨r, hr.1, hr.2.le⟩).norm_sq
    simpa only [X, X', wordField_zero, projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1, hr.2.le⟩)] using h
  have hb : ∀ r ∈ Ico (0 : ℝ) T, X' r ≤ (2 * K) * X r := by
    intro r _
    exact viscous_difference_pairing hν _ _ _ _ K (hK _) (hdiv _) (hW _) (hP _) (hD _)
  have h := linear_stability_within X X' (2 * K) T hc hd hb t t.property
  simpa only [X, projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)] using h

/-- Zero initial difference implies pointwise equality at every time, after
upgrading the zero L2 class using smooth representatives. -/
theorem difference_zero {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 ≤ ν)
    (U W P D : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hWc : ∀ n, Continuous (fun t => (W t).jetLp n))
    (hDc : ∀ n, Continuous (fun t => (D t).jetLp n))
    (hTime : ∀ t (ht : t ∈ Ioo 0 T) x,
      HasDerivAt (fun r => (W (projIcc 0 T hT r)).field x) ((D ⟨t, ht.1.le, ht.2.le⟩).field x) t)
    (K : ℝ) (hK : ∀ t x, ‖fderiv ℝ (U t).field x‖ ≤ K)
    (hdiv : ∀ t x, divergence (addField (U t) (W t)).field x = 0)
    (hW : ∀ t, (W t).toLp ∈ solenoidalSpace)
    (hP : ∀ t, (P t).toLp ∈ gradientSpace)
    (hD : ∀ t x, (D t).field x = (differenceRhs (U t) (W t) (P t)).field x +
      ν • (laplacianField (W t)).field x)
    (hzero : (W ⟨0, le_rfl, hT⟩).field = 0) : ∀ t, (W t).field = 0 := by
  have hzLp := field_toLp_zero _ hzero
  intro t
  have hb := difference_energy_bound hT hν U W P D hWc hDc hTime K hK hdiv hW hP hD t
  rw [hzLp, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hb
  apply field_zero_of_toLp_zero
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hb (sq_nonneg _)))

end NSFormalization.Source.OrdinaryViscousStability
