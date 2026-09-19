import NSFormalization.Section3.T23.NoSlipUniqueness
import NavierStokes.PeriodicUniqueness

/-! Energy calculus on bounded domains with the explicit boundary IBP identity. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open scoped ContDiff InnerProductSpace Topology

/-- Neighborhood smoothness on a compact closure implies set integrability. -/
theorem integrableOn_of_contDiffAt_closure {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set Space} {f : Space → E}
    (hΩ : Bornology.IsBounded Ω) (hf : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ f x) :
    IntegrableOn f Ω :=
  ((show ContinuousOn f (closure Ω) from fun x hx =>
    (hf x hx).continuousAt.continuousWithinAt).integrableOn_compact
      hΩ.isCompact_closure).mono_set subset_closure

/-- A coordinate derivative retains neighborhood smoothness. -/
theorem contDiffAt_partial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} {x : Space} (hf : ContDiffAt ℝ ∞ f x) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => fderiv ℝ f y (coordinateVector i)) x := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiffAt_const

/-- Componentwise differentiation commutes with the Euclidean projection. -/
theorem fderiv_component_at {f : Space → Space} {x : Space}
    (hf : ContDiffAt ℝ ∞ f x) (j : Fin 3) (v : Space) :
    fderiv ℝ (fun y => f y j) x v = fderiv ℝ f x v j := by
  exact congrArg (fun A : Space →L[ℝ] ℝ => A v)
    (((EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp x
      (hf.differentiableAt (by simp)).hasFDerivAt).fderiv)

/-- Scalar transport IBP; the transporting field vanishes on the frontier. -/
theorem IBP.integral_fderiv_apply {Ω : Set Space} (hI : IBP Ω)
    (hΩ : Bornology.IsBounded Ω) (hm : MeasurableSet Ω)
    {f : Space → ℝ} {v : Space → Space}
    (hf : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ f x)
    (hv : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ v x)
    (hz : ∀ x ∈ frontier Ω, v x = 0) :
    (∫ x in Ω, fderiv ℝ f x (v x)) =
      -(∫ x in Ω, f x * ∑ i : Fin 3, fderiv ℝ v x (coordinateVector i) i) := by
  have hc (i : Fin 3) (x : Space) (hx : x ∈ closure Ω) :
      ContDiffAt ℝ ∞ (fun y => v y i) x :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.contDiffAt.comp x (hv x hx)
  conv_lhs => arg 2; ext x; rw [NavierStokes.PeriodicUniqueness.fderiv_apply_eq_sum]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum, integral_finsetSum, ← Finset.sum_neg_distrib]
  · apply Finset.sum_congr rfl
    intro i _
    have h := hI (fun x => v x i) f
      (fun x hx => (hc i x hx).of_le (by simp))
      (fun x hx => (hf x hx).of_le (by simp)) (fun x hx => by simp [hz x hx]) i
    rw [h]
    congr 1
    apply setIntegral_congr_fun hm
    intro x hx
    dsimp
    rw [fderiv_component_at (hv x (subset_closure hx))]
    ring
  · intro i _
    apply integrableOn_of_contDiffAt_closure hΩ
    intro x hx
    exact (hf x hx).mul ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.contDiffAt.comp x
      (contDiffAt_partial (hv x hx) i))
  · intro i _
    exact integrableOn_of_contDiffAt_closure hΩ fun x hx =>
      (hc i x hx).mul (contDiffAt_partial (hf x hx) i)

/-- Divergence-free no-slip transport integrates to zero. -/
theorem IBP.integral_fderiv_apply_zero {Ω : Set Space} (hI : IBP Ω)
    (hΩ : Bornology.IsBounded Ω) (hm : MeasurableSet Ω)
    {f : Space → ℝ} {v : Space → Space}
    (hf : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ f x)
    (hv : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ v x)
    (hz : ∀ x ∈ frontier Ω, v x = 0)
    (hd : ∀ x ∈ Ω, (∑ i : Fin 3, fderiv ℝ v x (coordinateVector i) i) = 0) :
    (∫ x in Ω, fderiv ℝ f x (v x)) = 0 := by
  rw [hI.integral_fderiv_apply hΩ hm hf hv hz]
  rw [setIntegral_eq_zero_of_forall_eq_zero (fun x hx => by rw [hd x hx, mul_zero]), neg_zero]

/-- The advective transport term makes no contribution to difference energy. -/
theorem IBP.integral_transport_energy_zero {Ω : Set Space} (hI : IBP Ω)
    (hΩ : Bornology.IsBounded Ω) (hm : MeasurableSet Ω)
    {w v : Space → Space}
    (hw : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ w x)
    (hv : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ v x)
    (hz : ∀ x ∈ frontier Ω, v x = 0)
    (hd : ∀ x ∈ Ω, (∑ i : Fin 3, fderiv ℝ v x (coordinateVector i) i) = 0) :
    (∫ x in Ω, ⟪w x, fderiv ℝ w x (v x)⟫_ℝ) = 0 := by
  have h := hI.integral_fderiv_apply_zero hΩ hm (fun x hx => (hw x hx).norm_sq ℝ) hv hz hd
  have he : (∫ x in Ω, fderiv ℝ (fun y => ‖w y‖ ^ 2) x (v x)) =
      ∫ x in Ω, 2 * ⟪w x, fderiv ℝ w x (v x)⟫_ℝ := by
    apply setIntegral_congr_fun hm
    intro x hx
    dsimp
    rw [((hw x (subset_closure hx)).differentiableAt (by simp)).hasFDerivAt.norm_sq.fderiv]
    simp
  rw [he, integral_const_mul] at h
  linarith
/-- A scalar field vanishing on the boundary has zero integrated derivative. -/
theorem IBP.integral_partial_zero {Ω : Set Space} (hI : IBP Ω)
    {f : Space → ℝ} (hf : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ f x)
    (hz : ∀ x ∈ frontier Ω, f x = 0) (i : Fin 3) :
    (∫ x in Ω, fderiv ℝ f x (coordinateVector i)) = 0 := by
  have h := hI f (fun _ => 1) (fun x hx => (hf x hx).of_le (by simp))
    (fun _ _ => contDiffAt_const) hz i
  simpa using h.symm

/-- Vector IBP derived from the scalar identity, with no-slip first factor. -/
theorem IBP.integral_inner_partial {Ω : Set Space} (hI : IBP Ω)
    (hΩ : Bornology.IsBounded Ω) (hm : MeasurableSet Ω)
    {f g : Space → Space}
    (hf : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ f x)
    (hg : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ g x)
    (hz : ∀ x ∈ frontier Ω, f x = 0) (i : Fin 3) :
    (∫ x in Ω, ⟪f x, fderiv ℝ g x (coordinateVector i)⟫_ℝ) =
      -(∫ x in Ω, ⟪fderiv ℝ f x (coordinateVector i), g x⟫_ℝ) := by
  have h := hI.integral_partial_zero (fun x hx => (hf x hx).inner ℝ (hg x hx))
    (fun x hx => by simp [hz x hx]) i
  have he : (∫ x in Ω, fderiv ℝ (fun y => ⟪f y, g y⟫_ℝ) x (coordinateVector i)) =
      ∫ x in Ω, ⟪f x, fderiv ℝ g x (coordinateVector i)⟫_ℝ +
        ⟪fderiv ℝ f x (coordinateVector i), g x⟫_ℝ := by
    apply setIntegral_congr_fun hm
    intro x hx
    dsimp
    rw [(((hf x (subset_closure hx)).differentiableAt (by simp)).hasFDerivAt.inner ℝ
      ((hg x (subset_closure hx)).differentiableAt (by simp)).hasFDerivAt).fderiv]
    rfl
  rw [he, integral_add
    (integrableOn_of_contDiffAt_closure hΩ fun x hx =>
      (hf x hx).inner ℝ (contDiffAt_partial (hg x hx) i))
    (integrableOn_of_contDiffAt_closure hΩ fun x hx =>
      (contDiffAt_partial (hf x hx) i).inner ℝ (hg x hx))] at h
  linarith

/-- The viscous pairing is minus the integrated squared gradient. -/
theorem IBP.integral_laplacian_energy {Ω : Set Space} (hI : IBP Ω)
    (hΩ : Bornology.IsBounded Ω) (hm : MeasurableSet Ω)
    {w : SpaceTimeField} {t : ℝ}
    (hw : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => w (t, y)) x)
    (hz : ∀ x ∈ frontier Ω, w (t, x) = 0) :
    (∫ x in Ω, ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) =
      -(∫ x in Ω, ∑ i : Fin 3, ‖spatialDerivative w t x (coordinateVector i)‖ ^ 2) := by
  simp only [spatialLaplacian, inner_sum]
  rw [integral_finsetSum, integral_finsetSum, ← Finset.sum_neg_distrib]
  · apply Finset.sum_congr rfl
    intro i _
    simpa only [real_inner_self_eq_norm_sq, spatialDerivative] using hI.integral_inner_partial hΩ hm hw
      (fun x hx => contDiffAt_partial (hw x hx) i) hz i
  · intro i _
    exact integrableOn_of_contDiffAt_closure hΩ fun x hx =>
      (contDiffAt_partial (hw x hx) i).norm_sq ℝ
  · intro i _
    exact integrableOn_of_contDiffAt_closure hΩ fun x hx =>
      (hw x hx).inner ℝ (contDiffAt_partial (contDiffAt_partial (hw x hx) i) i)

/-- The pressure pairing vanishes by divergence and no-slip, with no gauge assumption. -/
theorem IBP.integral_pressure_energy_zero {Ω : Set Space} (hI : IBP Ω)
    (hΩ : Bornology.IsBounded Ω) (hm : MeasurableSet Ω)
    {w : SpaceTimeField} {p : SpaceTimeScalar} {t : ℝ}
    (hw : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => w (t, y)) x)
    (hp : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => p (t, y)) x)
    (hz : ∀ x ∈ frontier Ω, w (t, x) = 0)
    (hd : ∀ x ∈ Ω, spatialDivergence w t x = 0) :
    (∫ x in Ω, ⟪w (t, x), pressureGradient p t x⟫_ℝ) = 0 := by
  simp only [NavierStokes.PeriodicUniqueness.inner_pressureGradient]
  exact hI.integral_fderiv_apply_zero hΩ hm hp hw hz hd

end NSFormalization.Section3.T23

