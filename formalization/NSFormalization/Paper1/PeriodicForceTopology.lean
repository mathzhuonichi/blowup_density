import NSFormalization.Paper1.PeriodicDensityFiber
import NSFormalization.Paper1.PeriodicForceMeasurability

/-!
# Topological interface for the periodic force gauge

`forceDistance` is an extended-valued time `L¹` gauge.  The symmetry and
zero laws below are proved for the actual Fourier gauge.  The triangle and
monotonicity lemmas expose the exact measurability and pointwise comparison
obligations; they do not silently turn the gauge into a manuscript topology.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicForceTopology

open Set Filter MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper1.PeriodicDensityFiber
open NSFormalization.Paper1.PeriodicForceConvergence
open NSFormalization.Paper1.PeriodicForceSpace
open NSFormalization.Source
open scoped ContDiff ENNReal Topology

def forceProfile (s : ℝ) (f₁ f₂ : VelocityField) : ℝ → ℝ :=
  fun t => periodicVectorSobolevNorm s (f₁ - f₂) t

@[simp] theorem forceDistance_eq_profile (s : ℝ) (f₁ f₂ : VelocityField) :
    forceDistance s f₁ f₂ = eLpNorm (forceProfile s f₁ f₂) 1 volume := rfl

theorem forceProfile_self (s : ℝ) (f : VelocityField) :
    forceProfile s f f = 0 := by
  funext t
  simp [forceProfile, periodicVectorSobolevNorm, periodicSobolevSq,
    periodicFourierCoeff_eq_cube, NavierStokes.PeriodicIntegration.cubeIntegral,
    coordinateForce]

theorem forceDistance_self (s : ℝ) (f : VelocityField) :
    forceDistance s f f = 0 := by
  rw [forceDistance_eq_profile, forceProfile_self]
  exact eLpNorm_zero

/-- Smooth test forces have genuinely measurable periodic Sobolev profiles.
The statement concerns the actual Fourier-series definition and does not
assume finiteness of its time integral. -/
theorem stronglyMeasurable_forceProfile_of_testForces
    {f₁ f₂ : VelocityField} (h₁ : IsTestForce f₁) (h₂ : IsTestForce f₂)
    (s : ℝ) : StronglyMeasurable (forceProfile s f₁ f₂) := by
  have hsub : ContDiff ℝ ∞ (f₁ - f₂) := h₁.smooth.sub h₂.smooth
  have hsq (i : Fin 3) : StronglyMeasurable (fun t : ℝ =>
      periodicSobolevSq s (fun x => coordinateForce (f₁ - f₂) i (t, x))) := by
    exact stronglyMeasurable_periodicSobolevSq_time s
      (coordinateForce_smooth hsub i).continuous
  have hsum : StronglyMeasurable (fun t : ℝ => ∑ i : Fin 3,
      periodicSobolevSq s (fun x => coordinateForce (f₁ - f₂) i (t, x))) := by
    convert (Finset.stronglyMeasurable_sum Finset.univ (fun i _ => hsq i)) using 1
    ext t
    simp
  exact Real.continuous_sqrt.comp_stronglyMeasurable hsum

/- A finite-valued interface for the force gauge.  The component `MemLp`
  premises are exactly the endpoint/time-integrability facts needed to make
  the vector profile finite; no blanket finiteness is inferred from smoothness
  alone. -/
theorem memLp_forceProfile_of_testForces
    {f₁ f₂ : VelocityField} (h₁ : IsTestForce f₁) (h₂ : IsTestForce f₂)
    (s : ℝ)
    (hcomp : ∀ i : Fin 3, MemLp
      (fun t : ℝ => periodicSobolevNorm s
        (fun x => coordinateForce (f₁ - f₂) i (t, x))) 1 volume) :
    MemLp (forceProfile s f₁ f₂) 1 volume := by
  refine ⟨(stronglyMeasurable_forceProfile_of_testForces h₁ h₂ s).aestronglyMeasurable, ?_⟩
  have hbound := eLpNorm_periodicVectorSobolevNorm_le_sum (s := s)
    (F := f₁ - f₂) (fun i => (hcomp i).1)
  exact hbound.trans_lt ((ENNReal.sum_lt_top).2 (fun i _ => (hcomp i).2))

theorem forceDistance_lt_top_of_testForces
    {f₁ f₂ : VelocityField} (h₁ : IsTestForce f₁) (h₂ : IsTestForce f₂)
    (s : ℝ)
    (hcomp : ∀ i : Fin 3, MemLp
      (fun t : ℝ => periodicSobolevNorm s
        (fun x => coordinateForce (f₁ - f₂) i (t, x))) 1 volume) :
    forceDistance s f₁ f₂ < ⊤ := by
  rw [forceDistance_eq_profile]
  exact (memLp_forceProfile_of_testForces h₁ h₂ s hcomp).eLpNorm_lt_top

theorem forceDistance_eq_zero_of_testForces_of_ae_zero
    {f₁ f₂ : VelocityField} (h₁ : IsTestForce f₁) (h₂ : IsTestForce f₂)
    {s : ℝ} (hzero : forceProfile s f₁ f₂ =ᵐ[volume] 0) :
    forceDistance s f₁ f₂ = 0 := by
  rw [forceDistance_eq_profile]
  exact (eLpNorm_eq_zero_iff
    (stronglyMeasurable_forceProfile_of_testForces h₁ h₂ s).aestronglyMeasurable
    (by norm_num : (1 : ℝ≥0∞) ≠ 0)).2 hzero

theorem forceDistance_symm (s : ℝ) (f₁ f₂ : VelocityField) :
    forceDistance s f₁ f₂ = forceDistance s f₂ f₁ := by
  unfold forceDistance
  apply eLpNorm_congr_ae
  filter_upwards [] with t
  rw [show f₁ - f₂ = -(f₂ - f₁) by
    funext z
    simp [sub_eq_add_neg]]
  rw [periodicVectorSobolevNorm_neg]

theorem forceDistance_eq_zero_of_ae_zero
    {s : ℝ} {f₁ f₂ : VelocityField}
    (hmeas : AEStronglyMeasurable (forceProfile s f₁ f₂) volume)
    (hzero : forceProfile s f₁ f₂ =ᵐ[volume] 0) :
    forceDistance s f₁ f₂ = 0 := by
  rw [forceDistance_eq_profile]
  exact (eLpNorm_eq_zero_iff hmeas (by norm_num : (1 : ℝ≥0∞) ≠ 0)).2 hzero

theorem forceDistance_mono
    {s : ℝ} {f₁ f₂ g₂ : VelocityField}
    (hpoint : ∀ t, forceProfile s f₁ f₂ t ≤ forceProfile s f₁ g₂ t) :
    forceDistance s f₁ f₂ ≤ forceDistance s f₁ g₂ := by
  rw [forceDistance_eq_profile, forceDistance_eq_profile]
  apply eLpNorm_mono_real
  intro t
  simp only [forceProfile, periodicVectorSobolevNorm]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact hpoint t

theorem forceDistance_triangle
    {s : ℝ} {f₁ f₂ f₃ : VelocityField}
    (h12 : AEStronglyMeasurable (forceProfile s f₁ f₂) volume)
    (h23 : AEStronglyMeasurable (forceProfile s f₂ f₃) volume)
    (hpoint : ∀ t,
      forceProfile s f₁ f₃ t ≤
        forceProfile s f₁ f₂ t + forceProfile s f₂ f₃ t) :
    forceDistance s f₁ f₃ ≤ forceDistance s f₁ f₂ + forceDistance s f₂ f₃ := by
  rw [forceDistance_eq_profile, forceDistance_eq_profile, forceDistance_eq_profile]
  calc
    eLpNorm (forceProfile s f₁ f₃) 1 volume ≤
        eLpNorm (fun t => forceProfile s f₁ f₂ t + forceProfile s f₂ f₃ t) 1 volume := by
      apply eLpNorm_mono_real
      intro t
      simp only [forceProfile, periodicVectorSobolevNorm]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hpoint t
    _ ≤ eLpNorm (forceProfile s f₁ f₂) 1 volume +
        eLpNorm (forceProfile s f₂ f₃) 1 volume := by
      exact eLpNorm_add_le h12 h23 (by norm_num)

end NSFormalization.Paper1.PeriodicForceTopology
