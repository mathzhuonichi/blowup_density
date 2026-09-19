import NSFormalization.Section3.T23.NormBridge
import NSFormalization.Section3.T24.AffineEnergy
import NSFormalization.Paper1.ScalingLimits

/-! Domain restriction and closeness rates for T23. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section4.I02 (spatialGradient)
open scoped ENNReal Topology

/-- Restricting the spatial measure contracts both summands of the energy. -/
theorem domainEnergyENorm_le (Ω : Set Space) (T : ℝ) (z : VelocityField) :
    domainEnergyENorm Ω T z ≤ NSFormalization.Section3.T24.energyENorm T z := by
  apply add_le_add
  · exact essSup_mono_ae (Filter.Eventually.of_forall fun t =>
      eLpNorm_mono_measure (fun x => z (t, x)) Measure.restrict_le_self)
  · apply ENNReal.rpow_le_rpow _ (by norm_num)
    apply lintegral_mono
    intro t
    exact ENNReal.rpow_le_rpow
      (eLpNorm_mono_measure (fun x => spatialGradient z t x) Measure.restrict_le_self)
      (by norm_num)

/-- The whole-space correction constant is made nonnegative once, before ε. -/
def energyConst (C : ℝ) : ℝ := max C 0

theorem energyConst_nonneg (C : ℝ) : 0 ≤ energyConst C := le_max_right _ _

/-- Transport the canonical I03 perturbation energy estimate, with its two
separate exponents, through restriction and the insertion formula. -/
theorem energyRate {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K Ω : Set Space} {a : Space → Space} {g : VelocityField}
    (place : DomainPlacementData u p f K) {δ : ℝ} (D : CutoffData)
    (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
    (velocity : ℝ → VelocityField) (M E C ε₀ : ℝ)
    (hformula : ∀ ε z, velocity ε z = reference.velocity z + D.correction ε z +
      NSFormalization.Section3.T15.scaledVelocity u place.x₀ place.T ε z)
    (hwhole : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      NSFormalization.Section3.T24.energyENorm place.T
        (fun z => D.correction ε z +
          NSFormalization.Section3.T15.scaledVelocity u place.x₀ place.T ε z) ≤
        ENNReal.ofReal ((M + E) * ε ^ ((1 : ℝ) / 2) + C * ε ^ ((3 : ℝ) / 2))) :
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      domainEnergyENorm Ω place.T (fun z => velocity ε z - reference.velocity z) ≤
        ENNReal.ofReal ((M + E) * ε ^ ((1 : ℝ) / 2) +
          energyConst C * ε ^ ((3 : ℝ) / 2)) := by
  intro ε hε
  have heq : (fun z => velocity ε z - reference.velocity z) =
      (fun z => D.correction ε z +
        NSFormalization.Section3.T15.scaledVelocity u place.x₀ place.T ε z) := by
    funext z
    rw [hformula]
    abel
  rw [heq]
  exact (domainEnergyENorm_le Ω place.T _).trans ((hwhole ε hε).trans
    (ENNReal.ofReal_le_ofReal (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hε.1.le _)))))

end NSFormalization.Section3.T23
