import NSFormalization.Section3.T23.NoSlipUniqueness

/-! Partial U7 probe. Checks the proved analytic pieces; does not assert that
noSlip_uniqueness exists or that the difference-energy identity is proved. -/
noncomputable section
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T23
open scoped ContDiff

-- The no-slip scalar integration-by-parts identity, with its literal hypotheses.
example (a b : Fin 3 → ℝ) (hab : ∀ i, a i < b i)
    (f g : (Fin 3 → ℝ) → ℝ)
    (hf : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 f x)
    (hg : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 g x)
    (hz : ∀ x ∈ frontier (Icc a b), f x = 0) (j : Fin 3) :
    (∫ x in Icc a b, f x * fderiv ℝ g x (Pi.single j 1)) =
      -(∫ x in Icc a b, fderiv ℝ f x (Pi.single j 1) * g x) :=
  box_integral_mul_fderiv_eq_neg a b hab f g hf hg hz j

-- The original solution records alone supply finite difference energy.
example {ν T₁ T₂ : ℝ} {Ω : Set Space} {a : SpatialField} {g : SpaceTimeField}
    (hΩ : IsBoundedBoxOrSmoothDomain Ω)
    (u₁ : ClassicalSolutionOmega ν Ω a g T₁)
    (u₂ : ClassicalSolutionOmega ν Ω a g T₂)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (min T₁ T₂)) :
    IntegrableOn (fun x => ‖u₁.velocity (t, x) - u₂.velocity (t, x)‖ ^ 2) Ω :=
  difference_energy_integrable hΩ.2.1 u₁ u₂ ht

-- The derivative bound is derived, not stored as an additional solution field.
example {ν T : ℝ} {Ω : Set Space} {a : SpatialField} {g : SpaceTimeField}
    (hΩ : IsBoundedBoxOrSmoothDomain Ω) (u : ClassicalSolutionOmega ν Ω a g T)
    {S : ℝ} (hS : S < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) S, ∀ x ∈ closure Ω,
      ‖spatialDerivative u.velocity t x‖ ≤ C :=
  u.spatialDerivative_bound hΩ.2.1 hS
