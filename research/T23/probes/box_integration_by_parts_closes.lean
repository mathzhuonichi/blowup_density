import NSFormalization.Section3.T23.BoxIntegration

noncomputable section
open Set MeasureTheory
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
