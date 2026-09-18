import NSFormalization.Section3.T17.Transport
import NSFormalization.Section3.T17.LatticeDeriv
import NSFormalization.Paper1.CorrectionProfile
import NSFormalization.Source.PhysicalRemoval

/-! # T17, unit U5: derivative bounds for the concrete correction

The constants below are the constants selected by the corresponding Euclidean
Paper1 estimate.  The bound is then transported pointwise through the single
copy selected by `latticeLift_iteratedFDeriv_eq`.
-/

noncomputable section

namespace NSFormalization.Section3.T17

open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Source.PhysicalRemoval
open NSFormalization.Paper1.CorrectionProfile
open scoped ContDiff Topology BigOperators

/-! The Paper1 constants, fixed before the scale is quantified. -/

def correctionDerivConst {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) : ℕ → ℕ → ℝ :=
  fun j m => Classical.choose
    (physical_mixed_derivative_bound hv x₀ T hθ hη hθc hηc j m)

theorem correctionDerivConst_nonneg {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∀ j m, 0 ≤ correctionDerivConst hv x₀ T hθ hη hθc hηc j m := by
  intro j m
  exact (Classical.choose_spec
    (physical_mixed_derivative_bound hv x₀ T hθ hη hθc hηc j m)).1

/-! The concrete field, with the exact quantifier order of the Spec field.
The global `hv` premise is present because Paper1's
`physical_mixed_derivative_bound` requires it. -/

theorem correction_derivative_bound_mutated {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) (θR ε₀ r : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ Metric.ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hε₀ : ε₀ ≤ 1)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ j m : ℕ,
      ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
        ∀ z : SpaceTime,
          ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
            ‖iteratedFDeriv ℝ (j + m)
                ((correctionData v x₀ T θ η O θR ε₀).correction ε) z
                (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space)))
                  (fun i => ((0 : ℝ), u i)))‖ ≤
              correctionDerivConst hv x₀ T hθ hη hθc hηc j m *
                (ε⁻¹) ^ (2 * j + m + 1) := by
  intro j m ε hε z u hu
  have hεIoc : ε ∈ Ioc (0 : ℝ) 1 :=
    ⟨hε.1, hε.2.trans hε₀⟩
  have hρ : ε * θR < r := hεspace ε hε
  have hsum : r + ε * θR ≤ 1 := by nlinarith
  have hslice : ∀ (t : ℝ) (y : Space),
      physicalCorrection v x₀ T θ η ε (t, y) ≠ 0 → y ∈ ball x₀ (ε * θR) := by
    intro t y hy
    exact (physical_support hε.1 v x₀ T hθc hηc hθsupp hηsupp
      (subset_tsupport _ hy)).2
  obtain ⟨k, hk⟩ := latticeLift_iteratedFDeriv_eq
    hslice hsum hρ z (j + m)
      (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space)))
        (fun i => ((0 : ℝ), u i)))
  rw [correctionData_correction, hk]
  exact (Classical.choose_spec
    (physical_mixed_derivative_bound hv x₀ T hθ hη hθc hηc j m)).2
    ε hεIoc (z - (0, latticeVector k)) u hu

end NSFormalization.Section3.T17
