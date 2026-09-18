import NSFormalization.Section3.T17.Transport
import NSFormalization.Section3.T17.LatticeDeriv
import NSFormalization.Paper1.CorrectionForceProfile
import NSFormalization.Source.PhysicalRemoval

/-! # T17, unit U6: derivative bounds for the concrete correction force

The Euclidean force estimate is transported through `force_eq` and the same
single-copy lattice derivative bridge used for the correction itself.
-/

noncomputable section

namespace NSFormalization.Section3.T17

open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T16
open NSFormalization.Section3.T10 (IsPeriodicOn)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Paper1.CorrectionProfile
open NSFormalization.Source.PhysicalRemoval
open NSFormalization.Paper1.CorrectionForceProfile
open NSFormalization.Source.LocalizedInsertion (correctionForce_support)
open scoped ContDiff Topology BigOperators

/-! The Paper1 constants, fixed before the scale is quantified. -/

def forceDerivConst (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) : ℕ → ℝ :=
  fun m => Classical.choose
    (physicalForce_spatial_derivative_bound ν hv x₀ T hθ hη hθc hηc m)

theorem forceDerivConst_nonneg (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∀ m, 0 ≤ forceDerivConst ν hv x₀ T hθ hη hθc hηc m := by
  intro m
  exact (Classical.choose_spec
    (physicalForce_spatial_derivative_bound ν hv x₀ T hθ hη hθc hηc m)).1

/-! The concrete field, with the exact quantifier order of the Spec field.
The global `hv` premise is present because Paper1's
`physicalForce_spatial_derivative_bound` requires it; it also supplies the
local smoothness premise of `force_eq`. -/

theorem force_derivative_bound (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hε₀ : ε₀ ≤ 1)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ m : ℕ,
      ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
        ∀ z : SpaceTime,
          ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
            ‖iteratedFDeriv ℝ m
                (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) z
                (fun i => ((0 : ℝ), u i))‖ ≤
              forceDerivConst ν hv x₀ T hθ hη hθc hηc m *
                (ε⁻¹) ^ (2 + m) := by
  intro m ε hε z u hu
  have hεIoc : ε ∈ Ioc (0 : ℝ) 1 :=
    ⟨hε.1, hε.2.trans hε₀⟩
  have hρ : ε * θR < r := hεspace ε hε
  have hsum : r + ε * θR ≤ 1 := by nlinarith
  have hforce := force_eq (ν := ν) (v := v) (x₀ := x₀) (T := T)
    (δ := δ) (r := r) (θ := θ) (η := η) (O := O) (θR := θR)
    (ε₀ := ε₀) (ε := ε) hvper hv.contDiffOn hθ hη hθc hηc hθsupp hηsupp hr2
    hε.1 hρ (hεtime ε hε)
  rw [hforce]
  have hslice : ∀ (t : ℝ) (y : Space),
      NSFormalization.Source.correctionForce ν v
          (physicalCorrection v x₀ T θ η ε) (t, y) ≠ 0 →
        y ∈ ball x₀ (ε * θR) := by
    intro t y hy
    have hmem := correctionForce_support ν v
      (physicalCorrection v x₀ T θ η ε) (subset_tsupport _ hy)
    exact (physical_support hε.1 v x₀ T hθc hηc hθsupp hηsupp hmem).2
  obtain ⟨k, hk⟩ := latticeLift_iteratedFDeriv_eq
    hslice hsum hρ z m (fun i => ((0 : ℝ), u i))
  rw [hk]
  exact (Classical.choose_spec
    (physicalForce_spatial_derivative_bound ν hv x₀ T hθ hη hθc hηc m)).2
    ε hεIoc (z - (0, latticeVector k)) u hu

end NSFormalization.Section3.T17
