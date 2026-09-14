import NSFormalization.Section4.A01.L2Descent

/-! Reviewer probe (lane 153), **mutation 1** — replace the `θ`-average `G₀ x := ∫ θ, g₀ (x,θ)` by
the `θ = 0` slice `G₀ x := g₀ (x, 0)` and show the slice-constancy step breaks.

This is the mathematical heart of piece (d): the invariance datum is `∀ᵐ θ`, and pinning it at the
single angle `θ = -pt.2` needed for a fixed slice is exactly what a null set forbids.  `AddCircle 1`
is atomless, so `{-pt.2}` is `volume`-null and the instantiation is not merely unavailable, it is
false in general.  The average, by contrast, needs only the a.e. statement (`integral_congr_ae`). -/

noncomputable section
namespace Rev153Mut1

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerCylinderSobolev
open scoped ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
  constructor; simp [AddCircle.measure_univ]


/-- POSITIVE CONTROL: the same hypothesis, with the `θ`-average, closes (this is the module's route,
`L2Descent.lean:99-110`). -/
example (g₀ : LiftDomain (1 : ℝ) → Space)
    (hswap : ∀ᵐ pt ∂(liftMeasure 1), ∀ᵐ θ ∂(volume : Measure (AddCircle (1 : ℝ))),
      g₀ pt = g₀ (pt + ((0 : Vector3), θ))) :
    ∀ᵐ pt ∂(liftMeasure 1),
      g₀ pt = ∫ θ, g₀ (pt.1, θ) ∂(volume : Measure (AddCircle (1 : ℝ))) := by
  filter_upwards [hswap] with pt hpt
  calc g₀ pt
      = ∫ _θ : AddCircle (1 : ℝ), g₀ pt ∂volume := by rw [integral_const]; simp
    _ = ∫ θ, g₀ (pt + ((0 : Vector3), θ)) ∂volume := integral_congr_ae hpt
    _ = ∫ θ, g₀ (pt.1, pt.2 + θ) ∂volume := by
          refine integral_congr_ae (ae_of_all _ (fun θ => ?_))
          show g₀ (pt + ((0 : Vector3), θ)) = g₀ (pt.1, pt.2 + θ)
          rw [show pt + ((0 : Vector3), θ) = (pt.1, pt.2 + θ) from by simp [Prod.add_def]]
    _ = ∫ θ, g₀ (pt.1, θ) ∂volume :=
          integral_add_left_eq_self (fun θ => g₀ (pt.1, θ)) pt.2

/-- What the a.e. datum *does* give at a point: SOME angle, depending on `pt`, not the fixed `0`. -/
example (g₀ : LiftDomain (1 : ℝ) → Space) (pt : LiftDomain (1 : ℝ))
    (hpt : ∀ᵐ θ ∂(volume : Measure (AddCircle (1 : ℝ))), g₀ pt = g₀ (pt + ((0 : Vector3), θ))) :
    ∃ θ : AddCircle (1 : ℝ), g₀ pt = g₀ (pt.1, pt.2 + θ) := by
  obtain ⟨θ, hθ⟩ := hpt.exists
  exact ⟨θ, by rw [hθ, show pt + ((0 : Vector3), θ) = (pt.1, pt.2 + θ) from by simp [Prod.add_def]]⟩

/-- MUTANT: the `θ = 0` slice in place of the `θ`-average.  Expected to FAIL. -/
example (g₀ : LiftDomain (1 : ℝ) → Space)
    (hswap : ∀ᵐ pt ∂(liftMeasure 1), ∀ᵐ θ ∂(volume : Measure (AddCircle (1 : ℝ))),
      g₀ pt = g₀ (pt + ((0 : Vector3), θ))) :
    ∀ᵐ pt ∂(liftMeasure 1), g₀ pt = g₀ (pt.1, 0) := by
  filter_upwards [hswap] with pt hpt
  -- the only route to a *fixed* slice: instantiate the invariance at the single angle `-pt.2`
  have key : g₀ pt = g₀ (pt + ((0 : Vector3), -pt.2)) := hpt (-pt.2)
  rw [key]
  simp [Prod.add_def]

end Rev153Mut1
