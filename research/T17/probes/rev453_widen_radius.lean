import NSFormalization.Section3.T17.Assembly

/-! Reviewer negative probe: widen the main statement's radius guard from
`r < 1 / 2` to `r < 3 / 4`.  The existing proof must not inhabit this type. -/
noncomputable section
namespace NSFormalization.Section3.T17.Rev453
open Set Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff

def widenedRadiusStatement : Prop :=
  ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (place : PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ),
    0 < ν → 0 < r → r < 3 / 4 → 0 < δ → IsPeriodicOn univ v → ContDiff ℝ ∞ v →
    (∀ t ∈ Ioo (0 : ℝ) (place.T + δ), ∀ x ∈ ball place.x₀ r,
      spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t, x)) ⊆ K) →
    ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius →
    ∃ D : CutoffData, LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧
      Nonempty (CorrectionAPI ν place v r δ D)

example : widenedRadiusStatement := by
  intro ν u p f K place v r δ hν hr hr34 hδ hper hv hdiv hsupp hball
  exact correctionStatementAmended_holds ν u p f K place v r δ
    hν hr hr34 hδ hper hv hdiv hsupp hball

end NSFormalization.Section3.T17.Rev453
