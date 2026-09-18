import NSFormalization.Section3.T17.Transport

open Set Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 (IsPeriodicOn)
open NSFormalization.Section3.T16 (latticeLift)
open NSFormalization.Section3.T17
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Paper1.CorrectionProfile (physicalCorrection)
open scoped ContDiff

noncomputable section

-- Deliberate substantive mutation: the sign of the transported force is flipped.
example {ν : ℝ} {v : SpaceTimeField} {x₀ : Space} {T δ r : ℝ} {θ : Space → ℝ}
    {η : ℝ → ℝ} {O : Set Space} {θR ε₀ ε : ℝ}
    (hv : IsPeriodicOn univ v)
    (hvsm : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r))
    (hθsm : ContDiff ℝ ∞ θ) (hηsm : ContDiff ℝ ∞ η)
    (hθcs : HasCompactSupport θ) (hηcs : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hε : 0 < ε) (hεspace : ε * θR < r)
    (hεtime : 2 * ε ^ 2 < min T δ) :
    correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε
      = -latticeLift (NSFormalization.Source.correctionForce ν v
          (physicalCorrection v x₀ T θ η ε)) := by
  exact force_eq (ν := ν) (v := v) (x₀ := x₀) (T := T) (δ := δ) (r := r)
    (θ := θ) (η := η) (O := O) (θR := θR) (ε₀ := ε₀) (ε := ε)
    hv hvsm hθsm hηsm hθcs hηcs hθsupp hηsupp hr2 hε hεspace hεtime

end
