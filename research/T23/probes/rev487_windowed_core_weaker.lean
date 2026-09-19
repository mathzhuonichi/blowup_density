import NSFormalization.Section3.T23.LocalCorrection

/-! Review probe: the U3 operational core is invariant under arbitrary changes
to the unused potential field, so it cannot hide a global potential identity. -/

namespace NSFormalization.Section3.T23

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff

def replacePotential (D : CutoffData) (A : SpaceTimeField) : CutoffData :=
  { θ := D.θ
    η := D.η
    plateau := D.plateau
    θRadius := D.θRadius
    ε₀ := D.ε₀
    potential := A
    correction := D.correction }

theorem WindowedCorrectionCore.replacePotential
    {v U : SpaceTimeField} {K : Set Space} {x₀ : Space}
    {r T δ : ℝ} {D : CutoffData}
    (h : WindowedCorrectionCore v U K x₀ r T δ D) (A : SpaceTimeField) :
    WindowedCorrectionCore v U K x₀ r T δ (replacePotential D A) where
  theta_radius_pos := by change 0 < D.θRadius; exact h.theta_radius_pos
  eps_time := by
    change ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, 2 * ε ^ 2 < min T δ
    exact h.eps_time
  eps_space := by
    change ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ε * D.θRadius < r
    exact h.eps_space
  correction_smooth := by
    change ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ContDiff ℝ ∞ (D.correction ε)
    exact h.correction_smooth
  correction_divergence_free := by
    change ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t x,
      spatialDivergence (D.correction ε) t x = 0
    exact h.correction_divergence_free
  correction_compactSupport := by
    change ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, HasCompactSupport (D.correction ε)
    exact h.correction_compactSupport
  correction_support := by
    change ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      tsupport (D.correction ε) ⊆
        Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ Metric.ball x₀ (ε * D.θRadius)
    exact h.correction_support
  correction_cancels := by
    change ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t ∈ Ico (T - ε ^ 2) T,
      ∃ O : Set Space, IsOpen O ∧ O ⊆ Metric.ball x₀ r ∧
        tsupport (fun x => NSFormalization.Section3.T15.scaledVelocity U x₀ T ε (t, x)) ⊆ O ∧
        ∀ x ∈ O, v (t, x) + D.correction ε (t, x) = 0
    exact h.correction_cancels
  crossTransport_background_advects_packet := by
    change ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDerivative (NSFormalization.Section3.T15.scaledVelocity U x₀ T ε) t x
        (NSFormalization.Section3.T16.correctedBackground v D.correction ε (t, x)) = 0
    exact h.crossTransport_background_advects_packet
  crossTransport_packet_advects_background := by
    change ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDerivative (NSFormalization.Section3.T16.correctedBackground v D.correction ε) t x
        (NSFormalization.Section3.T15.scaledVelocity U x₀ T ε (t, x)) = 0
    exact h.crossTransport_packet_advects_background

end NSFormalization.Section3.T23
