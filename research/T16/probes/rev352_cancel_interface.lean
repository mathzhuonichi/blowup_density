import NSFormalization.Section3.T16.LatticeLift

open Set Filter Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T16
open NSFormalization.Section3.T10 (IsPeriodicOn)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Paper1.CorrectionProfile (spatialCutoff temporalCutoff)
open scoped ContDiff Topology

noncomputable section

/- Interface check (resolved).  The chart-removal lemma
   `NSFormalization.Paper1.exists_local_background_removal` gives eventual
   cancellation in every neighborhood, `∀ x ∈ O, ∀ᶠ y in 𝓝 x, v + w = 0`, not
   the pointwise hypothesis consumed by `correction_fields_of_chart`.  Lane 352
   now supplies the bridge `cancel_of_eventually`, so the eventual output is
   accepted; the earlier type error is gone. -/
example {v w : SpaceTimeField} {O : Set Space} {t : ℝ}
    (hzero : ∀ x ∈ O, ∀ᶠ y in 𝓝 x, v (t, y) + w (t, y) = 0) :
    ∀ x ∈ O, v (t, x) + w (t, x) = 0 :=
  cancel_of_eventually hzero

/- And the packaged theorem now accepts the eventual cancellation form directly,
   through `correction_fields_of_chart'`. -/
example (v U : SpaceTimeField) (x₀ : Space) (θ : Space → ℝ) (η : ℝ → ℝ)
    (A : SpaceTimeField) (r T ε₀ θRadius : ℝ) (W : ℝ → SpaceTimeField)
    (hr2 : r < 1 / 2) (hv_per : IsPeriodicOn univ v)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θRadius < r)
    (hWsmooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ContDiff ℝ ∞ (W ε))
    (hWcompact : ∀ ε ∈ Ioc (0 : ℝ) ε₀, HasCompactSupport (W ε))
    (hWdiv : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t x, spatialDivergence (W ε) t x = 0)
    (hWtsupp : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      tsupport (W ε) ⊆ Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ ball x₀ (ε * θRadius))
    (hWformula : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t, ∀ x ∈ ball x₀ r,
      W ε (t, x) = -SpatialCurl.curl (fun y =>
        (temporalCutoff η T ε t * spatialCutoff θ x₀ ε y) • A (t, y)) x)
    (hWcancelEv : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ico (T - ε ^ 2) T,
      ∃ O : Set Space, IsOpen O ∧ O ⊆ ball x₀ r ∧
        tsupport (fun x => periodicScaledPacket U x₀ T ε (t, x)) ⊆ periodicSet O ∧
        ∀ x ∈ O, ∀ᶠ y in 𝓝 x, v (t, y) + W ε (t, y) = 0) :
    ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ico (T - ε ^ 2) T,
      ∃ O : Set Space, IsOpen O ∧
        tsupport (fun x => periodicScaledPacket U x₀ T ε (t, x)) ⊆ O ∧
        ∀ x ∈ O, correctedBackground v (fun ε => latticeLift (W ε)) ε (t, x) = 0 :=
  (correction_fields_of_chart' v U x₀ θ η A r T ε₀ θRadius W hr2 hv_per
    hεspace hWsmooth hWcompact hWdiv hWtsupp hWformula hWcancelEv).2.2.2.2.2.2
