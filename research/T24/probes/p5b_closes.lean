import NSFormalization.Section3.T24.MultipleOmegaRegions

noncomputable section
namespace NSFormalization.Section3.T24.OmegaRegions.Probe
open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T15
variable {N : ℕ} {T : ℝ} {c : Fin N → Space} {r : Fin N → ℝ}
  {w : Fin N → VelocityField}
  (hd : Pairwise (fun i j : Fin N =>
    Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j))))
  (hs : ∀ j, ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
    x ∉ Metric.ball (c j) (r j) → w j (t, x) = 0)
include hd hs

theorem agreement : ∀ j, ∀ t ∈ Ico (0 : ℝ) T,
    ∀ x ∈ Metric.ball (c j) (r j), assembledVelocity w (t, x) = w j (t, x) := by
  exact region_agreement hd hs

theorem blowup {u : VelocityField} {x₀ : Fin N → Space} {ε : Fin N → ℝ}
    (hp : ∀ j, w j = scaledVelocity u (x₀ j) T (ε j))
    (he : ∀ j, 0 < ε j) (ht : ∀ j, ε j ^ 2 < T)
    (hb : SpeedUnboundedAtOne u) :
    ∀ j, SpeedUnboundedAtOn T (Metric.ball (c j) (r j)) (assembledVelocity w) := by
  exact region_blowup hd hs hp he ht hb
end NSFormalization.Section3.T24.OmegaRegions.Probe
