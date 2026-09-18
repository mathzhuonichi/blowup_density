import NSFormalization.Section3.T16.BallPotential

/-!
# Probe: `exists_potential_on_ball` fills the three T16 potential fields

Standalone check (`cd verification && lake env lean ../research/T16/probes/ball_potential_closes.lean`)
that lane 351's `exists_potential_on_ball` discharges exactly the canonical
`NSFormalization.Section3.T16.LocalPotentialAPI` fields
`potential_smooth`, `potential_formula`, `potential_curl` (their field types are
written out verbatim through the structure projection `D.potential`), plus a
non-vacuity instance for a nonzero smooth divergence-free reference.
-/

noncomputable section

namespace NSFormalization.Section3.T16.Probe

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement NavierStokes.SpatialCurl
open NSFormalization.Paper1.RadialPotential (cross timePotential centeredPotential_eq_integral)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T16
open scoped ContDiff Topology

/-- Lane 353's use site: choose `D.potential := timePotential v x₀` and close the
three potential fields of `LocalPotentialAPI` by `exact`.  The three goals below
are the field types of `potential_smooth`, `potential_formula`, `potential_curl`
copied verbatim, with the structure projection `D.potential` in place. -/
example (D : CutoffData) (v : SpaceTimeField) (x₀ : Space) (r T δ : ℝ)
    (hA : D.potential = timePotential v x₀)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
      spatialDivergence v t x = 0) :
    -- potential_smooth
    ContDiffOn ℝ ∞ D.potential (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r) ∧
    -- potential_formula
    (∀ t x, D.potential (t, x) =
      ∫ ρ in (0 : ℝ)..1, ρ • cross (v (t, x₀ + ρ • (x - x₀))) (x - x₀)) ∧
    -- potential_curl
    (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
      SpatialCurl.curl (fun y => D.potential (t, y)) x = v (t, x)) := by
  rw [hA]
  exact ⟨timePotential_contDiffOn_ball isOpen_Ioo hv,
    fun t x => centeredPotential_eq_integral (fun y => v (t, y)) x₀ x,
    fun t ht x hx => spatialCurl_timePotential_on_ball hv hdiv ht hx⟩

/-- Non-vacuity: the constant field `v ≡ e₀` is smooth and divergence free on the
unit ball, so `exists_potential_on_ball` produces a potential whose curl recovers
the (nonzero) reference. -/
example : ∃ A : SpaceTimeField,
    ContDiffOn ℝ ∞ A (Ioo (0 : ℝ) (1 + 0) ×ˢ Metric.ball (0 : Space) 1) ∧
    (∀ t x, A (t, x) =
      ∫ ρ in (0 : ℝ)..1, ρ • cross (coordinateVector 0) (x - 0)) ∧
    (∀ t ∈ Ioo (0 : ℝ) (1 + 0), ∀ x ∈ Metric.ball (0 : Space) 1,
      SpatialCurl.curl (fun y => A (t, y)) x = coordinateVector 0) :=
  exists_potential_on_ball (v := fun _ : SpaceTime => coordinateVector 0)
    (x₀ := (0 : Space)) (r := 1) (T := 1) (δ := 0) contDiffOn_const
    (fun t _ x _ => spatialDivergence_const_zero (coordinateVector 0) t x)

/-- The reference in the non-vacuity instance is genuinely nonzero. -/
example : (coordinateVector 0 : Space) ≠ 0 := by
  intro h
  have hc := congrArg (fun z : Space => z 0) h
  simp [coordinateVector] at hc

end NSFormalization.Section3.T16.Probe
