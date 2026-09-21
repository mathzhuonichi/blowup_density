import NSFormalization.Section3.T15.Assembly

/-! Theorem 3.6 (`03-torus.tex:199`): "Fix any nonempty coordinate ball."
The compact-carrier construction of T24, factored for one prescribed chart. -/
noncomputable section
namespace NSFormalization.Section3.T15
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13
variable {u f : VelocityField} {p : PressureField} {K : Set Space}
  (center : Space) (radius : ℝ) (hρ : 0 < radius)
  (hcube : closure (Metric.ball center radius) ⊆ interior fundamentalCube)
  (hK : IsCompact K) (hf : HasCompactSupport f) (T : ℝ) (hT : 0 < T)

def placementDataAt : PlacementData u p f K where
  T := T
  time_pos := hT
  chartCenter := center
  chartRadius := radius
  chartRadius_pos := hρ
  chartBall_in_cube := hcube
  x₀ := center
  x₀_mem := Metric.mem_ball_self (hρ)
  Kstar := placementCarrier K f
  Kstar_compact := placementCarrier_compact hK hf
  carrier_subset := subset_union_left
  force_projection_subset := fun t x hx => Or.inr ⟨(t, x), hx, rfl⟩
  ε₀ := min (min (1 / 2) (T / 4))
    (radius / (2 * (placementRadius hK hf + 1)))
  eps_pos := by
    have := placementRadius_pos hK hf
    have := hρ
    have := hT
    positivity
  eps_le_one := (min_le_left _ _).trans ((min_le_left _ _).trans (by norm_num))
  eps_time := by
    intro ε hε
    have he : ε ≤ 1 / 2 := hε.2.trans ((min_le_left _ _).trans (min_le_left _ _))
    have ht : ε ≤ T / 4 := hε.2.trans ((min_le_left _ _).trans (min_le_right _ _))
    nlinarith [hε.1, mul_nonneg hε.1.le (sub_nonneg.mpr he)]
  eps_space := by
    intro ε hε y hy
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hε.1]
    have hR := placementRadius_pos hK hf
    have hden : 0 < 2 * (placementRadius hK hf + 1) := by positivity
    have he := (le_div_iff₀ hden).mp (hε.2.trans (min_le_right _ _))
    have hn := mul_le_mul_of_nonneg_left
      (placement_norm_le_radius hK hf hy) hε.1.le
    have hr := hρ
    nlinarith

theorem placementDataAt_T :
    (placementDataAt (u := u) (p := p) center radius hρ hcube hK hf T hT).T = T := rfl

theorem placementDataAt_chartCenter :
    (placementDataAt (u := u) (p := p) center radius hρ hcube hK hf T hT).chartCenter = center := rfl

theorem placementDataAt_chartRadius :
    (placementDataAt (u := u) (p := p) center radius hρ hcube hK hf T hT).chartRadius = radius := rfl

theorem placementDataAt_x₀ :
    (placementDataAt (u := u) (p := p) center radius hρ hcube hK hf T hT).x₀ = center := rfl

end NSFormalization.Section3.T15
