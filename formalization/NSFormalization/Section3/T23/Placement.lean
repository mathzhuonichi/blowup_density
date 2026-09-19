import NSFormalization.Section3.T15.Scaling

/-!
# T23 U1: cube-free placement in a prescribed interior ball

This module restates the sixteen fields of `DomainPlacementData` from
`research/T23/Spec.lean:374-450` over the raw packet fields permitted inside
`formalization/`.  Unlike the torus placement used by T15, it contains no
fundamental-cube condition: the prescribed ball is related directly to the
domain by `interiorBall_in_domain` below.
-/

noncomputable section

namespace NSFormalization.Section3.T23

open Set
open NavierStokes.ProblemStatement

/-- Cube-free interior placement data, adapted from the T15 torus placement by
removing its fundamental-cube field.  The raw arguments `u`, `p`, `f`, and `K`
are the local spelling of the packet velocity, pressure, force, and carrier. -/
structure DomainPlacementData (u : VelocityField) (p : PressureField)
    (f : VelocityField) (K : Set Space) where
  /-- `03-torus.tex:103-106`: the target singular time `T`. -/
  T : ℝ
  /-- `03-torus.tex:103-106`: `0<T`. -/
  time_pos : 0 < T
  /-- `03-torus.tex:102-105`: center of the fixed localization ball `B`. -/
  chartCenter : Space
  /-- `03-torus.tex:102-105`: radius of the fixed localization ball `B`. -/
  chartRadius : ℝ
  /-- `03-torus.tex:102`: `B` has positive radius. -/
  chartRadius_pos : 0 < chartRadius
  /-- `03-torus.tex:102,105`: the placement center `x₀∈B`. -/
  x₀ : Space
  /-- `03-torus.tex:102`: `x₀∈B`. -/
  x₀_mem : x₀ ∈ Metric.ball chartCenter chartRadius
  /-- `03-torus.tex:101-102`: the compact spatial set `K_*` enlarged to cover
  both the velocity/pressure carrier and the spatial projection of `supp F`. -/
  Kstar : Set Space
  /-- `03-torus.tex:101`: `K_*` is compact. -/
  Kstar_compact : IsCompact Kstar
  /-- `03-torus.tex:101`: `K⊆K_*`, where `K` is the packet carrier. -/
  carrier_subset : K ⊆ Kstar
  /-- `03-torus.tex:101-102`: the spatial projection of `supp F` is in `K_*`. -/
  force_projection_subset : ∀ t : ℝ, ∀ x : Space,
    (t, x) ∈ tsupport f → x ∈ Kstar
  /-- `03-torus.tex:103`: one positive threshold for all sufficiently small
  scales. -/
  ε₀ : ℝ
  /-- `03-torus.tex:103`: `ε₀>0`. -/
  eps_pos : 0 < ε₀
  /-- `03-torus.tex:103`, harmless normalization after shrinking: `ε₀≤1`. -/
  eps_le_one : ε₀ ≤ 1
  /-- `03-torus.tex:104-106`: `2ε²<T`, before `t_ε` is defined. -/
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < T
  /-- `03-torus.tex:104-105`: `x₀+εK_*⊆B`. -/
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ y ∈ Kstar,
    x₀ + ε • y ∈ Metric.ball chartCenter chartRadius

/-! ## The canonical compact enlargement -/

/-- `03-torus.tex:101-102`: enlarge the packet carrier by the spatial
projection of the spacetime support of its force. -/
def domainPlacementCarrier (K : Set Space) (f : VelocityField) : Set Space :=
  K ∪ Prod.snd '' tsupport f

/-- The canonical enlargement is compact when both raw packet supports are
compact. -/
theorem domainPlacementCarrier_compact {K : Set Space} {f : VelocityField}
    (hK : IsCompact K) (hf : HasCompactSupport f) :
    IsCompact (domainPlacementCarrier K f) :=
  hK.union (hf.image continuous_snd)

/-- A positive radius bounds every point of the canonical compact
enlargement. -/
theorem domainPlacementCarrier_bound {K : Set Space} {f : VelocityField}
    (hK : IsCompact K) (hf : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∀ y ∈ domainPlacementCarrier K f, ‖y‖ ≤ R :=
  (domainPlacementCarrier_compact hK hf).isBounded.exists_pos_norm_le

/-- A fixed positive bound for the canonical compact enlargement. -/
def domainPlacementRadius {K : Set Space} {f : VelocityField}
    (hK : IsCompact K) (hf : HasCompactSupport f) : ℝ :=
  Classical.choose (domainPlacementCarrier_bound hK hf)

/-- The chosen carrier radius is strictly positive. -/
theorem domainPlacementRadius_pos {K : Set Space} {f : VelocityField}
    (hK : IsCompact K) (hf : HasCompactSupport f) :
    0 < domainPlacementRadius hK hf :=
  (Classical.choose_spec (domainPlacementCarrier_bound hK hf)).1

/-- Every point in the canonical enlargement is bounded by the chosen
radius. -/
theorem norm_le_domainPlacementRadius {K : Set Space} {f : VelocityField}
    (hK : IsCompact K) (hf : HasCompactSupport f) {y : Space}
    (hy : y ∈ domainPlacementCarrier K f) :
    ‖y‖ ≤ domainPlacementRadius hK hf :=
  (Classical.choose_spec (domainPlacementCarrier_bound hK hf)).2 y hy

/-! ## Interior margin and the common threshold -/

/-- The distance from `x₀` to the boundary radius of the prescribed ball. -/
def domainPlacementMargin (chartCenter x₀ : Space) (chartRadius : ℝ) : ℝ :=
  chartRadius - dist x₀ chartCenter

/-- Membership of `x₀` in the prescribed open ball gives a strictly
positive radial margin. -/
theorem domainPlacementMargin_pos {chartCenter x₀ : Space} {chartRadius : ℝ}
    (hx₀ : x₀ ∈ Metric.ball chartCenter chartRadius) :
    0 < domainPlacementMargin chartCenter x₀ chartRadius := by
  rw [domainPlacementMargin, sub_pos]
  exact Metric.mem_ball.mp hx₀

/-- One threshold simultaneously enforces normalization, strict time
smallness, and strict containment in the prescribed ball.  The last factor
keeps a half-margin at the closed upper endpoint. -/
def domainPlacementThreshold {K : Set Space} {f : VelocityField}
    (hK : IsCompact K) (hf : HasCompactSupport f) (T : ℝ)
    (chartCenter x₀ : Space) (chartRadius : ℝ) : ℝ :=
  min (min (1 / 2) (T / 4))
    (domainPlacementMargin chartCenter x₀ chartRadius /
      (2 * (domainPlacementRadius hK hf + 1)))

/-- The common threshold is positive. -/
theorem domainPlacementThreshold_pos {K : Set Space} {f : VelocityField}
    (hK : IsCompact K) (hf : HasCompactSupport f) {T chartRadius : ℝ}
    {chartCenter x₀ : Space} (hT : 0 < T)
    (hx₀ : x₀ ∈ Metric.ball chartCenter chartRadius) :
    0 < domainPlacementThreshold hK hf T chartCenter x₀ chartRadius := by
  unfold domainPlacementThreshold
  exact lt_min (lt_min (by norm_num) (by positivity))
    (div_pos (domainPlacementMargin_pos hx₀) (by
      have := domainPlacementRadius_pos hK hf
      positivity))

/-- The common threshold has the harmless normalization `ε₀ ≤ 1`. -/
theorem domainPlacementThreshold_le_one {K : Set Space} {f : VelocityField}
    (hK : IsCompact K) (hf : HasCompactSupport f) (T : ℝ)
    (chartCenter x₀ : Space) (chartRadius : ℝ) :
    domainPlacementThreshold hK hf T chartCenter x₀ chartRadius ≤ 1 :=
  (min_le_left _ _).trans ((min_le_left _ _).trans (by norm_num))

/-- Every admissible scale satisfies the strict temporal placement
inequality, including at the closed upper endpoint. -/
theorem domainPlacementThreshold_time {K : Set Space} {f : VelocityField}
    (hK : IsCompact K) (hf : HasCompactSupport f) {T : ℝ}
    (hT : 0 < T) (chartCenter x₀ : Space) (chartRadius : ℝ) :
    ∀ ε ∈ Ioc (0 : ℝ)
      (domainPlacementThreshold hK hf T chartCenter x₀ chartRadius),
      2 * ε ^ 2 < T := by
  intro ε hε
  have he : ε ≤ 1 / 2 :=
    hε.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have ht : ε ≤ T / 4 :=
    hε.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  nlinarith [mul_nonneg hε.1.le (sub_nonneg.mpr he)]

end NSFormalization.Section3.T23
