import NSFormalization.Section3.T15.Bridges

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

/-- Cube-free interior placement data, **adapted from** the T15 torus
`PlacementData` (`research/T18/Spec.lean:454-548`) by **removing**
`chartBall_in_cube` (the torus artifact `closure(ball …) ⊆ interior
fundamentalCube`) and never referencing `fundamentalCube`; every other field is
kept verbatim.  On a bounded domain `Ω ⊂ R³` there is no torus, so the ball's
placement is fixed by the free center `chartCenter`/`x₀` and its interior
containment is a field of the API (`interiorBall_in_domain`), not of the
placement.  `Kstar` still contains both spatial packet supports.  The raw
arguments `u`, `p`, `f`, and `K` are the local spelling of the packet velocity,
pressure, force, and carrier permitted inside `formalization/`.

Non-vacuity: the fields below constrain actual real data (a positive time,
a positive-radius metric ball, a compact `Kstar` carrying the packet and force
supports, a positive threshold with genuine scale conditions); nothing is
`True`. -/
structure DomainPlacementData (u : VelocityField) (p : PressureField)
    (f : VelocityField) (K : Set Space) where
  /-- `03-torus.tex:103-106`: the target singular time `T`.

  Non-vacuity: positivity makes `(0,T)` a genuine evolution interval. -/
  T : ℝ
  /-- `03-torus.tex:103-106`: `0<T`.

  Non-vacuity: this rules out the empty or reversed time interval. -/
  time_pos : 0 < T
  /-- `03-torus.tex:102-105`: center of the fixed localization ball `B`.

  Non-vacuity: it is used in the concrete ball containment below. -/
  chartCenter : Space
  /-- `03-torus.tex:102-105`: radius of the fixed localization ball `B`.

  Non-vacuity: the next field requires this radius to be positive. -/
  chartRadius : ℝ
  /-- `03-torus.tex:102`: `B` has positive radius.

  Non-vacuity: this excludes an empty metric ball. -/
  chartRadius_pos : 0 < chartRadius
  /-- `03-torus.tex:102,105`: the placement center `x₀∈B`.

  Non-vacuity: the point is tied to the same concrete chart ball. -/
  x₀ : Space
  /-- `03-torus.tex:102`: `x₀∈B`.

  Non-vacuity: this is membership in the explicit ball above. -/
  x₀_mem : x₀ ∈ Metric.ball chartCenter chartRadius
  /-- `03-torus.tex:101-102`: the compact spatial set `K_*` enlarged to cover
  both the velocity/pressure carrier and the spatial projection of `supp F`.

  Non-vacuity: the following three fields constrain this actual set. -/
  Kstar : Set Space
  /-- `03-torus.tex:101`: `K_*` is compact.

  Non-vacuity: this is an assertion about the carried set, not an existential
  choice made separately for each scale. -/
  Kstar_compact : IsCompact Kstar
  /-- `03-torus.tex:101`: `K⊆K_*`, where `K` is T14's packet carrier.

  Exact quantifier order: every point of `K` lies in the fixed
  `Kstar`.  Non-vacuity: this links placement to the selected packet. -/
  carrier_subset : K ⊆ Kstar
  /-- `03-torus.tex:101-102`: the spatial projection of `supp F` is in `K_*`.

  Exact quantifier order: for every spacetime support point `(t,x)`, its
  spatial coordinate lies in `Kstar`.  Non-vacuity: this rules out choosing a
  set that only covers the velocity carrier. -/
  force_projection_subset : ∀ t : ℝ, ∀ x : Space,
    (t, x) ∈ tsupport f → x ∈ Kstar
  /-- `03-torus.tex:103`: one positive threshold for all sufficiently small
  scales.

  Non-vacuity: every conclusion below uses the same interval `(0,ε₀]`. -/
  ε₀ : ℝ
  /-- `03-torus.tex:103`: `ε₀>0`.

  Non-vacuity: `(0,ε₀]` contains admissible scales. -/
  eps_pos : 0 < ε₀
  /-- `03-torus.tex:103`, harmless normalization after shrinking: `ε₀≤1`.

  Non-vacuity: this is a quantitative restriction on the one threshold. -/
  eps_le_one : ε₀ ≤ 1
  /-- `03-torus.tex:104-106`: `2ε²<T`, before `t_ε` is defined.

  Exact quantifier order: first `ε∈(0,ε₀]`, then the inequality.
  Non-vacuity: it gives `t_ε>0`, so positive-time force norms contain the
  complete rescaled temporal support. -/
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < T
  /-- `03-torus.tex:104-105`: `x₀+εK_*⊆B`.

  Exact quantifier order: first `ε∈(0,ε₀]`, then every `y∈Kstar`.
  Non-vacuity: together with `interiorBall_in_domain`, this is precisely the
  support-versus-scale condition used by the single-copy conclusions. -/
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

/-- Every scaled translate of the canonical carrier remains strictly inside
the prescribed ball, including at the closed upper endpoint. -/
theorem domainPlacementThreshold_space {K : Set Space} {f : VelocityField}
    (hK : IsCompact K) (hf : HasCompactSupport f)
    {T chartRadius : ℝ} {chartCenter x₀ : Space} :
    ∀ ε ∈ Ioc (0 : ℝ)
        (domainPlacementThreshold hK hf T chartCenter x₀ chartRadius),
      ∀ y ∈ domainPlacementCarrier K f,
        x₀ + ε • y ∈ Metric.ball chartCenter chartRadius := by
  intro ε hε y hy
  have hR : 0 < domainPlacementRadius hK hf :=
    domainPlacementRadius_pos hK hf
  have hden : 0 < 2 * (domainPlacementRadius hK hf + 1) := by
    positivity
  have he :
      ε * (2 * (domainPlacementRadius hK hf + 1)) ≤
        domainPlacementMargin chartCenter x₀ chartRadius :=
    (le_div_iff₀ hden).mp
      (hε.2.trans (min_le_right _ _))
  have hn : ε * ‖y‖ ≤ ε * domainPlacementRadius hK hf :=
    mul_le_mul_of_nonneg_left (norm_le_domainPlacementRadius hK hf hy) hε.1.le
  have hfactor : domainPlacementRadius hK hf <
      2 * (domainPlacementRadius hK hf + 1) := by
    linarith
  have hstrict : ε * domainPlacementRadius hK hf <
      ε * (2 * (domainPlacementRadius hK hf + 1)) :=
    mul_lt_mul_of_pos_left hfactor hε.1
  have hsmall : ε * ‖y‖ < domainPlacementMargin chartCenter x₀ chartRadius := by
    exact hn.trans_lt (hstrict.trans_le he)
  rw [Metric.mem_ball, dist_eq_norm]
  have heq : x₀ + ε • y - chartCenter = (x₀ - chartCenter) + ε • y := by
    abel
  rw [heq]
  calc
    ‖(x₀ - chartCenter) + ε • y‖ ≤
        ‖x₀ - chartCenter‖ + ‖ε • y‖ := norm_add_le _ _
    _ = dist x₀ chartCenter + ε * ‖y‖ := by
      rw [dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hε.1]
    _ < chartRadius := by
      rw [domainPlacementMargin] at hsmall
      linarith

/-! ## The sixteen-field constructor -/

/-- The canonical cube-free placement for any prescribed interior ball and
any point `x₀` in that ball.  The domain hypothesis is threaded here so the
same arguments immediately furnish `interiorBall_in_domain`; no origin or
fundamental cube is chosen. -/
def domainPlacementData {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K Ω : Set Space}
    (hK : IsCompact K) (hf : HasCompactSupport f)
    (chartCenter : Space) (chartRadius : ℝ) (hchartRadius : 0 < chartRadius)
    (hball : closure (Metric.ball chartCenter chartRadius) ⊆ Ω)
    (x₀ : Space) (hx₀ : x₀ ∈ Metric.ball chartCenter chartRadius)
    (T : ℝ) (hT : 0 < T) : DomainPlacementData u p f K where
  T := T
  time_pos := hT
  chartCenter := chartCenter
  chartRadius := chartRadius
  chartRadius_pos := hchartRadius
  x₀ := x₀
  x₀_mem := hx₀
  Kstar := domainPlacementCarrier K f
  Kstar_compact := domainPlacementCarrier_compact hK hf
  carrier_subset := subset_union_left
  force_projection_subset := fun t x hx => Or.inr ⟨(t, x), hx, rfl⟩
  ε₀ := domainPlacementThreshold hK hf T chartCenter x₀ chartRadius
  eps_pos := domainPlacementThreshold_pos hK hf hT hx₀
  eps_le_one := domainPlacementThreshold_le_one hK hf T chartCenter x₀ chartRadius
  eps_time := domainPlacementThreshold_time hK hf hT chartCenter x₀ chartRadius
  eps_space := by
    have _hball := hball
    exact domainPlacementThreshold_space hK hf

/-- The prescribed horizon is preserved definitionally. -/
theorem domainPlacementData_time {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K Ω : Set Space}
    (hK : IsCompact K) (hf : HasCompactSupport f)
    (chartCenter : Space) (chartRadius : ℝ) (hchartRadius : 0 < chartRadius)
    (hball : closure (Metric.ball chartCenter chartRadius) ⊆ Ω)
    (x₀ : Space) (hx₀ : x₀ ∈ Metric.ball chartCenter chartRadius)
    (T : ℝ) (hT : 0 < T) :
    (domainPlacementData (u := u) (p := p) hK hf chartCenter chartRadius
      hchartRadius hball x₀ hx₀ T hT).T = T := rfl

/-- The prescribed chart center is preserved definitionally. -/
theorem domainPlacementData_chartCenter {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K Ω : Set Space}
    (hK : IsCompact K) (hf : HasCompactSupport f)
    (chartCenter : Space) (chartRadius : ℝ) (hchartRadius : 0 < chartRadius)
    (hball : closure (Metric.ball chartCenter chartRadius) ⊆ Ω)
    (x₀ : Space) (hx₀ : x₀ ∈ Metric.ball chartCenter chartRadius)
    (T : ℝ) (hT : 0 < T) :
    (domainPlacementData (u := u) (p := p) hK hf chartCenter chartRadius
      hchartRadius hball x₀ hx₀ T hT).chartCenter = chartCenter := rfl

/-- The prescribed chart radius is preserved definitionally. -/
theorem domainPlacementData_chartRadius {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K Ω : Set Space}
    (hK : IsCompact K) (hf : HasCompactSupport f)
    (chartCenter : Space) (chartRadius : ℝ) (hchartRadius : 0 < chartRadius)
    (hball : closure (Metric.ball chartCenter chartRadius) ⊆ Ω)
    (x₀ : Space) (hx₀ : x₀ ∈ Metric.ball chartCenter chartRadius)
    (T : ℝ) (hT : 0 < T) :
    (domainPlacementData (u := u) (p := p) hK hf chartCenter chartRadius
      hchartRadius hball x₀ hx₀ T hT).chartRadius = chartRadius := rfl

/-- The prescribed placement point is preserved definitionally. -/
theorem domainPlacementData_x₀ {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K Ω : Set Space}
    (hK : IsCompact K) (hf : HasCompactSupport f)
    (chartCenter : Space) (chartRadius : ℝ) (hchartRadius : 0 < chartRadius)
    (hball : closure (Metric.ball chartCenter chartRadius) ⊆ Ω)
    (x₀ : Space) (hx₀ : x₀ ∈ Metric.ball chartCenter chartRadius)
    (T : ℝ) (hT : 0 < T) :
    (domainPlacementData (u := u) (p := p) hK hf chartCenter chartRadius
      hchartRadius hball x₀ hx₀ T hT).x₀ = x₀ := rfl

/-- `03-torus.tex:646,653-654`: the fixed localization ball of the canonical
placement is the prescribed interior ball.  This is the exact geometry field
used by `BoundaryInsertionAPI`, with no fundamental-cube side condition. -/
theorem interiorBall_in_domain {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K Ω : Set Space}
    (hK : IsCompact K) (hf : HasCompactSupport f)
    (chartCenter : Space) (chartRadius : ℝ) (hchartRadius : 0 < chartRadius)
    (hball : closure (Metric.ball chartCenter chartRadius) ⊆ Ω)
    (x₀ : Space) (hx₀ : x₀ ∈ Metric.ball chartCenter chartRadius)
    (T : ℝ) (hT : 0 < T) :
    closure (Metric.ball
      (domainPlacementData (u := u) (p := p) hK hf chartCenter chartRadius
        hchartRadius hball x₀ hx₀ T hT).chartCenter
      (domainPlacementData (u := u) (p := p) hK hf chartCenter chartRadius
        hchartRadius hball x₀ hx₀ T hT).chartRadius) ⊆ Ω :=
  hball

end NSFormalization.Section3.T23
