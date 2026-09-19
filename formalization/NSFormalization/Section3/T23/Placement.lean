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

end NSFormalization.Section3.T23
