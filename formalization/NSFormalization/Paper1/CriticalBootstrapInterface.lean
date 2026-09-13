import NSFormalization.Paper1.ScalarEnergy

/-!
# Scalar critical bootstrap interface

This module packages exactly the real-variable hypotheses consumed by
`critical_norm_bound`.  It deliberately contains no PDE objects (`Flow`,
pressure, or lifespan), so constructing a value is an explicit obligation for
a later analytic bridge.
-/
noncomputable section
namespace NSFormalization.Paper1

open Set

/-- Data for the scalar critical bootstrap on a finite interval. -/
structure CriticalBootstrapData (ν T C K ρ : ℝ) where
  y : ℝ → ℝ
  E' : ℝ → ℝ
  z : ℝ → ℝ
  b : ℝ → ℝ
  N : ℝ → ℝ
  hν : 0 ≤ ν
  hC : 0 ≤ C
  hρ0 : 0 ≤ ρ
  hρK : ρ < K
  hK : C * K ≤ ν / 2
  hy : Continuous y
  hy0 : y 0 = 0
  hynonneg : ∀ t ∈ Icc 0 T, 0 ≤ y t
  hN : ContinuousOn N (Icc 0 T)
  hN0 : N 0 = 0
  hNbound : ∀ t ∈ Icc 0 T, N t ≤ ρ
  hb : ∀ t ∈ Ioo 0 T, 0 ≤ b t
  hdE : ∀ t ∈ Ioo 0 T, HasDerivAt (fun x => (y x) ^ 2) (E' t) t
  hdN : ∀ t ∈ Ioo 0 T, HasDerivAt N (b t) t
  henergy : ∀ t ∈ Ioo 0 T,
    E' t / 2 + (ν - C * y t) * (z t) ^ 2 ≤ b t * y t

/-- The scalar critical bound supplied by a bootstrap certificate. -/
theorem CriticalBootstrapData.bound
    {ν T C K ρ : ℝ} (D : CriticalBootstrapData ν T C K ρ) :
    ∀ t ∈ Icc 0 T, D.y t ≤ ρ := by
  exact critical_norm_bound D.hν D.hC D.hρ0 D.hρK D.hK D.hy D.hy0
    D.hynonneg D.hN D.hN0 D.hNbound D.hb D.hdE D.hdN D.henergy

end NSFormalization.Paper1
