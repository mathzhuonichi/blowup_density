import NSFormalization.Source.PacketEnergy
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Pressure normalization on the initial quiet interval

The conclusions use the actual PDE and compact spatial support of pressure.
-/
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace NSFormalization.Source.PacketPressure
open NavierStokes.ProblemStatement

/-- A smooth compact pressure with zero physical spatial gradient is zero,
not merely spatially constant. -/
theorem compact_pressure_eq_zero {p : PressureField} {t : ℝ}
    (hp : Differentiable ℝ (fun x : Space => p (t, x)))
    (hcp : HasCompactSupport (fun x : Space => p (t, x)))
    (hg : ∀ x, pressureGradient p t x = 0) : ∀ x, p (t, x) = 0 := by
  have hd (x : Space) : fderiv ℝ (fun y => p (t, y)) x = 0 := by
    ext w
    have h := NavierStokes.PeriodicUniqueness.inner_pressureGradient p t x w
    rw [hg x, inner_zero_right] at h
    exact h.symm
  obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem _).mp hcp.isCompact.ne_univ
  intro x
  rw [is_const_of_fderiv_eq_zero hp hd x y]
  exact image_eq_zero_of_notMem_tsupport (f := fun x : Space => p (t, x)) hy

/-- A velocity which vanishes on an open time interval has zero physical
residual there except for its pressure gradient, at every viscosity. -/
theorem residual_eq_pressure_on_quiet_interval {a b ν t : ℝ}
    {u : VelocityField} {p : PressureField} (ht : t ∈ Ioo a b)
    (hu : ∀ s ∈ Ioo a b, ∀ x, u (s, x) = 0) (x : Space) :
    NSFormalization.Source.residual ν u p t x = pressureGradient p t x := by
  have hs : (fun y : Space => u (t, y)) = fun _ => 0 := funext (hu t ht)
  have htzero : (fun s : ℝ => u (s, x)) =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hu s hs x
  have htime : temporalDerivative u t x = 0 := by
    unfold temporalDerivative
    rw [htzero.fderiv_eq]
    simp
  have hspace (y : Space) : spatialDerivative u t y = 0 := by
    unfold spatialDerivative
    rw [hs]
    simp
  have hlap : spatialLaplacian u t x = 0 := by
    simp [spatialLaplacian, hspace]
  simp [NSFormalization.Source.residual, htime, advection, hspace, hlap]

/-- From a zero velocity and forcing on an initial open interval, the actual
PDE and compact pressure normalization imply pointwise zero pressure. -/
theorem pressure_vanishes_on_quiet_interval {a b ν : ℝ}
    {u f : VelocityField} {p : PressureField}
    (hu : ∀ t ∈ Ioo a b, ∀ x, u (t, x) = 0)
    (hf : ∀ t ∈ Ioo a b, ∀ x, f (t, x) = 0)
    (hp : ∀ t ∈ Ioo a b, Differentiable ℝ (fun x : Space => p (t, x)))
    (hcp : ∀ t ∈ Ioo a b, HasCompactSupport (fun x : Space => p (t, x)))
    (hNS : ∀ t ∈ Ioo a b, ∀ x,
      NSFormalization.Source.residual ν u p t x = f (t, x)) :
    ∀ t ∈ Ioo a b, ∀ x, p (t, x) = 0 := by
  intro t ht
  apply compact_pressure_eq_zero (hp t ht) (hcp t ht)
  intro x
  have h := hNS t ht x
  rwa [residual_eq_pressure_on_quiet_interval ht hu x, hf t ht x] at h

end NSFormalization.Source.PacketPressure
