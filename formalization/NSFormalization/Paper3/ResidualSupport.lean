import NSFormalization.Source.Insertion
import Mathlib.Analysis.Calculus.FDeriv.Congr
import NSFormalization.Paper3.TimeObservations
import NavierStokes.PeriodicUniqueness

/-! Locality of the actual residual and its compact difference support. -/
noncomputable section
namespace NSFormalization.Paper3
open Set Filter NavierStokes NavierStokes.ProblemStatement
open scoped Topology ContDiff

/-- Equality of the temporal/spatial germs suffices for equality of the actual
residual; all first and second derivatives are handled explicitly. -/
theorem residual_eq_of_germs {u v : VelocityField} {p q : PressureField} (ν t : ℝ) (x : Space)
    (hT : (fun r => u (r, x)) =ᶠ[𝓝 t] (fun r => v (r, x)))
    (hX : (fun y => u (t, y)) =ᶠ[𝓝 x] (fun y => v (t, y)))
    (hP : (fun y => p (t, y)) =ᶠ[𝓝 x] (fun y => q (t, y))) :
    NSFormalization.Source.residual ν u p t x = NSFormalization.Source.residual ν v q t x := by
  have htime : temporalDerivative u t x = temporalDerivative v t x :=
    congrArg (fun L : ℝ →L[ℝ] Space => L 1) hT.fderiv_eq
  have hder : spatialDerivative u t x = spatialDerivative v t x := hX.fderiv_eq
  have hadv : advection u t x = advection v t x := by
    simp only [advection, hder, hX.eq_of_nhds]
  have hpressure : pressureGradient p t x = pressureGradient q t x := by
    unfold pressureGradient
    simp only [hP.fderiv_eq]
  have hlap : spatialLaplacian u t x = spatialLaplacian v t x := by
    unfold spatialLaplacian
    apply Finset.sum_congr rfl
    intro i _
    have heq : (fun y => spatialDerivative u t y (coordinateVector i)) =ᶠ[𝓝 x]
        (fun y => spatialDerivative v t y (coordinateVector i)) := by
      filter_upwards [hX.fderiv (𝕜 := ℝ)] with y hy
      exact congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector i)) hy
    exact congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector i)) heq.fderiv_eq
  simp only [NSFormalization.Source.residual, htime, hadv, hlap, hpressure]

/-- A common compact support for the velocity difference and a compact pressure
difference contain the actual forcing residual difference at interior times. -/
theorem support_residual_difference_subset {u v : VelocityField} {p q : PressureField}
    {a b t ν : ℝ} {K : Set Space} (hK : IsClosed K)
    (hsupp : ∀ r ∈ Icc a b, ∀ x ∉ K, (u - v) (r, x) = 0)
    (hpressure : ∀ x ∉ K, (p - q) (t, x) = 0) (ht : t ∈ Ioo a b) :
    Function.support (fun x => NSFormalization.Source.residual ν u p t x -
      NSFormalization.Source.residual ν v q t x) ⊆ K := by
  intro x hx
  by_contra hxK
  have hT : (fun r => u (r, x)) =ᶠ[𝓝 t] (fun r => v (r, x)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact sub_eq_zero.mp (hsupp r (Ioo_subset_Icc_self hr) x hxK)
  have hX : (fun y => u (t, y)) =ᶠ[𝓝 x] (fun y => v (t, y)) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hxK] with y hy
    exact sub_eq_zero.mp (hsupp t (Ioo_subset_Icc_self ht) y hy)
  have hP : (fun y => p (t, y)) =ᶠ[𝓝 x] (fun y => q (t, y)) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hxK] with y hy
    exact sub_eq_zero.mp (hpressure y hy)
  exact hx (sub_eq_zero.mpr (residual_eq_of_germs ν t x hT hX hP))

/-- Jointly smooth velocity and smooth spatial pressure give a continuous
spatial residual at every interior time. -/
theorem continuous_residual {u : VelocityField} {p : PressureField} {a b t ν : ℝ}
    (hu : ContDiffOn ℝ ∞ u (Icc a b ×ˢ univ))
    (hp : ContDiff ℝ ∞ (fun x => p (t, x))) (ht : t ∈ Ioo a b) :
    Continuous (NSFormalization.Source.residual ν u p t) := by
  have hus := NavierStokes.PeriodicUniqueness.spatial_smooth hu (Ioo_subset_Icc_self ht)
  have hT : Continuous (temporalDerivative u t) :=
    NavierStokesR3.CompactTimeIntegral.continuous_slice
      (NavierStokesR3.CompactTimeIntegral.continuousOn_timeDeriv_of_contDiffOn
        (hu.of_le (by simp))) ht
  have hA : Continuous (advection u t) :=
    (hus.continuous_fderiv (by simp)).clm_apply hus.continuous
  have hL := (NavierStokes.PeriodicUniqueness.spatialLaplacian_contDiff hus).continuous
  have hP := (NavierStokes.PeriodicUniqueness.pressureGradient_contDiff hp).continuous
  exact ((hT.add hA).sub (hL.const_smul ν)).add hP

/-- Compact velocity/pressure differences yield integrability of each actual
residual difference component without any global integrability of the background. -/
theorem integrable_residual_difference_component
    {u v : VelocityField} {p q : PressureField} {a b t ν : ℝ} {K : Set Space}
    (hK : IsCompact K)
    (hu : ContDiffOn ℝ ∞ u (Icc a b ×ˢ univ))
    (hv : ContDiffOn ℝ ∞ v (Icc a b ×ˢ univ))
    (hp : ContDiff ℝ ∞ (fun x => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x => q (t, x)))
    (hsupp : ∀ r ∈ Icc a b, ∀ x ∉ K, (u - v) (r, x) = 0)
    (hpressure : ∀ x ∉ K, (p - q) (t, x) = 0) (ht : t ∈ Ioo a b) (j : Fin 3) :
    MeasureTheory.Integrable (fun x : Space => NSFormalization.Source.residual ν u p t x j -
      NSFormalization.Source.residual ν v q t x j) := by
  have hsupport := support_residual_difference_subset hK.isClosed hsupp hpressure ht (ν := ν)
  have hc : HasCompactSupport (fun x => NSFormalization.Source.residual ν u p t x -
      NSFormalization.Source.residual ν v q t x) := by
    apply HasCompactSupport.intro hK
    intro x hx
    by_contra hn
    exact hx (hsupport hn)
  exact ((EuclideanSpace.proj j).continuous.comp
    ((continuous_residual hu hp ht).sub (continuous_residual hv hq ht))).integrable_of_hasCompactSupport
      (NavierStokes.R3CompactIntegration.component_compact hc j)

end NSFormalization.Paper3
