import NSFormalization.Source.Insertion
import NSFormalization.Paper3.TimeObservations
import NavierStokes.R3.ConservativeDifference

/-! Spatial means of the actual Navier--Stokes residual difference.
The background fields may be noncompact; only their differences have compact support. -/

noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NavierStokes.R3CompactIntegration
open NavierStokesR3.ConservativeDifference (scalarLaplacian)
open scoped ContDiff

 theorem compact_tensor_difference {u v : VelocityField} {t : ℝ}
    (hc : HasCompactSupport (fun x => u (t, x) - v (t, x))) (j i : Fin 3) :
    HasCompactSupport (NavierStokesR3.Comparison.tensorDiff u v t j i) := by
  apply HasCompactSupport.intro hc
  intro x hx
  have hz : (fun y => u (t, y) - v (t, y)) x = 0 := image_eq_zero_of_notMem_tsupport (f := fun y : Space => u (t, y) - v (t, y)) hx
  have heq : u (t, x) = v (t, x) := sub_eq_zero.mp hz
  simp [NavierStokesR3.Comparison.tensorDiff, heq]

 theorem integral_scalarLaplacian_eq_zero {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ x : Space, scalarLaplacian f x) = 0 := by
  have hd (i : Fin 3) : ContDiff ℝ ∞ (spatialPartial i f) :=
    NavierStokes.PeriodicUniqueness.spatial_partial_contDiff hf i
  have hi (i : Fin 3) : Integrable (spatialPartial i (spatialPartial i f)) :=
    (partial_continuous ((hd i).of_le (by simp)) i).integrable_of_hasCompactSupport
      (partial_compact (partial_compact hc i) i)
  change (∫ x : Space, ∑ i : Fin 3, spatialPartial i (spatialPartial i f) x) = 0
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp [integral_spatialPartial_eq_zero ((hd _).of_le (by simp)) (partial_compact hc _)]

 theorem integral_advection_difference_component_eq_zero {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    (hc : HasCompactSupport (fun x => u (t, x) - v (t, x)))
    (hdivu : ∀ x, spatialDivergence u t x = 0)
    (hdivv : ∀ x, spatialDivergence v t x = 0) (j : Fin 3) :
    (∫ x : Space, advection u t x j - advection v t x j) = 0 := by
  have htc := compact_tensor_difference hc j
  have hts := NavierStokesR3.ConservativeDifference.tensorDiff_contDiff hu hv j
  have hi (i : Fin 3) : Integrable
      (spatialPartial i (NavierStokesR3.Comparison.tensorDiff u v t j i)) :=
    (partial_continuous ((hts i).of_le (by simp)) i).integrable_of_hasCompactSupport
      (partial_compact (htc i) i)
  have heq (x : Space) : advection u t x j - advection v t x j =
      ∑ i : Fin 3, spatialPartial i (NavierStokesR3.Comparison.tensorDiff u v t j i) x :=
    (NavierStokesR3.ConservativeDifference.tensorDiff_divergence hu hv x j (hdivu x) (hdivv x)).symm
  simp_rw [heq]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp [integral_spatialPartial_eq_zero ((hts _).of_le (by simp)) (htc _)]

/-- Joint smoothness and a common compact spatial support give integrable
temporal derivative components; no derivative integrability is assumed. -/
theorem integrable_temporalDerivative_component
    {w : VelocityField} {a b t : ℝ} {K : Set Space}
    (hK : IsCompact K) (hw : ContDiffOn ℝ ∞ w (Icc a b ×ˢ univ))
    (hsupp : ∀ r ∈ Icc a b, ∀ x ∉ K, w (r, x) = 0)
    (ht : t ∈ Ioo a b) (j : Fin 3) :
    Integrable (fun x : Space => temporalDerivative w t x j) := by
  have hG : ContinuousOn (fun q : ℝ × Space => temporalDerivative w q.1 q.2)
      (Ioo a b ×ˢ univ) :=
    NavierStokesR3.CompactTimeIntegral.continuousOn_timeDeriv_of_contDiffOn
      (hw.of_le (by simp))
  have hcont : Continuous (fun x : Space => temporalDerivative w t x) :=
    NavierStokesR3.CompactTimeIntegral.continuous_slice hG ht
  have hcompact : HasCompactSupport (fun x : Space => temporalDerivative w t x) := by
    apply HasCompactSupport.intro hK
    intro x hx
    exact NavierStokesR3.CompactTimeIntegral.derivative_eq_zero_outside
      (G := fun q : ℝ × Space => temporalDerivative w q.1 q.2)
      (fun r hr => hsupp r (Ioo_subset_Icc_self hr))
      (fun r hr x => (NavierStokes.PeriodicUniqueness.time_differentiable_at_interior hw hr x).hasDerivAt)
      ht hx
  exact ((EuclideanSpace.proj j).continuous.comp hcont).integrable_of_hasCompactSupport
    (component_compact hcompact j)

/-- The nonlinear transport difference is integrable solely from smoothness,
incompressibility and compactness of the velocity difference. -/
theorem integrable_advection_difference_component {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    (hc : HasCompactSupport (fun x => u (t, x) - v (t, x)))
    (hdivu : ∀ x, spatialDivergence u t x = 0)
    (hdivv : ∀ x, spatialDivergence v t x = 0) (j : Fin 3) :
    Integrable (fun x : Space => advection u t x j - advection v t x j) := by
  have heq (x : Space) : advection u t x j - advection v t x j =
      ∑ i : Fin 3, spatialPartial i (NavierStokesR3.Comparison.tensorDiff u v t j i) x :=
    (NavierStokesR3.ConservativeDifference.tensorDiff_divergence hu hv x j (hdivu x) (hdivv x)).symm
  simp_rw [heq]
  apply integrable_finsetSum
  intro i _
  exact (partial_continuous
    ((NavierStokesR3.ConservativeDifference.tensorDiff_contDiff hu hv j i).of_le (by simp)) i).integrable_of_hasCompactSupport (partial_compact (compact_tensor_difference hc j i) i)

/-- The scalar Laplacian of a compact smooth function is integrable. -/
theorem integrable_scalarLaplacian {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : Integrable (scalarLaplacian f) :=
  (NavierStokesR3.ConservativeDifference.scalarLaplacian_contDiff hf).continuous.integrable_of_hasCompactSupport (NavierStokesR3.ConservativeDifference.compact_scalarLaplacian hc)

/-- The actual residual difference has zero spatial component integral.
All four terms are treated as Lebesgue integrals; the reference may be noncompact.
Viscosity is arbitrary and no force-mean or conservative-balance assumption occurs. -/
theorem integral_residual_difference_component_eq_zero
    {u v : VelocityField} {p q : PressureField} {a b t ν : ℝ} {K : Set Space}
    (hK : IsCompact K)
    (hu : ContDiffOn ℝ ∞ u (Icc a b ×ˢ univ))
    (hv : ContDiffOn ℝ ∞ v (Icc a b ×ˢ univ))
    (hp : ContDiff ℝ ∞ (fun x => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x => q (t, x)))
    (hsupp : ∀ r ∈ Icc a b, ∀ x ∉ K, (u - v) (r, x) = 0)
    (hpc : HasCompactSupport (fun x => (p - q) (t, x)))
    (hdivu : ∀ r ∈ Icc a b, ∀ x, spatialDivergence u r x = 0)
    (hdivv : ∀ r ∈ Icc a b, ∀ x, spatialDivergence v r x = 0)
    (ht : t ∈ Ioo a b) (j : Fin 3) :
    (∫ x : Space, NSFormalization.Source.residual ν u p t x j -
      NSFormalization.Source.residual ν v q t x j) = 0 := by
  have ht' := Ioo_subset_Icc_self ht
  have hus := NavierStokes.PeriodicUniqueness.spatial_smooth hu ht'
  have hvs := NavierStokes.PeriodicUniqueness.spatial_smooth hv ht'
  have hws := hus.sub hvs
  have hwc : HasCompactSupport (fun x : Space => (u - v) (t, x)) :=
    HasCompactSupport.intro hK (hsupp t ht')
  have hdivw : ∀ r ∈ Icc a b, ∀ x,
      Comparator.divergence (fun y => (u - v) (r, y)) x = 0 := by
    intro r hr x
    rw [← ComparatorBridge.divergence_eq]
    rw [NavierStokes.PeriodicUniqueness.spatialDivergence_sub
      (NavierStokes.PeriodicUniqueness.spatial_smooth hu hr)
      (NavierStokes.PeriodicUniqueness.spatial_smooth hv hr), hdivu r hr, hdivv r hr, sub_self]
  have htime := integral_timeDerivative_component_eq_zero hK
    ((hu.sub hv).of_le (by simp)) hsupp hdivw ht
    (fun x => (NavierStokes.PeriodicUniqueness.time_differentiable_at_interior (hu.sub hv) ht x).hasDerivAt) j
  have hiT := integrable_temporalDerivative_component hK (hu.sub hv) hsupp ht j
  have hiA := integrable_advection_difference_component hus hvs hwc (hdivu t ht') (hdivv t ht') j
  have hwjs := NavierStokes.PeriodicUniqueness.component_contDiff hws j
  have hwjc := component_compact hwc j
  have hiL := integrable_scalarLaplacian hwjs hwjc
  have hiP : Integrable (spatialPartial j (fun x => (p - q) (t, x))) :=
    (partial_continuous ((hp.sub hq).of_le (by simp)) j).integrable_of_hasCompactSupport (partial_compact hpc j)
  have heq (x : Space) : NSFormalization.Source.residual ν u p t x j -
      NSFormalization.Source.residual ν v q t x j =
      temporalDerivative (u - v) t x j + (advection u t x j - advection v t x j) -
      ν * scalarLaplacian (fun y => (u - v) (t, y) j) x +
      spatialPartial j (fun y => (p - q) (t, y)) x := by
    have hPcomp : pressureGradient (p - q) t x j =
        spatialPartial j (fun y => (p - q) (t, y)) x :=
      NavierStokesR3.ConservativeDifference.pressureGradient_component (p - q) t x j
    rw [← NavierStokesR3.ConservativeDifference.spatialLaplacian_component hws, ← hPcomp]
    rw [NavierStokes.PeriodicUniqueness.temporalDerivative_sub
      (NavierStokes.PeriodicUniqueness.time_differentiable_at_interior hu ht x)
      (NavierStokes.PeriodicUniqueness.time_differentiable_at_interior hv ht x),
      NavierStokes.PeriodicUniqueness.spatialLaplacian_sub hus hvs,
      NavierStokes.PeriodicUniqueness.pressureGradient_sub hp hq]
    simp only [NSFormalization.Source.residual, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]
    ring
  have hsplit₁ := integral_add ((hiT.add hiA).sub (hiL.const_mul ν)) hiP
  have hsplit₂ := integral_sub (hiT.add hiA) (hiL.const_mul ν)
  simp only [Pi.add_apply, Pi.sub_apply] at hsplit₁ hsplit₂
  simp_rw [heq]
  simp only [Pi.sub_apply] at *
  change (∫ x : Space, temporalDerivative (fun z => u z - v z) t x j +
    (advection u t x j - advection v t x j) -
    ν * scalarLaplacian (fun y => (u (t, y) - v (t, y)) j) x +
    spatialPartial j (fun y => p (t, y) - q (t, y)) x) = 0
  rw [hsplit₁, hsplit₂, integral_add hiT hiA, integral_const_mul]
  change (∫ x : Space, temporalDerivative (fun z => u z - v z) t x j) = 0 at htime
  rw [htime, integral_advection_difference_component_eq_zero hus hvs hwc (hdivu t ht') (hdivv t ht') j,
    integral_scalarLaplacian_eq_zero hwjs hwjc,
    integral_spatialPartial_eq_zero ((hp.sub hq).of_le (by simp)) hpc j]
  ring

end NSFormalization.Paper3
