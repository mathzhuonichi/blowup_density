import Formal.EndpointSafeTwoSpaceDuhamel
import Formal.R3ProjectedSobolevConvection
import Formal.R3StokesH3Evolution

namespace MNS2

open MeasureTheory Set
open scoped Interval NNReal

noncomputable section

/--
The concrete endpoint-safe two-space mild contract on the order-three and order-two
Bessel-coordinate carriers.

The same-space initial evolution is indexed by honest nonnegative time. The cross-space
map is available only for positive elapsed time, and its endpoint totalization is supplied
by the generic contract rather than by a fictitious bounded H² to H³ map at time zero.
-/
def r3EndpointSafeProjectedDuhamelContract
    {nu : ℝ} (hnu : 0 < nu) :
    EndpointSafeTwoSpaceDuhamelContract ℂ
      (R3HsVelocity 3) (R3HsVelocity 2) where
  linearEvolution := r3StokesH3Evolution hnu.le
  linear_zero := r3StokesH3Evolution_zero hnu.le
  linear_add := r3StokesH3Evolution_add hnu.le
  continuous_linear_action := continuous_r3StokesH3Evolution_action hnu.le
  positiveSmoothing := fun _tau htau =>
    r3StokesH2ToH3Operator hnu htau
  bilinear := r3ProjectedConvectionH3ToH2
  smoothingKernel := r3StokesH2H3TimeKernel nu
  smoothingKernel_nonneg := fun _tau htau =>
    r3StokesH2H3TimeKernel_nonneg hnu htau
  norm_positiveSmoothing_apply_le := fun _tau htau y =>
    norm_r3StokesH2ToH3Operator_apply_le hnu htau y
  intervalIntegrable_smoothingKernel := fun _T hT =>
    intervalIntegrable_r3StokesH2H3TimeKernel hnu hT
  smoothing_coherent := fun _a ha b =>
    r3StokesH2ToH3Operator_add_nnreal hnu ha b

/-- The actual endpoint-safe projected-convection Duhamel integrand in the H³ carrier. -/
def r3EndpointSafeProjectedDuhamelIntegrand
    {nu : ℝ} (hnu : 0 < nu)
    (t : ℝ) (u : ℝ → R3HsVelocity 3) (s : ℝ) :
    R3HsVelocity 3 :=
  (r3EndpointSafeProjectedDuhamelContract hnu).duhamelIntegrand t u s

@[simp]
theorem r3EndpointSafeProjectedDuhamelIntegrand_endpoint
    {nu : ℝ} (hnu : 0 < nu)
    (t : ℝ) (u : ℝ → R3HsVelocity 3) :
    r3EndpointSafeProjectedDuhamelIntegrand hnu t u t = 0 := by
  exact
    (r3EndpointSafeProjectedDuhamelContract hnu).duhamelIntegrand_endpoint t u

theorem r3EndpointSafeProjectedDuhamelIntegrand_of_lt
    {nu : ℝ} (hnu : 0 < nu)
    (t : ℝ) (u : ℝ → R3HsVelocity 3) {s : ℝ} (hs : s < t) :
    r3EndpointSafeProjectedDuhamelIntegrand hnu t u s =
      r3StokesH2ToH3Operator hnu (sub_pos.mpr hs)
        (r3ProjectedConvectionH3ToH2 (u s) (u s)) := by
  exact
    (r3EndpointSafeProjectedDuhamelContract hnu).duhamelIntegrand_of_lt
      t u hs

theorem r3EndpointSafeProjectedDuhamelIntegrand_of_le
    {nu : ℝ} (hnu : 0 < nu)
    (t : ℝ) (u : ℝ → R3HsVelocity 3) {s : ℝ} (hs : t ≤ s) :
    r3EndpointSafeProjectedDuhamelIntegrand hnu t u s = 0 := by
  exact
    (r3EndpointSafeProjectedDuhamelContract hnu).duhamelIntegrand_of_le
      t u hs

/-- The completed projected-convection and smoothing estimates give the actual pointwise bound. -/
theorem norm_r3EndpointSafeProjectedDuhamelIntegrand_le
    {nu : ℝ} (hnu : 0 < nu)
    (t : ℝ) (u : ℝ → R3HsVelocity 3) (s : ℝ) :
    ‖r3EndpointSafeProjectedDuhamelIntegrand hnu t u s‖ ≤
      endpointSafePositiveMajorant (r3StokesH2H3TimeKernel nu) (t - s) *
        ‖r3ProjectedConvectionH3ToH2‖ * ‖u s‖ ^ 2 := by
  exact
    (r3EndpointSafeProjectedDuhamelContract hnu).norm_duhamelIntegrand_le
      t u s

/--
For a continuous H³ trajectory, the actual vector-valued integrand is strongly measurable
on the interval. The proof uses positive-time joint smoothing continuity and changes only the
null endpoint s = t; scalar-kernel measurability alone is not used as a substitute.
-/
theorem aestronglyMeasurable_r3EndpointSafeProjectedDuhamelIntegrand
    {nu t : ℝ} (hnu : 0 < nu) (ht : 0 ≤ t)
    {u : ℝ → R3HsVelocity 3} (hu : ContinuousOn u (Icc 0 t)) :
    AEStronglyMeasurable
      (r3EndpointSafeProjectedDuhamelIntegrand hnu t u)
      (volume.restrict (Ι (0 : ℝ) t)) := by
  exact (r3EndpointSafeProjectedDuhamelContract hnu).aestronglyMeasurable_duhamelIntegrand_interval
    ht hu

/--
The actual projected-convection/Stokes integrand is Bochner interval-integrable for every
continuous H³ trajectory on a compact forward-time interval.
-/
theorem intervalIntegrable_r3EndpointSafeProjectedDuhamelIntegrand
    {nu t : ℝ} (hnu : 0 < nu) (ht : 0 ≤ t)
    {u : ℝ → R3HsVelocity 3} (hu : ContinuousOn u (Icc 0 t)) :
    IntervalIntegrable
      (r3EndpointSafeProjectedDuhamelIntegrand hnu t u) volume 0 t := by
  exact (r3EndpointSafeProjectedDuhamelContract hnu).intervalIntegrable_duhamelIntegrand_of_continuousOn
    ht hu

/-- Quantitative norm bound for the actual Duhamel integral under a trajectory bound. -/
theorem norm_integral_r3EndpointSafeProjectedDuhamelIntegrand_le
    {nu t R : ℝ} (hnu : 0 < nu) (ht : 0 ≤ t) (hR : 0 ≤ R)
    (u : ℝ → R3HsVelocity 3)
    (hu : ∀ s ∈ Icc (0 : ℝ) t, ‖u s‖ ≤ R) :
    ‖∫ s in (0 : ℝ)..t,
        r3EndpointSafeProjectedDuhamelIntegrand hnu t u s‖ ≤
      ∫ s in (0 : ℝ)..t,
        endpointSafePositiveMajorant
            (r3StokesH2H3TimeKernel nu) (t - s) *
          ‖r3ProjectedConvectionH3ToH2‖ * R ^ 2 := by
  have hsafe :
      IntervalIntegrable
        (endpointSafePositiveMajorant (r3StokesH2H3TimeKernel nu))
        volume 0 t :=
    intervalIntegrable_endpointSafePositiveMajorant
      (r3StokesH2H3TimeKernel nu) ht
      (intervalIntegrable_r3StokesH2H3TimeKernel hnu ht)
  have hrev : IntervalIntegrable
      (fun s : ℝ =>
        endpointSafePositiveMajorant
          (r3StokesH2H3TimeKernel nu) (t - s)) volume 0 t :=
    intervalIntegrable_endpointSafePositiveMajorant_sub
      (r3StokesH2H3TimeKernel nu) hsafe
  have hmajorant : IntervalIntegrable
      (fun s : ℝ =>
        endpointSafePositiveMajorant
            (r3StokesH2H3TimeKernel nu) (t - s) *
          ‖r3ProjectedConvectionH3ToH2‖ * R ^ 2)
      volume 0 t := by
    simpa only [mul_assoc] using
      hrev.mul_const (‖r3ProjectedConvectionH3ToH2‖ * R ^ 2)
  apply intervalIntegral.norm_integral_le_of_norm_le ht
  · exact ae_of_all _ fun s hs =>
      norm_endpointSafeTwoSpaceDuhamelIntegrand_le_of_trajectory_norm
        (fun _tau htau => r3StokesH2ToH3Operator hnu htau)
        r3ProjectedConvectionH3ToH2
        (r3StokesH2H3TimeKernel nu)
        (fun tau htau => r3StokesH2H3TimeKernel_nonneg hnu htau)
        (fun tau htau y =>
          norm_r3StokesH2ToH3Operator_apply_le hnu htau y)
        t u R hR s (hu s ⟨hs.1.le, hs.2⟩)
  · exact hmajorant

/-- Concrete endpoint-safe two-space mild-solution predicate. -/
def IsR3EndpointSafeProjectedMildSolutionOn
    {nu : ℝ} (hnu : 0 < nu)
    (T : ℝ) (u0 : R3HsVelocity 3)
    (u : ℝ → R3HsVelocity 3) : Prop :=
  (r3EndpointSafeProjectedDuhamelContract hnu).IsMildSolutionOn T u0 u

/-- Expose the concrete same-space initial term and actual integrable Duhamel equation. -/
theorem r3EndpointSafeProjectedMild_equation_at_time
    {nu T : ℝ} (hnu : 0 < nu)
    {u0 : R3HsVelocity 3} {u : ℝ → R3HsVelocity 3}
    (h : IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable
        (r3EndpointSafeProjectedDuhamelIntegrand hnu t u) volume 0 t ∧
      u t =
        r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0 -
          ∫ s in (0 : ℝ)..t,
            r3EndpointSafeProjectedDuhamelIntegrand hnu t u s := by
  exact
    (r3EndpointSafeProjectedDuhamelContract hnu).equation_at_time h ht

end

end MNS2
