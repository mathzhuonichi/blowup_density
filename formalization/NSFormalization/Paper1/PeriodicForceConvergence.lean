import NSFormalization.Paper1.PeriodicBridge
import NSFormalization.Paper1.PeriodicSobolev
import NSFormalization.Paper1.LocalizationBoundary
import NSFormalization.Source.CompactForceConvergence

/-!
# Transfer of compact force limits to a periodic lift

This file deliberately separates the analytic transfer from the missing
fractional localization estimate.  A comparison bound between the periodic
norm and the already proved whole-space norm is an explicit hypothesis.  The
result then transports convergence by an `ENNReal` squeeze argument; no
critical embedding or unproved Fourier identification is smuggled in.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicForceConvergence

open Set Filter MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicBridge
open NSFormalization.Paper1.LocalizationBoundary
open NavierStokes.PeriodicIntegration
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open NSFormalization.Paper1.LocalizationBoundary
open scoped ContDiff ENNReal Topology

/-- The componentwise periodic Sobolev norm used for a periodic velocity force.
The scalar components are measured with the actual unit-period Fourier series
on the fundamental cube. -/
def periodicVectorSobolevNorm (s : ℝ) (F : VelocityField) (t : ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin 3,
    periodicSobolevSq s (fun x => coordinateForce F i (t, x)))

/-- Negating a periodic force does not change any Fourier Sobolev energy.  This
lemma is purely algebraic and therefore does not assert regularity or finiteness. -/
theorem periodicVectorSobolevNorm_neg (s : ℝ) (F : VelocityField) (t : ℝ) :
    periodicVectorSobolevNorm s (-F) t = periodicVectorSobolevNorm s F t := by
  unfold periodicVectorSobolevNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hcoord : (fun x => coordinateForce (-F) i (t, x)) =
      (fun x => -(coordinateForce F i (t, x))) := by
    funext x
    simp [coordinateForce]
  rw [hcoord]
  unfold periodicSobolevSq
  apply tsum_congr
  intro k
  rw [periodicFourierCoeff_eq_cube, periodicFourierCoeff_eq_cube]
  unfold cubeIntegral
  simp only [Pi.neg_apply, mul_neg]
  rw [integral_neg]
  simp

theorem periodicVectorSobolevNorm_le_sum (s : ℝ) (F : VelocityField) (t : ℝ) :
    periodicVectorSobolevNorm s F t ≤
      ∑ i : Fin 3, periodicSobolevNorm s
        (fun x => coordinateForce F i (t, x)) := by
  unfold periodicVectorSobolevNorm
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  · have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (f := fun i : Fin 3 => periodicSobolevNorm s
        (fun x => coordinateForce F i (t, x)))
      (fun _ _ => Real.sqrt_nonneg _)
    have henergy (i : Fin 3) :
        0 ≤ periodicSobolevSq s (fun x => coordinateForce F i (t, x)) := by
      unfold periodicSobolevSq
      exact tsum_nonneg (fun k => mul_nonneg
        (Real.rpow_nonneg ((one_le_periodicFrequencyWeight k).trans' zero_le_one) s)
        (sq_nonneg _))
    simpa only [periodicSobolevNorm, Real.sq_sqrt (henergy _)] using h

/- A componentwise endpoint interpolation estimate for a genuine periodized
  vector field.  The hypotheses keep the derivative integrability visible;
  this is an assembly lemma, not a hidden fractional localization theorem. -/
theorem periodicVectorSobolevNorm_periodize_interpolation
    {r : ℝ} {F : VelocityField} (hF : SupportedInCube r F)
    (hr : r < 1 / 2)
    (hreg : ∀ i : Fin 3, ContDiff ℝ 1 (coordinateForce F i)) {t : ℝ}
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h0 : ∀ i : Fin 3,
      Integrable (fun x : Space => ‖coordinateForce F i (t, x)‖ ^ 2))
    (h1 : ∀ i j : Fin 3,
      Integrable (fun x : Space =>
        ‖spatialPartial j (fun y => coordinateForce F i (t, y)) x‖ ^ 2)) :
    periodicVectorSobolevNorm s (periodize F) t ≤
      ∑ i : Fin 3,
        (Real.sqrt (∫ x : Space, ‖coordinateForce F i (t, x)‖ ^ 2)) ^ (1 - s) *
          (Real.sqrt ((∫ x : Space, ‖coordinateForce F i (t, x)‖ ^ 2) +
            ∑ j : Fin 3, ∫ x : Space,
              ‖spatialPartial j (fun y => coordinateForce F i (t, y)) x‖ ^ 2)) ^ s := by
  apply (periodicVectorSobolevNorm_le_sum s (periodize F) t).trans
  apply Finset.sum_le_sum
  intro i hi
  have hcoord : (fun z => coordinateForce (periodize F) i z) =
      periodize (coordinateForce F i) := by
    have hp := periodize_comp hF hr
      (fun v : Space => (v i : ℂ)) (by simp)
    funext z
    exact congrFun hp z
  have hinterp := LocalizationBoundary.periodicSobolevNorm_periodize_interpolation_complex
      (f := coordinateForce F i)
      (supported_comp hF (fun v : Space => (v i : ℂ)) (by simp)) hr
      (hreg i) (h0 i)
      (fun j => h1 i j) hs0 hs1
  have hcoordslice : (fun x : Space => coordinateForce (periodize F) i (t, x)) =
      (fun x : Space => periodize (coordinateForce F i) (t, x)) := by
    funext x
    exact congrFun hcoord (t, x)
  rw [hcoordslice]
  exact hinterp

/-- The Euclidean vector norm of the three component Sobolev energies has an
`L¹` time bound by the finite sum of the component norms.  Measurability of
those scalar time profiles is kept as an explicit premise, so this transfer
lemma does not assume regularity of a packet or background implicitly. -/
theorem eLpNorm_periodicVectorSobolevNorm_le_sum
    {s : ℝ} {F : VelocityField}
    (hmeas : ∀ i : Fin 3, AEStronglyMeasurable
      (fun t : ℝ => periodicSobolevNorm s
        (fun x => coordinateForce F i (t, x))) volume) :
    eLpNorm (fun t => periodicVectorSobolevNorm s F t) 1 volume ≤
      ∑ i : Fin 3, eLpNorm
        (fun t => periodicSobolevNorm s
          (fun x => coordinateForce F i (t, x))) 1 volume := by
  apply (eLpNorm_mono_real (p := (1 : ℝ≥0∞)) (μ := volume)
    (f := fun t => periodicVectorSobolevNorm s F t)
    (g := fun t => ∑ i : Fin 3, periodicSobolevNorm s
      (fun x => coordinateForce F i (t, x))) (fun t => ?_)).trans
  · exact eLpNorm_sum_le
      (s := (Finset.univ : Finset (Fin 3)))
      (f := fun i t => periodicSobolevNorm s
        (fun x => coordinateForce F i (t, x)))
      (fun i _ => hmeas i) (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  · rw [Real.norm_eq_abs, abs_of_nonneg
      (show 0 ≤ periodicVectorSobolevNorm s F t from Real.sqrt_nonneg _)]
    exact periodicVectorSobolevNorm_le_sum s F t

/-- A uniform componentwise comparison yields a reusable vector comparison
with the finite-dimensional factor.  The source profiles are arbitrary real
`L¹` profiles; in applications they are the componentwise whole-space
Fourier-Sobolev norms supplied by `CompactForceConvergence`. -/
theorem periodicVector_bound_of_component_bounds
    {s : ℝ} {P : VelocityField} {C : ℝ≥0∞}
    (hmeas : ∀ i : Fin 3, AEStronglyMeasurable
      (fun t : ℝ => periodicSobolevNorm s
        (fun x => coordinateForce P i (t, x))) volume)
    {g : Fin 3 → ℝ → ℝ}
    (hcomp : ∀ i : Fin 3,
      eLpNorm (fun t => periodicSobolevNorm s
        (fun x => coordinateForce P i (t, x))) 1 volume ≤
        C * eLpNorm (g i) 1 volume) :
    eLpNorm (fun t => periodicVectorSobolevNorm s P t) 1 volume ≤
      C * ∑ i : Fin 3, eLpNorm (g i) 1 volume := by
  have hv := eLpNorm_periodicVectorSobolevNorm_le_sum (s := s) (F := P) hmeas
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
    (fun i _ => hcomp i)
  calc
    eLpNorm (fun t => periodicVectorSobolevNorm s P t) 1 volume ≤
        ∑ i : Fin 3, eLpNorm
          (fun t => periodicSobolevNorm s
            (fun x => coordinateForce P i (t, x))) 1 volume := hv
    _ ≤ ∑ i : Fin 3, C * eLpNorm (g i) 1 volume := hsum
    _ = C * ∑ i : Fin 3, eLpNorm (g i) 1 volume := by
      rw [Finset.mul_sum]

/-- Any finite multiplicative localization bound transfers a whole-space
`L¹_t H^s_x` limit to the periodic norm.  The bound is intentionally stated
at the time-norm level: proving it for a particular endpoint or fractional
order remains a separate, explicit localization obligation. -/
theorem tendsto_periodic_of_whole_bound
    {s : ℝ} {F P : ℝ → VelocityField} {C : ℝ≥0∞}
    (hwhole : Tendsto
      (fun ε : ℝ => eLpNorm (vectorFourierSobolevNorm s (F ε)) 1 volume)
      (𝓝[>] 0) (𝓝 0))
    (hC : C ≠ (⊤ : ℝ≥0∞))
    (hbound : ∀ᶠ ε in (𝓝[>] (0 : ℝ)),
      eLpNorm (fun t => periodicVectorSobolevNorm s (P ε) t) 1 volume ≤
        C * eLpNorm (vectorFourierSobolevNorm s (F ε)) 1 volume) :
    Tendsto
      (fun ε : ℝ => eLpNorm (fun t => periodicVectorSobolevNorm s (P ε) t) 1 volume)
      (𝓝[>] 0) (𝓝 0) := by
  have hupper := ENNReal.Tendsto.const_mul hwhole (a := C) (Or.inr hC)
  simp only [mul_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall (fun _ => bot_le)
  · exact hbound

/-- The preceding transfer with a uniform finite constant.  This is the form
used when the endpoint localization estimate has a constant independent of
the concentrating parameter. -/
theorem tendsto_periodic_of_uniform_whole_bound
    {s : ℝ} {F P : ℝ → VelocityField} {C : ℝ≥0∞}
    (hwhole : Tendsto
      (fun ε : ℝ => eLpNorm (vectorFourierSobolevNorm s (F ε)) 1 volume)
      (𝓝[>] 0) (𝓝 0))
    (hC : C ≠ (⊤ : ℝ≥0∞))
    (hbound : ∀ ε > 0,
      eLpNorm (fun t => periodicVectorSobolevNorm s (P ε) t) 1 volume ≤
        C * eLpNorm (vectorFourierSobolevNorm s (F ε)) 1 volume) :
    Tendsto
      (fun ε : ℝ => eLpNorm (fun t => periodicVectorSobolevNorm s (P ε) t) 1 volume)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_periodic_of_whole_bound hwhole hC
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε

/-- Concrete periodized form of the transfer lemma.  Here `P ε` is fixed to
the genuine lattice periodization of `F ε`; only the stated comparison bound
is left to the endpoint/localization argument. -/
theorem tendsto_periodized_of_whole_bound
    {s : ℝ} {F : ℝ → VelocityField} {C : ℝ≥0∞}
    (hwhole : Tendsto
      (fun ε : ℝ => eLpNorm (vectorFourierSobolevNorm s (F ε)) 1 volume)
      (𝓝[>] 0) (𝓝 0))
    (hC : C ≠ (⊤ : ℝ≥0∞))
    (hbound : ∀ ε > 0,
      eLpNorm (fun t => periodicVectorSobolevNorm s (periodize (F ε)) t) 1 volume ≤
        C * eLpNorm (vectorFourierSobolevNorm s (F ε)) 1 volume) :
    Tendsto
      (fun ε : ℝ => eLpNorm
        (fun t => periodicVectorSobolevNorm s (periodize (F ε)) t) 1 volume)
      (𝓝[>] 0) (𝓝 0) := by
  exact tendsto_periodic_of_uniform_whole_bound hwhole hC hbound

/-- The same statement specialized to the already formalized compact-force
convergence theorem.  Thus no new whole-space estimate is introduced here;
the only new obligation is the explicit comparison for the periodized lift. -/
theorem tendsto_periodized_parabolic_compact_force_L1
    {s : ℝ} (hs : s < 1 / 2) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (center : ℝ → ℝ) (spatialCenter : ℝ → Space) {C : ℝ≥0∞}
    (hC : C ≠ (⊤ : ℝ≥0∞))
    (hbound : ∀ ε > 0,
      eLpNorm (fun t => periodicVectorSobolevNorm s
        (periodize (parabolicForce ε⁻¹ (center ε) (spatialCenter ε) F)) t) 1 volume ≤
        C * eLpNorm (vectorFourierSobolevNorm s
          (parabolicForce ε⁻¹ (center ε) (spatialCenter ε) F)) 1 volume) :
    Tendsto
      (fun ε : ℝ => eLpNorm (fun t => periodicVectorSobolevNorm s
        (periodize (parabolicForce ε⁻¹ (center ε) (spatialCenter ε) F)) t) 1 volume)
      (𝓝[>] 0) (𝓝 0) := by
  exact tendsto_periodized_of_whole_bound
    (hwhole := compact_vector_force_L1_tendsto hs hF hc center spatialCenter)
    hC hbound

end NSFormalization.Paper1.PeriodicForceConvergence
