import NSFormalization.Paper1.PeriodicForceEndpoints
import NSFormalization.Paper1.PeriodicInsertionSupport

/-!
# Concrete periodic force convergence at every nonpositive order

Parseval and the disjoint-copy endpoint identity identify periodic `H⁰`
with the whole-space zero-order Fourier norm. Periodic weight monotonicity
then controls every `s ≤ 0`. Applied to the actual concentrated force, this
discharges the periodization comparison rather than assuming it.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicNonpositiveForce

open Set Filter MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open NSFormalization.Source NSFormalization.Paper1
open PeriodicBridge PeriodicForceConvergence PeriodicForceEndpoints
open scoped ContDiff ENNReal Topology FourierTransform

theorem whole_zero_energy_eq {f : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    fourierSobolevSq 0 f = ∫ x : Space, ‖f x‖ ^ 2 := by
  let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport f hf hc
  unfold fourierSobolevSq
  simp only [Real.rpow_zero, one_mul]
  exact SchwartzMap.integral_norm_sq_fourier φ

theorem periodic_zero_norm_eq_whole {r : ℝ} {F : VelocityField}
    (hsupp : SupportedInCube r F) (hr : r < 1 / 2)
    (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    periodicVectorSobolevNorm 0 (periodize F) t = vectorFourierSobolevNorm 0 F t := by
  have hslice (i : Fin 3) : ContDiff ℝ ∞ (fun x => coordinateForce F i (t, x)) :=
    (coordinateForce_smooth hF i).comp (contDiff_const.prodMk contDiff_id)
  have hcompact (i : Fin 3) : HasCompactSupport (fun x => coordinateForce F i (t, x)) :=
    slice_compact_of_supported (supported_comp hsupp
      (fun v : Space => (v i : ℂ)) (by simp)) t
  have hint (i : Fin 3) : Integrable (fun x : Space => ‖coordinateForce F i (t, x)‖ ^ 2) := by
    let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport
      (fun x => coordinateForce F i (t, x)) (hslice i) (hcompact i)
    exact (φ.memLp 2 volume).integrable_norm_pow (by norm_num)
  rw [periodicVectorSobolevNorm_zero_periodize_eq hsupp hr
    (fun i => (coordinateForce_smooth hF i).of_le (by norm_num)) hint]
  unfold vectorFourierSobolevNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (whole_zero_energy_eq (hslice i) (hcompact i)).symm

theorem periodic_vector_norm_mono {s q : ℝ} (hsq : s ≤ q) (hq : q ≤ 1)
    {F : VelocityField} (hF : ContDiff ℝ ∞ F)
    (hp : UnitSpatialPeriodsOn univ F) (t : ℝ) :
    periodicVectorSobolevNorm s F t ≤ periodicVectorSobolevNorm q F t := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  have hs : ContDiff ℝ 1 (fun x => coordinateForce F i (t, x)) :=
    ((coordinateForce_smooth hF i).comp
      (contDiff_const.prodMk contDiff_id)).of_le (by norm_num)
  have hper : UnitPeriods (fun x => coordinateForce F i (t, x)) := by
    intro x j
    exact congrArg (fun v : Space => (v i : ℂ)) (hp t (mem_univ _) x j)
  exact periodicSobolevSq_mono hs hper hsq hq

theorem periodic_nonpositive_norm_le_whole_zero {s r : ℝ} (hs : s ≤ 0)
    {F : VelocityField} (hsupp : SupportedInCube r F) (hr : r < 1 / 2)
    (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    periodicVectorSobolevNorm s (periodize F) t ≤ vectorFourierSobolevNorm 0 F t := by
  rw [← periodic_zero_norm_eq_whole hsupp hr hF t]
  exact periodic_vector_norm_mono hs (by norm_num)
    (contDiff_periodize hsupp hF) (unitSpatialPeriodsOn_periodize F univ) t

theorem periodic_nonpositive_L1_le_whole_zero {s r : ℝ} (hs : s ≤ 0)
    {F : VelocityField} (hsupp : SupportedInCube r F) (hr : r < 1 / 2)
    (hF : ContDiff ℝ ∞ F) :
    eLpNorm (fun t => periodicVectorSobolevNorm s (periodize F) t) 1 volume ≤
      eLpNorm (vectorFourierSobolevNorm 0 F) 1 volume := by
  apply eLpNorm_mono_real
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ periodicVectorSobolevNorm s _ t
    from Real.sqrt_nonneg _)]
  exact periodic_nonpositive_norm_le_whole_zero hs hsupp hr hF t

/- A family-level adapter: eventual fixed-cube support is enough to transfer
 any already proved whole-space zero-order limit to every nonpositive periodic
 order. -/
theorem periodic_nonpositive_L1_tendsto_of_eventually_supported
    {s : ℝ} (hs : s ≤ 0) {F : ℝ → VelocityField}
    (hF : ∀ ε, ContDiff ℝ ∞ (F ε))
    (hwhole : Tendsto (fun ε : ℝ =>
      eLpNorm (vectorFourierSobolevNorm 0 (F ε)) 1 volume)
      (𝓝[>] 0) (𝓝 0))
    (hsupp : ∀ᶠ ε : ℝ in 𝓝[>] 0, SupportedInCube (1 / 4) (F ε)) :
    Tendsto (fun ε : ℝ => eLpNorm (fun t =>
      periodicVectorSobolevNorm s (periodize (F ε)) t) 1 volume)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hwhole
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [hsupp] with ε hε
    exact periodic_nonpositive_L1_le_whole_zero hs hε (by norm_num) (hF ε)

/-- The actual compact packet force converges after periodization for every
`s ≤ 0`, without a localization comparison hypothesis. -/
theorem concentrated_force_periodic_L1_tendsto_zero {s : ℝ} (hs : s ≤ 0)
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (center : ℝ → ℝ) :
    Tendsto (fun ε : ℝ => eLpNorm (fun t => periodicVectorSobolevNorm s
      (periodize (parabolicForce ε⁻¹ (center ε) 0 F)) t) 1 volume)
      (𝓝[>] 0) (𝓝 0) := by
  have hwhole := compact_vector_force_L1_nonpositive_tendsto (s := 0) le_rfl
    hF hc center (fun _ => 0)
  exact periodic_nonpositive_L1_tendsto_of_eventually_supported hs
    (fun ε => parabolicForce_smooth (ε⁻¹) (center ε) 0 hF) hwhole
    (eventually_supportedInQuarterCube_parabolicForce_inv hc center)

/- The same transfer applies to the complete background-removal insertion
 force. Its two summands have a common eventual cube support, while the
 whole-space convergence is the already proved insertion theorem. -/
theorem insertion_force_periodic_L1_tendsto_zero {s : ℝ} (hs : s ≤ 0)
    (ν : ℝ) {f v : VelocityField} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hv : ContDiff ℝ ∞ v)
    (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    Tendsto (fun ε : ℝ => eLpNorm (fun t => periodicVectorSobolevNorm s
      (periodize (InsertionFamily.force ν f v 0 T θ η ε)) t) 1 volume)
      (𝓝[>] 0) (𝓝 0) := by
  exact periodic_nonpositive_L1_tendsto_of_eventually_supported hs
    (fun ε => InsertionFamily.force_smooth_all ν hf hv 0 T ε hθ hη)
    (InsertionFamily.force_L1_tendsto_zero ν hf hfc hv 0 T hθ hη hθc hηc
      (by linarith))
    (eventually_supportedInQuarterCube_insertionForce ν v T hfc η hθc)

end NSFormalization.Paper1.PeriodicNonpositiveForce
