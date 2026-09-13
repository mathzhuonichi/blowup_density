import NSFormalization.Source.BoundedReferenceComparison

/-! Actual same-force uniqueness against arbitrary smooth finite-energy competitors. -/
noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace NSFormalization.Source.BoundedReferenceUniqueness

open NavierStokesR3 ProblemStatement Comparison
open NavierStokes.ProblemStatement (spatialDivergence)
open NavierStokes.PeriodicUniqueness (spatial_smooth)

/-- A uniform velocity bound and actual kinetic energy already supply the L3
bound needed by the existing pressure reconstruction. -/
theorem exists_lpNorm_three_bound {T B : ℝ} {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (heu : UniformFiniteEnergy (Icc (0 : ℝ) T) u)
    (hB0 : 0 ≤ B) (hB : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖u (t,x)‖ ≤ B) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ Icc (0 : ℝ) T,
      MemLp (fun x => u (t,x)) 3 volume ∧ comparisonLpNorm 3 (fun x => u (t,x)) ≤ L := by
  obtain ⟨E, hE, he⟩ := heu
  refine ⟨(B * (2 * E)) ^ (3 : ℝ)⁻¹, by positivity, ?_⟩
  intro t ht
  have hc := (spatial_smooth hu ht).continuous
  obtain ⟨hi, henergy⟩ := he t ht
  have hpoint (x : Space) : ‖u (t,x)‖ ^ 3 ≤ B * ‖u (t,x)‖ ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right (hB t ht x) (sq_nonneg ‖u (t,x)‖)]
  have hcube : Integrable (fun x => ‖u (t,x)‖ ^ 3) :=
    (hi.const_mul B).mono' (hc.norm.pow 3).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by simpa only [norm_pow, norm_norm] using hpoint x))
  have hLp : MemLp (fun x => u (t,x)) 3 volume := by
    apply (integrable_norm_rpow_iff hc.aestronglyMeasurable (by norm_num : (3 : ℝ≥0∞) ≠ 0)
      (by norm_num : (3 : ℝ≥0∞) ≠ ⊤)).mp
    have heq : (fun x : Space => ‖u (t,x)‖ ^ (3 : ℝ)) =
        (fun x : Space => ‖u (t,x)‖ ^ (3 : ℕ)) :=
      funext (fun x => Real.rpow_natCast ‖u (t,x)‖ 3)
    simpa only [ENNReal.toReal_ofNat, heq] using hcube
  refine ⟨hLp, ?_⟩
  rw [CompactComparisonBounds.lpNorm_three_eq_integral_norm_cube_rpow hLp]
  apply Real.rpow_le_rpow (integral_nonneg (fun x => pow_nonneg (norm_nonneg _) 3)) _ (by positivity)
  have hb := integral_mono hcube (hi.const_mul B) hpoint
  rw [integral_const_mul] at hb
  unfold kineticEnergy at henergy
  nlinarith only [hb, mul_le_mul_of_nonneg_left henergy hB0]

/-- Whole-space comparison for a bounded smooth finite-energy reference. The
competitor has no support, pressure-growth, derivative-growth or energy-inequality premise. -/
theorem classical_uniqueness_on_Icc {T : ℝ} (hT : 0 < T)
    {u v : VelocityField} {p q : PressureField} {B G : ℝ}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (heu : UniformFiniteEnergy (Icc (0 : ℝ) T) u)
    (hB0 : 0 ≤ B) (hB : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖u (t,x)‖ ≤ B)
    (hG0 : 0 ≤ G) (hG : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      ‖NavierStokes.ProblemStatement.spatialDerivative u t x‖ ≤ G)
    (hev : UniformFiniteEnergy (Icc (0 : ℝ) T) v)
    (hdu : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      navierStokesResidual 1 u p t x = navierStokesResidual 1 v q t x)
    (hzero : ∀ x, u (0, x) = v (0, x)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x) := by
  obtain ⟨L, hL0, hL⟩ := exists_lpNorm_three_bound hu heu hB0 hB
  let H : PressureRecovery.Hypotheses T u v p q :=
    ⟨hT, hu, hv, hp, hq, hdu, hdv, (fun t ht x => by simpa using hNS t ht x), heu, hev⟩
  have hum : ∀ t ∈ Icc (0 : ℝ) T,
      AEStronglyMeasurable (fun x => u (t, x)) volume :=
    fun t ht => (spatial_smooth hu ht).continuous.aestronglyMeasurable
  have hvm : ∀ t ∈ Icc (0 : ℝ) T,
      AEStronglyMeasurable (fun x => v (t, x)) volume :=
    fun t ht => (spatial_smooth hv ht).continuous.aestronglyMeasurable
  have hew := uniformFiniteEnergy_sub hum hvm heu hev
  obtain ⟨M, hM0, hM⟩ := uniformFiniteEnergy_lpNorm_two_bound
    (fun t ht => (hum t ht).sub (hvm t ht)) hew
  obtain ⟨G₀, hG₀, hTensor⟩ := uniformFiniteEnergy_tensorDiff_lpNorm_one_bound hum hvm heu hev
  obtain ⟨CP, hCP, hpressure⟩ := PressureFlux.exists_uniform_actual_pressure_flux_bound
    H M L G₀ hM0 hL0 hG₀ hM hL hTensor
  apply BoundedReferenceComparison.eq_of_pressure_flux_bound
    hT.le hM0 hG0 hCP hB0 hB hu hv hp hq
    (fun t ht => (hM t ht).1) (fun t ht => (hM t ht).2) hG hdu hdv hNS hzero
  intro R hR t ht
  simpa only [BoundedReferenceComparison.pressureEnvelope, neg_div] using hpressure R hR t ht

end NSFormalization.Source.BoundedReferenceUniqueness
