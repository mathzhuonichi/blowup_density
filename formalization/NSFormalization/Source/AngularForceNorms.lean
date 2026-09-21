import NSFormalization.Source.FourierConvention
import NSFormalization.Source.CompactForceConvergence

/-!
# Force convergence in the exact manuscript Fourier convention

The real vector norm uses the sum of the three unitary angular Fourier
energies. Its time seminorm is Mathlib's actual `eLpNorm`. Explicit norm
equivalence transfers the concrete compact-force estimates to this convention.
-/
noncomputable section
namespace NSFormalization.Source
open NavierStokes.ProblemStatement MeasureTheory Filter Topology
open scoped ContDiff ENNReal FourierTransform

def vectorAngularSobolevNorm (s : ℝ) (F : VelocityField) (t : ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin 3, angularSobolevSq s (fun x => coordinateForce F i (t, x)))

theorem vectorAngularSobolevNorm_equivalence (s : ℝ) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t : ℝ) :
    vectorAngularSobolevNorm s F t ≤ frequencyUnit ^ |s| * vectorFourierSobolevNorm s F t ∧
    vectorFourierSobolevNorm s F t ≤ frequencyUnit ^ |s| * vectorAngularSobolevNorm s F t := by
  have he (i : Fin 3) := angularSobolevSq_equivalence s
    (fun x => coordinateForce F i (t, x))
    (Paper3.compact_spacetime_fourier_slice_continuous (coordinateForce_smooth hF i)
      (coordinateForce_compact hc i) t)
    (Paper3.compact_spacetime_bessel_slices s (coordinateForce_smooth hF i)
      (coordinateForce_compact hc i) t)
  constructor
  · have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (he i).1)
    rw [← Finset.mul_sum] at h
    exact (Real.sqrt_le_sqrt h).trans_eq (sqrt_frequency_constant s _)
  · have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (he i).2)
    rw [← Finset.mul_sum] at h
    exact (Real.sqrt_le_sqrt h).trans_eq (sqrt_frequency_constant s _)

theorem eLpNorm_angular_le (s : ℝ) (q : ℝ≥0∞) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    eLpNorm (vectorAngularSobolevNorm s F) q volume ≤
      ENNReal.ofReal (frequencyUnit ^ |s|) * eLpNorm (vectorFourierSobolevNorm s F) q volume := by
  have h := eLpNorm_mono_real (p := q) (μ := volume)
    (f := vectorAngularSobolevNorm s F)
    (g := fun t => frequencyUnit ^ |s| * vectorFourierSobolevNorm s F t) (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (show 0 ≤ vectorAngularSobolevNorm s F t from Real.sqrt_nonneg _)]
    exact (vectorAngularSobolevNorm_equivalence s hF hc t).1)
  convert h using 1
  rw [show (fun t => frequencyUnit ^ |s| * vectorFourierSobolevNorm s F t) =
    (frequencyUnit ^ |s|) • vectorFourierSobolevNorm s F from rfl,
    eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.rpow_nonneg frequencyUnit_pos.le _)]

/-- No time regularity assumption is hidden in the transfer: the bound holds
for all time exponents, including infinity, and only uses compact smooth fields. -/
theorem angular_family_tendsto_zero (s : ℝ) (q : ℝ≥0∞) {F : ℝ → VelocityField}
    (hF : ∀ ε, ContDiff ℝ ∞ (F ε)) (hc : ∀ ε, 0 < ε → HasCompactSupport (F ε))
    (hlim : Tendsto (fun ε : ℝ => eLpNorm (vectorFourierSobolevNorm s (F ε)) q volume)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => eLpNorm (vectorAngularSobolevNorm s (F ε)) q volume)
      (𝓝[>] 0) (𝓝 0) := by
  have hm := ENNReal.Tendsto.const_mul hlim
    (a := ENNReal.ofReal (frequencyUnit ^ |s|)) (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hm
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact eLpNorm_angular_le s q (hF ε) (hc ε hε)

theorem parabolicForce_compact (k t₀ : ℝ) (x₀ : Space) {F : VelocityField}
    (hc : HasCompactSupport F) : HasCompactSupport (parabolicForce k t₀ x₀ F) := by
  by_cases hk : k = 0
  · subst k
    have hz : parabolicForce 0 t₀ x₀ F = (0 : VelocityField) := by
      funext z
      simp [parabolicForce, dilateField]
    rw [hz]
    exact HasCompactSupport.zero
  · apply HasCompactSupport.intro (hc.isCompact.image
      (show Continuous (fun z : SpaceTime => ((k ^ 2)⁻¹ * z.1 + t₀, k⁻¹ • z.2 + x₀)) by
        fun_prop))
    intro z hz
    have hn : (k ^ 2 * (z.1 - t₀), k • (z.2 - x₀)) ∉ tsupport F := by
      intro hn
      apply hz
      refine ⟨_, hn, ?_⟩
      ext <;> simp [hk, smul_smul]
    simp [parabolicForce, dilateField, image_eq_zero_of_notMem_tsupport hn]

theorem compact_angular_force_L1_tendsto {s : ℝ} (hs : s < 1 / 2)
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (center : ℝ → ℝ) (spatialCenter : ℝ → Space) :
    Tendsto (fun ε : ℝ => eLpNorm (vectorAngularSobolevNorm s
      (parabolicForce ε⁻¹ (center ε) (spatialCenter ε) F)) 1 volume)
      (𝓝[>] 0) (𝓝 0) :=
  angular_family_tendsto_zero s 1 (fun _ => parabolicForce_smooth _ _ _ hF)
    (fun _ _ => parabolicForce_compact _ _ _ hc)
    (compact_vector_force_L1_tendsto hs hF hc center spatialCenter)

theorem compact_angular_force_L2_tendsto {s : ℝ} (hs : s < -1 / 2)
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (center : ℝ → ℝ) (spatialCenter : ℝ → Space) :
    Tendsto (fun ε : ℝ => eLpNorm (vectorAngularSobolevNorm s
      (parabolicForce ε⁻¹ (center ε) (spatialCenter ε) F)) 2 volume)
      (𝓝[>] 0) (𝓝 0) :=
  angular_family_tendsto_zero s 2 (fun _ => parabolicForce_smooth _ _ _ hF)
    (fun _ _ => parabolicForce_compact _ _ _ hc)
    (compact_vector_force_L2_tendsto hs hF hc center spatialCenter)

end NSFormalization.Source
