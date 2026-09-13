import NSFormalization.Paper1.PeriodicInsertionEndpointRateBound
import NSFormalization.Paper1.PeriodicNonpositiveForce

/-!
# Subcritical convergence of the complete periodic insertion force

The actual vector endpoint rates and the periodization estimate give the
power `ε^(1/2-s)`. The coefficient is finite even if an endpoint norm is zero.
Together with the nonpositive-order branch, this proves convergence for every
`s < 1/2` without a fractional-localization or measurability premise.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicInsertionPositiveConvergence
open Set Filter MeasureTheory NavierStokes.ProblemStatement
open NavierStokes.PeriodicLocalization
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicForceConvergence
open NSFormalization.Paper1.PeriodicInsertionEndpointRateBound
open scoped ContDiff ENNReal Topology

theorem endpoint_power_product_eq {ε s : ℝ} (hε : 0 < ε)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (C₀ C₁ : ℝ≥0∞) :
    (ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * C₀) ^ (1 - s) *
      (ENNReal.ofReal (2 * Real.pi) *
        (ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * C₁)) ^ s =
    ENNReal.ofReal (ε ^ ((1 : ℝ) / 2 - s)) *
      (C₀ ^ (1 - s) * (ENNReal.ofReal (2 * Real.pi) * C₁) ^ s) := by
  have he : ENNReal.ofReal ε ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hε)
  rw [← ENNReal.ofReal_rpow_of_pos hε,
    ← ENNReal.ofReal_rpow_of_pos hε,
    mul_left_comm (ENNReal.ofReal (2 * Real.pi))]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr hs1),
    ENNReal.mul_rpow_of_nonneg _ _ hs0,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  calc
    _ = ((ENNReal.ofReal ε) ^ ((1 / 2 : ℝ) * (1 - s)) *
          (ENNReal.ofReal ε) ^ ((-(1 : ℝ) / 2) * s)) *
        (C₀ ^ (1 - s) * (ENNReal.ofReal (2 * Real.pi) * C₁) ^ s) := by ac_rfl
    _ = _ := by
      rw [← ENNReal.rpow_add _ _ he ENNReal.ofReal_ne_top,
        show (1 / 2 : ℝ) * (1 - s) + (-(1 : ℝ) / 2) * s = 1 / 2 - s by ring,
        ENNReal.ofReal_rpow_of_pos hε]

theorem insertion_force_periodic_L1_power_bound
    (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hv : ContDiff ℝ ∞ v) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0,
      eLpNorm (fun t => periodicVectorSobolevNorm s
        (periodize (InsertionFamily.force ν f v 0 T θ η ε)) t) 1 volume ≤
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2 - s)) * C := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hb⟩ :=
    eventually_actual_insertion_vector_periodized_endpoint_bound
      ν hf hfc hv T hθ hη hθc hηc hs0 hs1
  let C : ℝ≥0∞ := 3 * (C₀ ^ (1 - s) * (ENNReal.ofReal (2 * Real.pi) * C₁) ^ s)
  have hC : C < ⊤ := by
    apply ENNReal.mul_lt_top (by norm_num)
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hs1) hC₀.ne)
      (ENNReal.rpow_lt_top_of_nonneg hs0
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC₁).ne)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, self_mem_nhdsWithin] with ε hε hpos
  refine hε.trans_eq ?_
  rw [endpoint_power_product_eq hpos hs0 hs1]
  dsimp [C]
  ac_rfl

theorem insertion_force_periodic_L1_tendsto_zero
    (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hv : ContDiff ℝ ∞ v) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {s : ℝ} (hs : s < 1 / 2) :
    Tendsto (fun ε : ℝ => eLpNorm (fun t => periodicVectorSobolevNorm s
      (periodize (InsertionFamily.force ν f v 0 T θ η ε)) t) 1 volume)
      (𝓝[>] 0) (𝓝 0) := by
  by_cases hs0 : s ≤ 0
  · exact PeriodicNonpositiveForce.insertion_force_periodic_L1_tendsto_zero
      hs0 ν hf hfc hv T hθ hη hθc hηc
  obtain ⟨C, hC, hb⟩ := insertion_force_periodic_L1_power_bound
    ν hf hfc hv T hθ hη hθc hηc (le_of_not_ge hs0) (by linarith)
  have hr : Tendsto (fun ε : ℝ => ε ^ ((1 : ℝ) / 2 - s)) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id.rpow_const_nhds_zero (sub_pos.mpr hs)).mono_left nhdsWithin_le_nhds
  have he := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hr) (Or.inr hC.ne)
  simp only [ENNReal.ofReal_zero, zero_mul] at he
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
    (Eventually.of_forall (fun _ => bot_le)) hb

end NSFormalization.Paper1.PeriodicInsertionPositiveConvergence
