import Contracts.V1.MainThresholds
import Bindings.DensityFromInsertion
import NSFormalization.Section4.R41.NonDensity

/-! Theorem 4.1: lanes 232/235 supply density, and one lane-233 record supplies
all rider conclusions. The reference is transported only on the presingular slab. -/
noncomputable section
namespace BlowupDensity.Bindings
open Set Filter MeasureTheory
open Contracts.V1 Contracts.V1.Data
open NSFormalization.Section4
open scoped ENNReal Topology

/-- The local force class and norm are the registered definitions. -/
theorem mainThresholds_forceClassR_eq : R41.forceClassR = forceClassR := rfl

theorem mainThresholds_forceSobolevENorm_eq :
    NSFormalization.Section4.D01.forceSobolevENorm = forceSobolevENorm := rfl

/-- The solution structures differ; transport lifespan through the A02 bridge. -/
theorem mainThresholds_breakdownSetR_eq : R41.breakdownSetR = breakdownSetR := by
  funext ν a T
  unfold R41.breakdownSetR R41.breakdownSetIn breakdownSetR breakdownSetIn
  simp only [maximalPartial_maximalLifespanR_eq]
  rfl

theorem mainThresholds_BreakdownDenseR_eq : R41.BreakdownDenseR = BreakdownDenseR := by
  funext ν a T q s
  unfold R41.BreakdownDenseR BreakdownDenseR
  rw [mainThresholds_breakdownSetR_eq]
  rfl

/-- Real-q supplier transported to the two registered ENNReal exponents. -/
theorem mainThresholds_nonDensity (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T)
    (q : ℝ≥0∞) (hq : q = 1 ∨ q = 2) (s : ℝ)
    (hs : criticalOrder q.toReal ≤ s) : ¬ BreakdownDenseR ν (fun _ => 0) T q s := by
  rcases hq with rfl | rfl
  · have h := R41.not_breakdownDenseR_zero_of_q R41.rMainThresholds
      1 (Or.inl rfl) ν T hν hT s
    rw [mainThresholds_BreakdownDenseR_eq] at h
    apply (by simpa using h)
    simpa [R41.rMainThresholds, NSFormalization.Paper3.forceExponent, criticalOrder] using hs
  · have h := R41.not_breakdownDenseR_zero_of_q R41.rMainThresholds
      2 (Or.inr rfl) ν T hν hT s
    rw [mainThresholds_BreakdownDenseR_eq] at h
    apply (by simpa using h)
    simpa [R41.rMainThresholds, NSFormalization.Paper3.forceExponent, criticalOrder] using hs

/-- Energy only sees spatial slices at times in `(0,T)`, including their derivatives. -/
theorem mainThresholds_energy_congr {T : ℝ} {u v : SpaceTimeField}
    (h : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, u (t, x) = v (t, x)) :
    energyENorm T u = energyENorm T v := by
  have hs : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
      (fun x => u (t, x)) = (fun x => v (t, x)) :=
    (ae_restrict_mem measurableSet_Ioo).mono fun t ht => funext (h t ht)
  unfold energyENorm energyEssSup energyGradient
  congr 1
  · exact essSup_congr_ae (hs.mono fun t ht => by dsimp only; rw [ht])
  · congr 1
    apply lintegral_congr_ae
    filter_upwards [hs] with t ht
    simp only [spatialGradient, NavierStokes.ProblemStatement.spatialDerivative, ht]

/-- The registered quantitative energy bound implies the qualitative limit. -/
theorem mainThresholds_energyConvergence {ν : ℝ} {P : PacketAPI ν}
    (F : InsertionFamilyAPI ν P) :
    Tendsto (fun ε => energyENorm F.T (F.velocity ε - F.v)) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (fun ε : ℝ => ENNReal.ofReal
      ((P.energyBound + P.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        F.scaling.correctionEnergyConst * ε ^ ((3 : ℝ) / 2))) :=
    ENNReal.continuous_ofReal.comp
      ((continuous_const.mul (Real.continuous_rpow_const (by norm_num))).add
        (continuous_const.mul (Real.continuous_rpow_const (by norm_num))))
  have hz : Tendsto (fun ε : ℝ => ENNReal.ofReal
      ((P.energyBound + P.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        F.scaling.correctionEnergyConst * ε ^ ((3 : ℝ) / 2))) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz
    (Eventually.of_forall fun _ => zero_le)
  have hw : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioc (0 : ℝ) F.ε₀ :=
    Ioc_mem_nhdsGT F.eps_pos
  exact hw.mono fun ε hε => F.energyRate ε hε

/-- Complete, statement-faithful witness of the reconciled four-field API. -/
theorem mainThresholds : MainThresholds.MainThresholdsAPI where
  fixedInitialDensity := fun ν hν T hT q hq s a ha hs =>
    breakdownDenseR_of_subcritical ν T hν hT q hq s hs a ha
  zeroInitialDensityIff := by
    intro ν hν T hT q hq s
    constructor
    · intro hd
      by_contra hs
      exact mainThresholds_nonDensity ν T hν hT q hq s (le_of_not_gt hs) hd
    · intro hs
      exact breakdownDenseR_zero_of_subcritical ν T hν hT q hq s hs
  thresholdValues := by norm_num [criticalOrder]
  regularReferenceApproximation := by
    intro ν hν T hT q hq s hs a ha g hg δ hδ v
    have hlong := (maximalPartial.regularThrough_iff ν a g T hT).mp ⟨δ, hδ, ⟨v⟩⟩
    obtain ⟨P, L, hLa, hLg, hLT⟩ :=
      insertionLifespanV2_of_data ν hν T hT a ha g hg hlong
    subst a
    subst g
    subst T
    have href : ∀ t ∈ Ico (0 : ℝ) L.family.T, ∀ x,
        L.family.v (t, x) = v.velocity (t, x) := by
      have heq := uniqueness.velocity_unique ν L.family.a L.family.g hν ha hg
        _ _ L.family.reference v
      intro t ht x
      have hm : 0 < L.family.margin := L.family.scaling.correction.margin_pos
      have ht' : t ∈ Ico (0 : ℝ)
          (min (L.family.T + L.family.margin) (L.family.T + δ)) :=
        ⟨ht.1, lt_min (by linarith [ht.2]) (by linarith [ht.2])⟩
      have hv := heq t ht' x
      rw [L.family.reference_velocity] at hv
      exact hv
    refine ⟨L.family.ε₀, L.family.eps_pos, L.family.force, L.family.velocity, ?_, ?_, ?_⟩
    · intro ε hε
      have he : ε ∈ Ioc (0 : ℝ) L.family.ε₀ := ⟨hε.1, hε.2.le⟩
      refine ⟨InsertionLifespan.memForceR_force L.family L.memForce he,
        L.lifespan ε he, ?_⟩
      obtain ⟨U, hu, _⟩ := L.solution ε he
      refine ⟨U, hu, ?_⟩
      intro t ht x
      have htT : t < L.family.T := by nlinarith [sq_pos_of_pos hε.1, ht.2]
      exact (L.family.history ε he t ht.1 ht.2 x).trans (href t ⟨ht.1, htT⟩ x)
    · apply insertionFromData_forceConvergence L rfl q hq s
      simpa only [L.family.scaling.thresholds.formula, sub_zero, criticalOrder] using hs
    · have heq : ∀ ε, energyENorm L.family.T (L.family.velocity ε - v.velocity) =
          energyENorm L.family.T (L.family.velocity ε - L.family.v) := by
        intro ε
        apply mainThresholds_energy_congr
        intro t ht x
        change L.family.velocity ε (t, x) - v.velocity (t, x) =
          L.family.velocity ε (t, x) - L.family.v (t, x)
        rw [href t ⟨ht.1.le, ht.2⟩ x]
      simpa only [heq] using mainThresholds_energyConvergence L.family
end BlowupDensity.Bindings
