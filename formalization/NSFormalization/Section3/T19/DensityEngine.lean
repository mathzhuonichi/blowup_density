import NSFormalization.Section3.T19.Threading
import NSFormalization.Section3.T19.Density

/-!
# T19 density engine

The fixed-initial and mixed density statements use the same lifespan
dichotomy.  In the regular branch, the T19 insertion supplies a nearby force
with lifespan exactly the prescribed time.
-/

noncomputable section

namespace NSFormalization.Section3.T19

open Set Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T15
open scoped ENNReal Topology

/-- `PeriodicDensityAPI.fixedInitialDensity` (U7). -/
theorem fixedInitialDensity :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T) := by
  intro a ha ν hν T hT s hs g hg r hr
  by_cases hLife : maximalLifespanT ν a g ≤ ENNReal.ofReal T
  · refine ⟨g, ⟨hg, hLife⟩, ?_⟩
    simpa only [sub_self, torusForceSobolevENorm_zero] using hr
  · have hlong : ENNReal.ofReal T < maximalLifespanT ν a g := lt_of_not_ge hLife
    have hreg : RegularThroughT ν a g T := by
      simp only [maximalLifespanT, lt_iSup_iff] at hlong
      obtain ⟨S, hreference, hTS⟩ := hlong
      have hTS' : T < S :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hT.le).mp hTS
      refine ⟨S - T, sub_pos.mpr hTS', ?_⟩
      simpa using hreference
    obtain ⟨ρ, hρ0, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
    have hρ0' : 0 < (ρ : ℝ) := by exact_mod_cast hρ0
    obtain ⟨f, hf, hflife, hclose⟩ :=
      exists_force_close hν ha hg hT hreg s hs (ρ : ℝ) hρ0'
    refine ⟨f, ⟨hf, hflife.le⟩, hclose.trans ?_⟩
    simpa using hρr

/-- `PeriodicDensityAPI.regularReferenceSingular` (U8). -/
theorem regularReferenceSingular :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT → RegularThroughT ν a g T →
          ∀ s : ℝ, s < 1 / 2 → ∀ r : ℝ≥0∞, 0 < r →
            ∃ f ∈ forceClassT,
              forceSobolevENormT 1 s (fun z => f z - g z) < r ∧
                maximalLifespanT ν a f = ENNReal.ofReal T := by
  intro a ha ν hν T hT g hg hreg s hs r hr
  obtain ⟨ρ, hρ0, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  have hρ0' : 0 < (ρ : ℝ) := by exact_mod_cast hρ0
  obtain ⟨f, hf, hflife, hclose⟩ :=
    exists_force_close hν ha hg hT hreg s hs (ρ : ℝ) hρ0'
  exact ⟨f, hf, hclose.trans (by simpa using hρr), hflife⟩

/-- `MixedRegionAPI.mixedDensity` (U9). -/
theorem mixedDensity :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
          3 < 3 / p.toReal + 2 / q.toReal →
            RelativelyDenseMixedT q p forceClassT (breakdownSetT ν a T) := by
  intro a ha ν hν T hT p q _ hq hpq g hg r hr
  by_cases hLife : maximalLifespanT ν a g ≤ ENNReal.ofReal T
  · refine ⟨g, ⟨hg, hLife⟩, ?_⟩
    rw [show (fun z => g z - g z) = (0 : SpaceTimeField) by
      funext z
      exact sub_self (g z)]
    simpa only [torusMixedLebesgueENormT_zero] using hr
  · have hlong : ENNReal.ofReal T < maximalLifespanT ν a g := lt_of_not_ge hLife
    have hreg : RegularThroughT ν a g T := by
      simp only [maximalLifespanT, lt_iSup_iff] at hlong
      obtain ⟨S, hreference, hTS⟩ := hlong
      have hTS' : T < S :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hT.le).mp hTS
      refine ⟨S - T, sub_pos.mpr hTS', ?_⟩
      simpa using hreference
    obtain ⟨δ, hδ, ⟨reference⟩⟩ := hreg
    let A := insertion hν ha hg hT hδ reference
    have hα := mixedRegionArithmetic p q hpq
    have hpow₀ : Tendsto (fun ε : ℝ => ε ^ alphaT p q) (𝓝 0) (𝓝 0) := by
      simpa only [id_eq] using
        (Filter.tendsto_id.rpow_const_nhds_zero hα.1)
    have hpow₁ : Tendsto (fun ε : ℝ => ε ^ (alphaT p q + 1)) (𝓝 0) (𝓝 0) := by
      simpa only [id_eq] using
        (Filter.tendsto_id.rpow_const_nhds_zero hα.2)
    have hreal : Tendsto
        (fun ε : ℝ => A.forceDiffMixedConst p q *
          (ε ^ alphaT p q + ε ^ (alphaT p q + 1)))
        (𝓝 0) (𝓝 0) := by
      simpa using (hpow₀.add hpow₁).const_mul (A.forceDiffMixedConst p q)
    have hupper : Tendsto
        (fun ε : ℝ => ENNReal.ofReal (A.forceDiffMixedConst p q *
          (ε ^ alphaT p q + ε ^ (alphaT p q + 1))))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
      simpa only [ENNReal.ofReal_zero] using
        (ENNReal.tendsto_ofReal hreal).mono_left nhdsWithin_le_nhds
    have hconv : Tendsto
        (fun ε : ℝ => mixedLebesgueENormT q p
          (fun z => A.force ε z - g z))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      · exact Eventually.of_forall (fun _ => bot_le)
      · filter_upwards [Ioc_mem_nhdsGT A.eps_pos] with ε hε
        exact A.forceDifference_mixed_bound p q hq ε hε
    have hclose := hconv.eventually (gt_mem_nhds hr)
    have hwindow : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioc (0 : ℝ) A.ε₀ :=
      Ioc_mem_nhdsGT A.eps_pos
    obtain ⟨ε, hε, hdist⟩ := (hwindow.and hclose).exists
    exact ⟨A.force ε, ⟨A.force_mem ε hε, (A.lifespan ε hε).le⟩, hdist⟩

end NSFormalization.Section3.T19
