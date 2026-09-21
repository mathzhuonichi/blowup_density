import Bindings.CompactClassDensity
import NSFormalization.Section4.R41.ClassFacts

/-!
# Corollary 4.5 for rapidly decaying forces

This file proves the `Y = forceClassRapid` instances of all three parametric
fields of `research/R45/Spec.lean`, together with its verbatim
`schwartzDensity` field.  It also combines the already-landed compact and new
rapid instances of `density` and `zeroIff` into the two guarded parametric
field statements.

The density proof follows the compact template.  A rapid target belongs to
`F_R` by R41 gap G2, and the R42 insertion remains rapidly decaying because
its difference from the target is compactly supported (gap G3).  The
regular-reference proof uses the same closure fact on the single insertion
record which simultaneously supplies exact lifespan, both norm limits, and
the expanding common history.  The Schwartz specialization is G4 followed by
`density_rapid`.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set Filter
open Contracts.V1 Contracts.V1.Data
open NSFormalization.Section4
open scoped ENNReal Topology

/-- The `Y = forceClassRapid` specialization of `RClassesAPI.density`, with
exactly the field's binder order. -/
theorem density_rapid :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        ∀ a : SpatialField, a ∈ initialClassR →
          s < criticalOrder q.toReal →
            RelativelyDense q s forceClassRapid
              (breakdownSetIn forceClassRapid ν a T) := by
  intro ν hν T hT q hq s a ha hs g hg r hr
  by_cases hLife : maximalLifespanR ν a g ≤ ENNReal.ofReal T
  · refine ⟨g, ⟨hg, hLife⟩, ?_⟩
    have hzero : forceSobolevENorm q s (0 : SpaceTimeField) = 0 := by
      change D01.forceSobolevENorm q s (0 : SpaceTimeField) = 0
      exact R41.forceSobolevENorm_zero q s
    simpa only [sub_self, hzero] using hr
  · have hlong := lt_of_not_ge hLife
    obtain ⟨P, L, hLa, hLg, hLT⟩ :=
      insertionLifespanV2_of_data ν hν T hT a ha g
        (R41.memForceR_of_memForceRapid hg) hlong
    have hs' : s < L.family.scaling.thresholds.exponent q.toReal 0 := by
      simpa only [L.family.scaling.thresholds.formula, sub_zero, criticalOrder] using hs
    have hsmall := (insertionFromData_forceConvergence L hLg q hq s hs').eventually
      (gt_mem_nhds hr)
    have hwindow : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ε ∈ Ioc (0 : ℝ) L.family.ε₀ :=
      Ioc_mem_nhdsGT L.family.eps_pos
    obtain ⟨ε, hε, hdist⟩ := (hwindow.and hsmall).exists
    refine ⟨L.family.force ε, ⟨?_, ?_⟩, hdist⟩
    · exact R41.memForceRapid_of_compact_difference L.family.g
        (L.family.force ε) (hLg.symm ▸ hg)
        (L.family.forceDifference_compact ε hε)
    · exact (insertionFromData_lifespan L hLa hLT ε hε).le

/-- The `Y = forceClassRapid` specialization of `RClassesAPI.zeroIff`, with
exactly the field's binder order. -/
theorem zeroIff_rapid :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        RelativelyDense q s forceClassRapid
            (breakdownSetIn forceClassRapid ν (fun _ => 0) T) ↔
          s < criticalOrder q.toReal := by
  intro ν hν T hT q hq s
  constructor
  · intro hdense
    by_contra hsub
    have hge : criticalOrder q.toReal ≤ s := le_of_not_gt hsub
    have hzero : (0 : SpaceTimeField) ∈ forceClassRapid := by
      refine ⟨contDiffOn_const, fun N k => ⟨0, fun t ht x => ?_⟩⟩
      simp
    rcases hq with rfl | rfl
    · have hthreshold :
          R41.rMainThresholds.exponent 1 0 ≤ s := by
        simpa [R41.rMainThresholds, NSFormalization.Paper3.forceExponent,
          criticalOrder] using hge
      obtain ⟨ρ, hρ, hbound⟩ :=
        R41.nonDensityZero_of_q R41.rMainThresholds 1 (Or.inl rfl)
          ν T hν hT s hthreshold
      rw [mainThresholds_forceSobolevENorm_eq] at hbound
      obtain ⟨f, hf, hdist⟩ := hdense 0 hzero (ENNReal.ofReal ρ)
        (ENNReal.ofReal_pos.mpr hρ)
      have hfR : f ∈ breakdownSetRZero ν T :=
        ⟨R41.memForceR_of_memForceRapid hf.1, hf.2⟩
      have hfR' : f ∈ R41.breakdownSetRZero ν T := by
        simpa only [R41.breakdownSetRZero, breakdownSetRZero,
          mainThresholds_breakdownSetR_eq] using hfR
      have hlower : ENNReal.ofReal ρ ≤ forceSobolevENorm 1 s f := by
        simpa using hbound f hfR'
      exact (not_lt_of_ge hlower) (by simpa only [sub_zero] using hdist)
    · have hthreshold :
          R41.rMainThresholds.exponent 2 0 ≤ s := by
        simpa [R41.rMainThresholds, NSFormalization.Paper3.forceExponent,
          criticalOrder] using hge
      obtain ⟨ρ, hρ, hbound⟩ :=
        R41.nonDensityZero_of_q R41.rMainThresholds 2 (Or.inr rfl)
          ν T hν hT s hthreshold
      rw [mainThresholds_forceSobolevENorm_eq] at hbound
      obtain ⟨f, hf, hdist⟩ := hdense 0 hzero (ENNReal.ofReal ρ)
        (ENNReal.ofReal_pos.mpr hρ)
      have hfR : f ∈ breakdownSetRZero ν T :=
        ⟨R41.memForceR_of_memForceRapid hf.1, hf.2⟩
      have hfR' : f ∈ R41.breakdownSetRZero ν T := by
        simpa only [R41.breakdownSetRZero, breakdownSetRZero,
          mainThresholds_breakdownSetR_eq] using hfR
      have hlower : ENNReal.ofReal ρ ≤ forceSobolevENorm 2 s f := by
        simpa using hbound f hfR'
      exact (not_lt_of_ge hlower) (by simpa only [sub_zero] using hdist)
  · intro hs
    exact density_rapid ν hν T hT q hq s (fun _ => 0)
      A04.zero_mem_initialClassR hs

/-- The `Y = forceClassRapid` specialization of
`RClassesAPI.regularReference`, with exactly the field's binder and conjunct
order. -/
theorem regularReference_rapid :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) →
        ∀ s : ℝ, s < criticalOrder q.toReal →
          ∀ a : SpatialField, a ∈ initialClassR →
            ∀ g : SpaceTimeField, g ∈ forceClassRapid →
              ∀ δ : ℝ, 0 < δ →
                ∀ v : ClassicalSolutionR ν a g (T + δ),
                  ∀ τ : ℝ, 0 ≤ τ → τ < T →
                    ∀ r η : ℝ≥0∞, 0 < r → 0 < η →
                      ∃ f : SpaceTimeField, f ∈ forceClassRapid ∧
                        ∃ u : ClassicalSolutionR ν a f T,
                          maximalLifespanR ν a f = ENNReal.ofReal T ∧
                          forceSobolevENorm q s (f - g) < r ∧
                          energyENorm T (u.velocity - v.velocity) < η ∧
                          (∀ t : ℝ, 0 ≤ t → t ≤ τ →
                            ∀ x : NavierStokes.ProblemStatement.Space,
                            u.velocity (t, x) = v.velocity (t, x)) := by
  intro ν hν T hT q hq s hs a ha g hg δ hδ v τ hτ0 hτT r η hr hη
  have hlong := (maximalPartial.regularThrough_iff ν a g T hT).mp
    ⟨δ, hδ, ⟨v⟩⟩
  obtain ⟨P, L, hLa, hLg, hLT⟩ :=
    insertionLifespanV2_of_data ν hν T hT a ha g
      (R41.memForceR_of_memForceRapid hg) hlong
  subst a
  subst g
  subst T
  have href : ∀ t ∈ Ico (0 : ℝ) L.family.T, ∀ x,
      L.family.v (t, x) = v.velocity (t, x) := by
    have heq := uniqueness.velocity_unique ν L.family.a L.family.g hν ha
      (R41.memForceR_of_memForceRapid hg) _ _ L.family.reference v
    intro t ht x
    have hm : 0 < L.family.margin := L.family.scaling.correction.margin_pos
    have ht' : t ∈ Ico (0 : ℝ)
        (min (L.family.T + L.family.margin) (L.family.T + δ)) :=
      ⟨ht.1, lt_min (by linarith [ht.2]) (by linarith [ht.2])⟩
    have hv := heq t ht' x
    rw [L.family.reference_velocity] at hv
    exact hv
  have hforce := (insertionFromData_forceConvergence L rfl q hq s (by
    simpa only [L.family.scaling.thresholds.formula, sub_zero, criticalOrder]
      using hs)).eventually (gt_mem_nhds hr)
  have henergyConv :
      Tendsto
        (fun ε => energyENorm L.family.T
          (L.family.velocity ε - v.velocity))
        (𝓝[>] 0) (𝓝 0) := by
    have heq : ∀ ε,
        energyENorm L.family.T (L.family.velocity ε - v.velocity) =
          energyENorm L.family.T (L.family.velocity ε - L.family.v) := by
      intro ε
      apply mainThresholds_energy_congr
      intro t ht x
      change L.family.velocity ε (t, x) - v.velocity (t, x) =
        L.family.velocity ε (t, x) - L.family.v (t, x)
      rw [href t ⟨ht.1.le, ht.2⟩ x]
    simpa only [heq] using mainThresholds_energyConvergence L.family
  have henergy := henergyConv.eventually (gt_mem_nhds hη)
  let ετ : ℝ := min 1 ((L.family.T - τ) / 4)
  have hετ : 0 < ετ := by
    dsimp [ετ]
    exact lt_min (by norm_num) (by linarith)
  have hwindow : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ε ∈ Ioc (0 : ℝ) L.family.ε₀ :=
    Ioc_mem_nhdsGT L.family.eps_pos
  have hhistoryWindow : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ε ∈ Ioc (0 : ℝ) ετ := Ioc_mem_nhdsGT hετ
  obtain ⟨ε, hε, hεhist, hforceSmall, henergySmall⟩ :=
    (hwindow.and (hhistoryWindow.and (hforce.and henergy))).exists
  have hcutoff : τ ≤ L.family.T - 2 * ε ^ 2 := by
    have hε1 : ε ≤ 1 := le_trans hεhist.2 (min_le_left _ _)
    have hεgap : ε ≤ (L.family.T - τ) / 4 :=
      le_trans hεhist.2 (min_le_right _ _)
    have hsq : ε ^ 2 ≤ ε := by
      nlinarith [mul_nonneg hεhist.1.le (sub_nonneg.mpr hε1)]
    linarith
  obtain ⟨u, hu, _⟩ := L.solution ε hε
  refine ⟨L.family.force ε, ?_, u, L.lifespan ε hε, hforceSmall, ?_, ?_⟩
  · exact R41.memForceRapid_of_compact_difference L.family.g
      (L.family.force ε) hg (L.family.forceDifference_compact ε hε)
  · rw [hu]
    exact henergySmall
  · intro t ht0 htτ x
    rw [hu]
    exact (L.family.history ε hε t ht0 (le_trans htτ hcutoff) x).trans
      (href t ⟨ht0, lt_of_le_of_lt htτ hτT⟩ x)

/-- The verbatim `RClassesAPI.schwartzDensity` field, obtained from G4 and the
rapid-class density theorem. -/
theorem schwartzDensity :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        ∀ a : SpatialField, a ∈ initialClassSchwartz →
          s < criticalOrder q.toReal →
            RelativelyDense q s forceClassRapid
              (breakdownSetIn forceClassRapid ν a T) := by
  intro ν hν T hT q hq s a ha hs
  exact density_rapid ν hν T hT q hq s a
    (R41.initialClassSchwartz_subset_initialClassR ha) hs

/-- The complete guarded `RClassesAPI.density` field, assembled from the
compact and rapid instances. -/
theorem density :
    ∀ Y : Set SpaceTimeField, (Y = forceClassCompact ∨ Y = forceClassRapid) →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
          ∀ a : SpatialField, a ∈ initialClassR →
            s < criticalOrder q.toReal →
              RelativelyDense q s Y (breakdownSetIn Y ν a T) := by
  intro Y hY
  rcases hY with rfl | rfl
  · exact density_compact
  · exact density_rapid

/-- The complete guarded `RClassesAPI.zeroIff` field, assembled from the
compact and rapid instances. -/
theorem zeroIff :
    ∀ Y : Set SpaceTimeField, (Y = forceClassCompact ∨ Y = forceClassRapid) →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
          RelativelyDense q s Y
              (breakdownSetIn Y ν (fun _ => 0) T) ↔
            s < criticalOrder q.toReal := by
  intro Y hY
  rcases hY with rfl | rfl
  · exact zeroIff_compact
  · exact zeroIff_rapid

end BlowupDensity.Bindings
