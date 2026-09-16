import Bindings.CompactClassDensity

/-!
# Corollary 4.5: regular-reference riders

This file proves the `Y = forceClassCompact` specialization of the
`regularReference` field of `research/R45/Spec.lean`.  One R42 insertion record
supplies the exact lifespan, the inserted solution, the two norm limits, and
the expanding common history.  The scale is chosen small enough that its
history interval contains the caller's arbitrary cutoff `τ < T`.

The second theorem is the corresponding epsilon-form rider in the ambient
class `forceClassR`, derived from Theorem 4.1's registered family-and-limit
form.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set Filter
open Contracts.V1 Contracts.V1.Data
open NSFormalization.Section4
open scoped ENNReal Topology

/-- The `Y = forceClassCompact` specialization of
`RClassesAPI.regularReference`, with exactly the field's binder and conjunct
order. -/
theorem regularReference_compact :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) →
        ∀ s : ℝ, s < criticalOrder q.toReal →
          ∀ a : SpatialField, a ∈ initialClassR →
            ∀ g : SpaceTimeField, g ∈ forceClassCompact →
              ∀ δ : ℝ, 0 < δ →
                ∀ v : ClassicalSolutionR ν a g (T + δ),
                  ∀ τ : ℝ, 0 ≤ τ → τ < T →
                    ∀ r η : ℝ≥0∞, 0 < r → 0 < η →
                      ∃ f : SpaceTimeField, f ∈ forceClassCompact ∧
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
      (memForceR_of_memForceCompact hg) hlong
  subst a
  subst g
  subst T
  have href : ∀ t ∈ Ico (0 : ℝ) L.family.T, ∀ x,
      L.family.v (t, x) = v.velocity (t, x) := by
    have heq := uniqueness.velocity_unique ν L.family.a L.family.g hν ha
      (memForceR_of_memForceCompact hg) _ _ L.family.reference v
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
  · exact memForceCompact_add_memForceCompact hg
      (L.family.forceDifference_compact ε hε)
  · rw [hu]
    exact henergySmall
  · intro t ht0 htτ x
    rw [hu]
    exact (L.family.history ε hε t ht0 (le_trans htτ hcutoff) x).trans
      (href t ⟨ht0, lt_of_le_of_lt htτ hτT⟩ x)

/-- The epsilon-form regular-reference rider in the ambient force class
`forceClassR`, derived once from Theorem 4.1's registered Tendsto-form rider. -/
theorem regularReference_of_memForceR :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) →
        ∀ s : ℝ, s < criticalOrder q.toReal →
          ∀ a : SpatialField, a ∈ initialClassR →
            ∀ g : SpaceTimeField, g ∈ forceClassR →
              ∀ δ : ℝ, 0 < δ →
                ∀ v : ClassicalSolutionR ν a g (T + δ),
                  ∀ τ : ℝ, 0 ≤ τ → τ < T →
                    ∀ r η : ℝ≥0∞, 0 < r → 0 < η →
                      ∃ f : SpaceTimeField, f ∈ forceClassR ∧
                        ∃ u : ClassicalSolutionR ν a f T,
                          maximalLifespanR ν a f = ENNReal.ofReal T ∧
                          forceSobolevENorm q s (f - g) < r ∧
                          energyENorm T (u.velocity - v.velocity) < η ∧
                          (∀ t : ℝ, 0 ≤ t → t ≤ τ →
                            ∀ x : NavierStokes.ProblemStatement.Space,
                            u.velocity (t, x) = v.velocity (t, x)) := by
  intro ν hν T hT q hq s hs a ha g hg δ hδ v τ hτ0 hτT r η hr hη
  obtain ⟨ε₀, hε₀, f, w, hall, hforce, henergy⟩ :=
    mainThresholds.regularReferenceApproximation ν hν T hT q hq s hs
      a ha g hg δ hδ v
  let ετ : ℝ := min (ε₀ / 2) (min 1 ((T - τ) / 4))
  have hετ : 0 < ετ := by
    dsimp [ετ]
    exact lt_min (by linarith) (lt_min (by norm_num) (by linarith))
  have hwindow : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioc (0 : ℝ) ετ :=
    Ioc_mem_nhdsGT hετ
  have hforceSmall := hforce.eventually (gt_mem_nhds hr)
  have henergySmall := henergy.eventually (gt_mem_nhds hη)
  obtain ⟨ε, hε, hfSmall, heSmall⟩ :=
    (hwindow.and (hforceSmall.and henergySmall)).exists
  have hεmain : ε ∈ Ioo (0 : ℝ) ε₀ :=
    ⟨hε.1, lt_of_le_of_lt hε.2
      (lt_of_le_of_lt (min_le_left _ _) (by linarith))⟩
  have hcutoff : τ ≤ T - 2 * ε ^ 2 := by
    have hε1 : ε ≤ 1 :=
      le_trans hε.2 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hεgap : ε ≤ (T - τ) / 4 :=
      le_trans hε.2 (le_trans (min_le_right _ _) (min_le_right _ _))
    have hsq : ε ^ 2 ≤ ε := by
      nlinarith [mul_nonneg hε.1.le (sub_nonneg.mpr hε1)]
    linarith
  obtain ⟨hf, hlife, u, hu, hhistory⟩ := hall ε hεmain
  refine ⟨f ε, hf, u, hlife, hfSmall, ?_, ?_⟩
  · rw [hu]
    exact heSmall
  · intro t ht0 htτ x
    rw [hu]
    exact hhistory t ⟨ht0, le_trans htτ hcutoff⟩ x

end BlowupDensity.Bindings
