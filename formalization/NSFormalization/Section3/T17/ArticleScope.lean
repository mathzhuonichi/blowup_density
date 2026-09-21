import NSFormalization.Section3.T19.Threading

/-!
# Lemma 3.5 with a classical reference

`paper/revised/sections/03-torus.tex:153-176`: “For $w_\eps$ in
Lemma~\ref{lem:potential}, define” $H_\eps$ by (H); “All constants are
independent of sufficiently small $\eps$.” We retain every bound in
(derivativebounds), (wE), (Hmixed), and (HHs), including both Sobolev terms.
Lines 135-139 specify the coordinate ball and the time support.

G5: `reference_periodic` prevents using the original velocity directly:
a classical solution has no constraints outside its lifespan. The potential
record also fixes its radial formula at every time; we retain that formula
for the zero extension and identify it with the article formula on the slab. The zero extension agrees on the entire classical slab. The force
agrees globally because the correction is supported strictly inside that slab.
Placement contains geometry, not the raw velocity support clause; that clause
is therefore explicit here (and is a projection of the registered packet).
-/
noncomputable section
namespace NSFormalization.Section3.T17
open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T15
open NSFormalization.Section3.T16 NSFormalization.Section3.T19
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open scoped ContDiff ENNReal

def correctionStatementArticle : Prop :=
  ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (place : PlacementData u p f K)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (reference : ClassicalSolutionT ν a g (place.T + δ)),
    0 < ν → 0 < r → r < 1 / 2 → 0 < δ →
    a ∈ initialClassT → g ∈ forceClassT →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t, x)) ⊆ K) →
    ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius →
    (∃ D : CutoffData,
      LocalPotentialAPI (extendByZero reference).velocity u place.Kstar place.x₀ r place.T δ D ∧
      Nonempty (CorrectionAPI ν place (extendByZero reference).velocity r δ D)) ∧
    ∀ t ∈ Ico (0 : ℝ) (place.T + δ), ∀ x,
      (extendByZero reference).velocity (t, x) = reference.velocity (t, x)

theorem correctionStatementArticle_holds : correctionStatementArticle := by
  intro ν u p f K place a g r δ reference hν hr hr2 hδ _ha _hg hsupp hball
  refine ⟨?_, fun t ht x => extendByZero_velocity_eqOn reference ⟨ht, mem_univ x⟩⟩
  exact correctionStatementSlab'_holds ν u p f K place _ r δ hν hr hr2 hδ
    (extendByZero_periodic reference) (extendByZero_smooth reference)
    (fun t ht x _ => (extendByZero reference).divergence t ⟨ht.1.le, ht.2⟩ x)
    hsupp hball

variable {ν : ℝ} {u : VelocityField} {p : PressureField} {f : VelocityField}
  {K : Set Space} {place : PlacementData u p f K} {a : SpatialField}
  {g : SpaceTimeField} {r δ : ℝ}
  {reference : ClassicalSolutionT ν a g (place.T + δ)} {D : CutoffData}
  (A : CorrectionAPI ν place (extendByZero reference).velocity r δ D)

include A

theorem article_window_identification (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) D.ε₀)
    (t : ℝ) (ht : |t - place.T| ≤ 2 * ε ^ 2) (x : Space) :
    (extendByZero reference).velocity (t, x) = reference.velocity (t, x) := by
  have hb := A.potential.eps_time ε hε
  have hT := lt_of_lt_of_le hb (min_le_left _ _)
  have hδ := lt_of_lt_of_le hb (min_le_right _ _)
  rw [abs_le] at ht
  exact extendByZero_velocity_eqOn reference
    ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, mem_univ x⟩

theorem article_force_identification (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) D.ε₀) :
    correctionForce ν (extendByZero reference).velocity D ε =
      correctionForce ν reference.velocity D ε := by
  apply correctionForce_eq_of_slices rfl (A.potential.correction_support ε hε)
  intro t ht x
  apply article_window_identification A ε hε t _ x
  rw [abs_le]
  constructor <;> linarith [ht.1, ht.2]

/-- Lemma 3.5: force smooth, with the article reference. -/
theorem article_force_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiff ℝ ∞ (correctionForce ν reference.velocity D ε) := by
  intro ε hε
  rw [← article_force_identification A ε hε]
  exact A.force_smooth ε hε

/-- Lemma 3.5: force periodic, with the article reference. -/
theorem article_force_periodic : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    IsPeriodicOn univ (correctionForce ν reference.velocity D ε) := by
  intro ε hε
  rw [← article_force_identification A ε hε]
  exact A.force_periodic ε hε

/-- Lemma 3.5: force support, with the article reference. -/
theorem article_force_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (correctionForce ν reference.velocity D ε) ⊆
      Ioo (place.T - 2 * ε ^ 2) (place.T + 2 * ε ^ 2) ×ˢ
        periodicSet (Metric.ball place.x₀ (ε * D.θRadius)) := by
  intro ε hε
  rw [← article_force_identification A ε hε]
  exact A.force_support ε hε

/-- Lemma 3.5: force spatial volume, with the article reference. -/
theorem article_force_spatial_volume : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    periodicTorusMeasure (torusSpatialSupport (correctionForce ν reference.velocity D ε)) ≤
      ENNReal.ofReal (A.spatialVolumeConst * ε ^ 3) := by
  intro ε hε
  rw [← article_force_identification A ε hε]
  exact A.force_spatial_volume ε hε

/-- Lemma 3.5: force time length, with the article reference. -/
theorem article_force_time_length : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    volume (torusTemporalSupport (correctionForce ν reference.velocity D ε)) ≤
      ENNReal.ofReal (4 * ε ^ 2) := by
  intro ε hε
  rw [← article_force_identification A ε hε]
  exact A.force_time_length ε hε

/-- Lemma 3.5: correction derivative bound, with the article reference. -/
theorem article_correction_derivative_bound : ∀ j m : ℕ,
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
      ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ (j + m) (D.correction ε) z
            (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space)))
              (fun i => ((0 : ℝ), u i)))‖ ≤
          A.correctionDerivConst j m * (ε⁻¹) ^ (2 * j + m) := by
  exact A.correction_derivative_bound

/-- Lemma 3.5: force derivative bound, with the article reference. -/
theorem article_force_derivative_bound : ∀ m : ℕ,
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
      ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ m (correctionForce ν reference.velocity D ε) z
            (fun i => ((0 : ℝ), u i))‖ ≤
          A.forceDerivConst m * (ε⁻¹) ^ (2 + m) := by
  intro m ε hε
  rw [← article_force_identification A ε hε]
  exact A.force_derivative_bound m ε hε

/-- Lemma 3.5: correction energy bound, with the article reference. -/
theorem article_correction_energy_bound : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    energyENormT place.T (D.correction ε) ≤
      ENNReal.ofReal (A.energyConst * ε ^ ((3 : ℝ) / 2)) := by
  exact A.correction_energy_bound

/-- Lemma 3.5: force spatial memLp, with the article reference. -/
theorem article_force_spatial_memLp : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
      MemLp (torusLift (fun x => correctionForce ν reference.velocity D ε (t, x))) p
        periodicTorusMeasure := by
  intro p inst ε hε
  rw [← article_force_identification A ε hε]
  exact A.force_spatial_memLp p ε hε

/-- Lemma 3.5: force mixed bound, with the article reference. -/
theorem article_force_mixed_bound : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      mixedLebesgueENormT q p (correctionForce ν reference.velocity D ε) ≤
        ENNReal.ofReal
          (A.mixedConst p q * ε ^ (alphaT p q + 1)) := by
  intro p q inst hq ε hε
  rw [← article_force_identification A ε hε]
  exact A.force_mixed_bound p q hq ε hε

/-- Lemma 3.5: forceSobolev memLp, with the article reference. -/
theorem article_forceSobolev_memLp : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      MemForceSobolevT 1 s (correctionForce ν reference.velocity D ε) := by
  intro s hs0 hs1 ε hε
  rw [← article_force_identification A ε hε]
  exact A.forceSobolev_memLp s hs0 hs1 ε hε

/-- Lemma 3.5: force sobolev bound, with the article reference. -/
theorem article_force_sobolev_bound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      forceSobolevENormT 1 s (correctionForce ν reference.velocity D ε) ≤
        ENNReal.ofReal
          (A.sobolevConst s *
            (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s))) := by
  intro s hs0 hs1 ε hε
  rw [← article_force_identification A ε hε]
  exact A.force_sobolev_bound s hs0 hs1 ε hε

/-- Lemma 3.4, (potential), on the article reference's entire slab. -/
theorem article_potential_formula (t : ℝ) (ht : t ∈ Ico (0 : ℝ) (place.T + δ))
    (x : Space) :
    D.potential (t, x) = ∫ ρ in (0 : ℝ)..1,
      ρ • NSFormalization.Paper1.RadialPotential.cross (reference.velocity (t, place.x₀ + ρ • (x - place.x₀))) (x - place.x₀) := by
  rw [A.potential.potential_formula]
  congr 1
  funext ρ
  rw [extendByZero_velocity_eqOn reference ⟨ht, mem_univ _⟩]

/-- The correction profile reads only cutoff-window reference slices. -/
theorem article_correction_profile_identification (ε : ℝ)
    (hε : ε ∈ Ioc (0 : ℝ) D.ε₀) :
    rescaledCorrectionProfile (extendByZero reference).velocity place.x₀ place.T ε D =
      rescaledCorrectionProfile reference.velocity place.x₀ place.T ε D := by
  apply correctionProfile_eq_of_slices rfl rfl
  intro σ hσ x
  have hσ' := A.potential.eta_support (subset_tsupport D.η hσ)
  exact article_window_identification A ε hε _
    (chart_time_mem_window _ _ _ ⟨hσ'.1.le, hσ'.2.le⟩) x

/-- The force profile agrees globally, including outside its fixed cylinder. -/
theorem article_force_profile_identification (ε : ℝ)
    (hε : ε ∈ Ioc (0 : ℝ) D.ε₀) :
    rescaledForceProfile ν (extendByZero reference).velocity place.x₀ place.T ε D =
      rescaledForceProfile ν reference.velocity place.x₀ place.T ε D := by
  apply forceProfile_eq_of_slices (article_correction_profile_identification A ε hε)
  · rw [← article_correction_profile_identification A ε hε]
    exact A.correction_profile_support ε hε
  · intro σ hσ x
    exact article_window_identification A ε hε _ (chart_time_mem_window _ _ _ hσ) x

/-- Lemma 3.5 proof: correction profile smooth. -/
theorem article_correction_profile_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiffOn ℝ ∞ (rescaledCorrectionProfile reference.velocity place.x₀ place.T ε D)
      (fixedProfileCylinder D) := by
  intro ε hε
  rw [← article_correction_profile_identification A ε hε]
  exact A.correction_profile_smooth ε hε

/-- Lemma 3.5 proof: correction profile support. -/
theorem article_correction_profile_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (rescaledCorrectionProfile reference.velocity place.x₀ place.T ε D) ⊆ fixedProfileCylinder D := by
  intro ε hε
  rw [← article_correction_profile_identification A ε hε]
  exact A.correction_profile_support ε hε

/-- Lemma 3.5 proof: correction profile uniform. -/
theorem article_correction_profile_uniform : ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (rescaledCorrectionProfile reference.velocity place.x₀ place.T ε D) z‖ ≤
        A.correctionProfileConst k := by
  intro k ε hε
  rw [← article_correction_profile_identification A ε hε]
  exact A.correction_profile_uniform k ε hε

/-- Lemma 3.5 proof: force profile smooth. -/
theorem article_force_profile_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiffOn ℝ ∞ (rescaledForceProfile ν reference.velocity place.x₀ place.T ε D)
      (fixedProfileCylinder D) := by
  intro ε hε
  rw [← article_force_profile_identification A ε hε]
  exact A.force_profile_smooth ε hε

/-- Lemma 3.5 proof: force profile support. -/
theorem article_force_profile_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (rescaledForceProfile ν reference.velocity place.x₀ place.T ε D) ⊆ fixedProfileCylinder D := by
  intro ε hε
  rw [← article_force_profile_identification A ε hε]
  exact A.force_profile_support ε hε

/-- Lemma 3.5 proof: force profile uniform. -/
theorem article_force_profile_uniform : ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (rescaledForceProfile ν reference.velocity place.x₀ place.T ε D) z‖ ≤
        A.forceProfileConst k := by
  intro k ε hε
  rw [← article_force_profile_identification A ε hε]
  exact A.force_profile_uniform k ε hε

/-- Lemma 3.5 proof: correction profile identity. -/
theorem article_correction_profile_identity : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      D.correction ε (correctionChartPoint place.x₀ place.T ε z) =
        rescaledCorrectionProfile reference.velocity place.x₀ place.T ε D z := by
  intro ε hε
  rw [← article_correction_profile_identification A ε hε]
  exact A.correction_profile_identity ε hε

/-- Lemma 3.5 proof: force profile identity. -/
theorem article_force_profile_identity : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      correctionForce ν reference.velocity D ε (correctionChartPoint place.x₀ place.T ε z) =
        (ε ^ 2)⁻¹ • rescaledForceProfile ν reference.velocity place.x₀ place.T ε D z := by
  intro ε hε
  rw [← article_force_profile_identification A ε hε, ← article_force_identification A ε hε]
  exact A.force_profile_identity ε hε

end NSFormalization.Section3.T17
