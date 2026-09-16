import NSFormalization.Section4.A02.MaximalWiring
import NSFormalization.Section4.A04.Continuation
import NSFormalization.Section4.A01.GronwallEndpoint

/-! # Restart data and local solutions supplied by A01
The H¹-uniform lifespan restart is not identified with A01's fixed-force H⁷
bound. See `research/A04/ATTEMPTS_RESTART_WIRING.md` for the exact distinction.
-/
noncomputable section
namespace NSFormalization.Section4.A04
open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section4.A02
open scoped ENNReal ContDiff

/-- Positive translation sends the half-line measure to a smaller measure. -/
theorem map_forceTimeMeasure_shift_le {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Measure.map (fun t : ℝ => t + t₀) forceTimeMeasure ≤ forceTimeMeasure := by
  apply Measure.le_iff.mpr
  intro s hs
  have hm : Measurable (fun t : ℝ => t + t₀) := measurable_id.add_const t₀
  rw [Measure.map_apply hm hs]
  change volume.restrict (Ioi (0 : ℝ)) ((fun t : ℝ => t + t₀) ⁻¹' s) ≤
    volume.restrict (Ioi (0 : ℝ)) s
  rw [Measure.restrict_apply (hm hs), Measure.restrict_apply hs]
  calc
    volume ((fun t : ℝ => t + t₀) ⁻¹' s ∩ Ioi 0) ≤
        volume ((fun t : ℝ => t + t₀) ⁻¹' (s ∩ Ioi 0)) := by
      apply measure_mono
      intro t ht
      exact ⟨ht.1, add_pos_of_pos_of_nonneg ht.2 ht₀⟩
    _ = volume (s ∩ Ioi 0) :=
      (measurePreserving_add_right (volume : Measure ℝ) t₀).measure_preimage
        (hs.inter measurableSet_Ioi).nullMeasurableSet

/-- Full force-class closure, including both L¹ and L² at every order. -/
theorem restart_force (f : SpaceTimeField) (hf : MemForceR f)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) : MemForceR (timeShift t₀ f) := by
  refine ⟨hf.1.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn
    (fun z hz => ?_), ?_⟩
  · exact ⟨add_nonneg hz.1 ht₀, mem_univ _⟩
  · intro m
    obtain ⟨G, hG, hGc, hG1, hG2⟩ := hf.2 m
    refine ⟨fun t => G (t + t₀), (fun t ht => hG (t + t₀) (add_nonneg ht ht₀)),
      hGc.comp (contDiff_id.add contDiff_const).contDiffOn
        (fun t ht => add_nonneg ht ht₀), ?_, ?_⟩
    · exact (hG1.mono_measure (map_forceTimeMeasure_shift_le ht₀)).comp_of_map
        (measurable_id.add_const t₀).aemeasurable
    · exact (hG2.mono_measure (map_forceTimeMeasure_shift_le ht₀)).comp_of_map
        (measurable_id.add_const t₀).aemeasurable

/-- An actual local solution of the shifted problem at every presingular time.
This does not assert a uniform duration or a concatenated solution. -/
theorem local_restart (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f)
    (u : SpaceTimeField) (p : SpaceTimeScalar) (hu : IsMaximalSolution ν a f u p)
    (t₀ : ℝ) (ht₀ : t₀ ∈ presingularTimes ν a f) :
    Nonempty (ClassicalSolutionR ν (fun x : Space => u (t₀, x)) (timeShift t₀ f)
      (A01.localHorizon' ν (fun x : Space => u (t₀, x)) (timeShift t₀ f))) :=
  ⟨(A01.localCarrier ν _ _ hν (restart_datum ν a f hν ha hf u p hu t₀ ht₀)
    (restart_force f hf t₀ ht₀.1)).w⟩

/-- The regularity of the selected local solution supplies A04's path input. -/
theorem localCarrier_hasSmoothSobolevPath (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) :
    HasSmoothSobolevPath (A01.localHorizon' ν a f)
      (A01.localCarrier ν a f hν ha hf).w.velocity :=
  (A01.manuscriptLocalRegularity_localCarrier ν a f hν ha hf).sobolev_smooth

/-- For a fixed shifted force, every datum in an H⁷ ball has a local solution
on the same positive horizon. The shift is fixed before choosing the horizon. -/
theorem uniform_local_restart_H7 (ν : ℝ) (hν : 0 < ν)
    (f : SpaceTimeField) (hf : MemForceR f) (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : SpatialField, a ∈ initialClassR →
      D01.sobolevENorm 7 a ≤ K →
      Nonempty (ClassicalSolutionR ν a (timeShift t₀ f) δ) := by
  have hshift := restart_force f hf t₀ ht₀
  obtain ⟨δ, hδ, hbound⟩ := A01.horizon_lower_bound_H7_fixedForce ν hν
    (timeShift t₀ f) hshift K hK
  refine ⟨δ, hδ, ?_⟩
  intro a ha hnorm
  exact ⟨(A01.localCarrier ν a (timeShift t₀ f) hν ha hshift).w.restrict hδ
    (hbound a ha hnorm)⟩

end NSFormalization.Section4.A04
