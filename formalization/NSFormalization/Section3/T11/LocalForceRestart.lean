import NSFormalization.Section3.T11.LocalForceBounds
import NSFormalization.Section4.A01.LocalForce

/-! Periodic restart for smooth forces with no temporal support requirement.
Cutting off after a fixed restart window supplies a single uniform local
horizon while preserving the original force on that window. -/
noncomputable section
namespace NSFormalization.Section3.T11
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar forceTimeMeasure)
open NSFormalization.Section4.A01 (localTimeCutoff localTimeCutoff_eq_one)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal

local instance localRestartNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance localRestartNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-- The equation depends only on the force during the solution's lifespan. -/
def withForceT {ν T : ℝ} {a : SpatialField} {f g : SpaceTimeField}
    (w : ClassicalSolutionT ν a g T)
    (hfg : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space, g (t, x) = f (t, x)) :
    ClassicalSolutionT ν a f T :=
  { w with momentum := fun t ht x => (w.momentum t ht x).trans (hfg t ht x) }

/-- A time cutoff supplies finite norms at every order without requiring the
force to vanish near time zero. -/
theorem periodic_cutoff_force {f : SpaceTimeField} (hf : ContDiff ℝ ∞ f)
    (hp : IsPeriodicOn univ f) (S : ℝ) :
    ∃ g : SpaceTimeField, ContDiff ℝ ∞ g ∧ IsPeriodicOn univ g ∧
      (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≠ ⊤) ∧
      ∀ t ∈ Icc (0 : ℝ) S, ∀ x : Space, g (t, x) = f (t, x) := by
  let g : SpaceTimeField := fun z => localTimeCutoff S z.1 • f z
  have hgs : ContDiff ℝ ∞ g :=
    ((localTimeCutoff S).contDiff.comp contDiff_fst).smul hf
  have hgp : IsPeriodicOn univ g := by
    intro t ht x i
    change localTimeCutoff S t • f (t, x + coordinateVector i) = _
    rw [hp t ht x i]
  refine ⟨g, hgs, hgp, ?_, ?_⟩
  · intro m
    obtain ⟨G, hGc, hG⟩ := exists_smooth_forceDatumPath hgs hgp m
    have hz : IsPeriodicDatum (m : ℝ) (0 : SpatialField) (0 : PeriodicSobolev (m : ℝ)) := by
      refine ⟨fun _ _ => rfl, ?_, ?_⟩
      · exact integrable_const (0 : Space)
      · intro i k
        change (0 : ℂ) = periodicFrequencyWeight k ^ ((m : ℝ) / 2) •
          periodicFourierCoeff (fun _ : Space => (0 : ℂ)) k
        rw [periodicFourierCoeff_const]
        simp
    have hcompact : HasCompactSupport G := by
      apply HasCompactSupport.of_support_subset_isCompact (localTimeCutoff S).hasCompactSupport
      intro t ht
      apply subset_tsupport
      intro hzero
      have hdatum : IsPeriodicDatum (m : ℝ) (0 : SpatialField) (G t) := by
        change IsPeriodicDatum (m : ℝ) (fun _ : Space => 0) (G t)
        simpa only [g, hzero, zero_smul] using hG t
      exact ht (datum_unique (m : ℝ) 0 (G t) 0 hdatum hz)
    have hmem : MemLp G 1 forceTimeMeasure := hGc.continuous.memLp_of_hasCompactSupport hcompact
    exact ne_top_of_le_ne_top hmem.2.ne (iInf_le_of_le
      ⟨G, (fun t _ => hG t), hmem.1⟩ le_rfl)
  · intro t ht x
    simp only [g, localTimeCutoff_eq_one ht, one_smul]

/-- One positive horizon works for all restart times in a fixed compact
window and all smooth data in a bounded `H³` ball. -/
theorem restartH3_smoothForceT
    (ν : ℝ) (hν : 0 < ν) (f : SpaceTimeField) (hf : ContDiff ℝ ∞ f)
    (hp : IsPeriodicOn univ f) (S : ℝ) (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t₀ ∈ Icc (0 : ℝ) S,
      ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 3 a ≤ K →
        Nonempty (ClassicalSolutionT ν a (timeShiftT t₀ f) δ) := by
  obtain ⟨g, hgs, hgp, hgfinite, hgf⟩ := periodic_cutoff_force hf hp (S + 1)
  obtain ⟨d, hd, hlocal⟩ := periodicQuantitativeLocalInputH3 ν hν K hK
    (fun m => forceSobolevENormT 1 (m : ℝ) g) hgfinite
  have hδ : 0 < min d 1 := lt_min hd zero_lt_one
  refine ⟨min d 1, hδ, ?_⟩
  intro t₀ ht₀ a ha hKa
  obtain ⟨w, _⟩ := hlocal a ha hKa (timeShiftT t₀ g)
    (timeShiftT_contDiff hgs t₀) (timeShiftT_periodic hgp t₀)
    (fun m => forceSobolevENormT_timeShift_le (m : ℝ) g t₀ ht₀.1)
  refine ⟨withForceT (restrictClassicalSolutionT w hδ (min_le_left _ _)) ?_⟩
  intro t ht x
  exact hgf (t + t₀) ⟨by linarith [ht.1, ht₀.1],
    by linarith [ht.2, ht₀.2, min_le_right d 1]⟩ x

end NSFormalization.Section3.T11
