import NSFormalization.Paper3.SobolevHilbertModel
import NSFormalization.Paper3.PositiveTemporalDensity

/-! Algebraic positive-time admissible force interface.

This deliberately uses the complex Hilbert realization currently available.  It
records the remaining real-distribution, angular-convention, and one-sided
smoothness bridges; it does not assert the full manuscript class.
-/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory NavierStokes.ProblemStatement
open scoped ContDiff ENNReal SchwartzMap

abbrev ForceDistribution := Fin 3 → 𝓢'(Space, ℂ)
abbrev ForceDatum (m : ℕ) := Fin 3 → SobolevHilbert (m : ℝ)

def forceRealization (m : ℕ) : ForceDatum m →L[ℂ] ForceDistribution :=
  ContinuousLinearMap.pi (fun i => (sobolevRealization (m : ℝ)).comp (ContinuousLinearMap.proj i))

@[simp] theorem forceRealization_apply (m : ℕ) (G : ForceDatum m) (i : Fin 3) :
    forceRealization m G i = sobolevRealization (m : ℝ) (G i) := rfl

theorem forceRealization_injective (m : ℕ) : Function.Injective (forceRealization m) := by
  intro G H h
  funext i
  apply sobolevRealization_injective (m : ℝ)
  exact congrFun h i

def AdmissibleForce (g : ℝ → ForceDistribution) : Prop :=
  ∀ m : ℕ, ∃ G : ℝ → ForceDatum m,
    (∀ t, 0 ≤ t → forceRealization m (G t) = g t) ∧
    ContDiffOn ℝ ∞ G (Ici 0) ∧ MemLp G 1 (positiveTimeMeasure) ∧ MemLp G 2 (positiveTimeMeasure)

theorem admissibleForce_zero : AdmissibleForce (fun _ => 0) := by
  intro m
  refine ⟨fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro t ht; exact map_zero (forceRealization m)
  · fun_prop
  · exact MemLp.zero
  · exact MemLp.zero

theorem admissibleForce_add {g h : ℝ → ForceDistribution}
    (hg : AdmissibleForce g) (hh : AdmissibleForce h) : AdmissibleForce (g + h) := by
  intro m
  obtain ⟨G, hG, cG, lG1, lG2⟩ := hg m
  obtain ⟨H, hH, cH, lH1, lH2⟩ := hh m
  refine ⟨G + H, ?_, cG.add cH, lG1.add lH1, lG2.add lH2⟩
  intro t ht
  simp only [Pi.add_apply, map_add, hG t ht, hH t ht]

theorem admissibleForce_neg {g : ℝ → ForceDistribution} (hg : AdmissibleForce g) :
    AdmissibleForce (-g) := by
  intro m
  obtain ⟨G, hG, cG, lG1, lG2⟩ := hg m
  refine ⟨-G, ?_, cG.neg, lG1.neg, lG2.neg⟩
  intro t ht; simp only [Pi.neg_apply, map_neg, hG t ht]

theorem admissibleForce_sub {g h : ℝ → ForceDistribution}
    (hg : AdmissibleForce g) (hh : AdmissibleForce h) : AdmissibleForce (g - h) := by
  simpa [sub_eq_add_neg] using admissibleForce_add hg (admissibleForce_neg hh)

theorem admissibleForce_congr_Ici {g h : ℝ → ForceDistribution}
    (he : ∀ t, t ∈ Ici 0 → g t = h t) : AdmissibleForce g ↔ AdmissibleForce h := by
  constructor
  · intro hg m
    obtain ⟨G, hG, cG, lG1, lG2⟩ := hg m
    refine ⟨G, ?_, cG, lG1, lG2⟩
    intro t ht; rw [hG t ht, he t ht]
  · intro hh m
    obtain ⟨H, hH, cH, lH1, lH2⟩ := hh m
    refine ⟨H, ?_, cH, lH1, lH2⟩
    intro t ht
    rw [hH t ht, (he t ht).symm]

end NSFormalization.Paper3
