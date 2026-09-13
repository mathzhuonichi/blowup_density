import NSFormalization.Paper3.CompactAdmissibleForce
import NSFormalization.Paper3.RealPositiveDensity

/-! Coherent real integer-order force witnesses, with reality expressed by
conjugate-reflection symmetry. This is a candidate manuscript interface;
real-distribution characterization, one-sided smoothness identification and
angular Fourier identification remain. The finite Pi norm is the supremum
norm, so exact Euclidean/angular metric transport remains outstanding. -/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source NSFormalization.Source.RealSobolev
open scoped ContDiff ENNReal

def RealAdmissibleForce (g : ℝ → ForceDistribution) : Prop :=
  ∀ m : ℕ, ∃ G : ℝ → ForceDatum m,
    (∀ t, 0 ≤ t → forceRealization m (G t) = g t) ∧
    ContDiffOn ℝ ∞ G (Ici 0) ∧ MemLp G 1 (positiveTimeMeasure) ∧ MemLp G 2 (positiveTimeMeasure) ∧
    ∀ t, 0 ≤ t → ∀ i, realSymmetry (G t i) = G t i

theorem realAdmissibleForce_zero : RealAdmissibleForce (fun _ => 0) := by
  intro m
  refine ⟨fun _ => 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; exact map_zero (forceRealization m)
  · fun_prop
  · exact MemLp.zero
  · exact MemLp.zero
  · intro t ht i; exact map_zero realSymmetry

theorem realAdmissibleForce_add {g h : ℝ → ForceDistribution}
    (hg : RealAdmissibleForce g) (hh : RealAdmissibleForce h) : RealAdmissibleForce (g + h) := by
  intro m
  obtain ⟨G, hG, cG, lG1, lG2, rG⟩ := hg m
  obtain ⟨H, hH, cH, lH1, lH2, rH⟩ := hh m
  refine ⟨G + H, ?_, cG.add cH, lG1.add lH1, lG2.add lH2, ?_⟩
  · intro t ht
    simp only [Pi.add_apply, map_add, hG t ht, hH t ht]
  · intro t ht i
    simp only [Pi.add_apply, map_add, rG t ht i, rH t ht i]

theorem realAdmissibleForce_neg {g : ℝ → ForceDistribution} (hg : RealAdmissibleForce g) :
    RealAdmissibleForce (-g) := by
  intro m
  obtain ⟨G, hG, cG, lG1, lG2, rG⟩ := hg m
  refine ⟨-G, ?_, cG.neg, lG1.neg, lG2.neg, ?_⟩
  · intro t ht; simp only [Pi.neg_apply, map_neg, hG t ht]
  · intro t ht i; simp only [Pi.neg_apply, map_neg, rG t ht i]

theorem realAdmissibleForce_sub {g h : ℝ → ForceDistribution}
    (hg : RealAdmissibleForce g) (hh : RealAdmissibleForce h) : RealAdmissibleForce (g - h) := by
  simpa [sub_eq_add_neg] using realAdmissibleForce_add hg (realAdmissibleForce_neg hh)

theorem realAdmissibleForce_congr_Ici {g h : ℝ → ForceDistribution}
    (he : ∀ t, t ∈ Ici 0 → g t = h t) : RealAdmissibleForce g ↔ RealAdmissibleForce h := by
  constructor
  · intro hg m
    obtain ⟨G, hG, cG, lG1, lG2, rG⟩ := hg m
    refine ⟨G, ?_, cG, lG1, lG2, rG⟩
    intro t ht; rw [hG t ht, he t ht]
  · intro hh m
    obtain ⟨H, hH, cH, lH1, lH2, rH⟩ := hh m
    refine ⟨H, ?_, cH, lH1, lH2, rH⟩
    intro t ht
    rw [hH t ht, (he t ht).symm]


theorem RealAdmissibleForce.admissibleForce {g : ℝ → ForceDistribution}
    (hg : RealAdmissibleForce g) : AdmissibleForce g := by
  intro m
  obtain ⟨G, hG, cG, lG1, lG2, _⟩ := hg m
  exact ⟨G, hG, cG, lG1, lG2⟩

theorem realSymmetry_compactForceDatum (m : ℕ) (F : VelocityField)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t : ℝ) (i : Fin 3) :
    realSymmetry (compactForceDatum m F hF hc t i) = compactForceDatum m F hF hc t i := by
  let R : ℝ × Space → ℝ := fun z => (coordinateForce F i z).re
  have hR : ContDiff ℝ ∞ R := Complex.reCLM.contDiff.comp (coordinateForce_smooth hF i)
  have hRc : HasCompactSupport R := (coordinateForce_compact hc i).comp_left (by simp)
  have he : (realCompactSobolevTimeSlice (m : ℝ) R hR hRc t : SobolevHilbert (m : ℝ)) =
      compactForceDatum m F hF hc t i := by
    rw [coe_realCompactSobolevTimeSlice]
    rfl
  rw [← he]
  exact (mem_realSubspace_iff _ _).mp (realCompactSobolevTimeSlice (m : ℝ) R hR hRc t).property

theorem realAdmissibleForce_compactForceDistribution (F : VelocityField)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    RealAdmissibleForce (compactForceDistribution F hF hc) := by
  intro m
  obtain ⟨G, hG, cG, lG1, lG2⟩ := admissibleForce_compactForceDistribution F hF hc m
  refine ⟨G, hG, cG, lG1, lG2, ?_⟩
  intro t ht i
  have he : G t = compactForceDatum m F hF hc t :=
    forceRealization_injective m ((hG t ht).trans
      (forceRealization_compactForceDatum m F hF hc t).symm)
  rw [he]
  exact realSymmetry_compactForceDatum m F hF hc t i

theorem realAdmissibleForce_add_compact {g : ℝ → ForceDistribution}
    (hg : RealAdmissibleForce g) (F : VelocityField)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    RealAdmissibleForce (g + compactForceDistribution F hF hc) :=
  realAdmissibleForce_add hg (realAdmissibleForce_compactForceDistribution F hF hc)

end NSFormalization.Paper3
