import NSFormalization.Section3.T11.H1Restart
import NSFormalization.Section3.T11.RestartBeyond

/-!
# H¹-uniform endpoint continuation on the three-torus

The local-theory argument cited at `appendix-a-local-theory.tex:146-153`
chooses one positive duration before the restart time and the smooth datum in
an H¹ ball.  This module supplies that duration with `h1RestartT` and reuses
the established periodic gluing and uniqueness argument to export the exact
endpoint target recorded as `research/P21/Targets.lean:h1UniformEndpointT`.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open scoped ENNReal

/-- The exact periodic H¹-uniform endpoint target: one duration works for every
admissible solution whose trajectory stays in the fixed H¹ ball.  The duration
is the one delivered by `h1RestartT` at `S`; the returned solution agrees with
the old velocity and normalized pressure throughout `[0,S)`. -/
theorem restartBeyondH1T :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField), a ∈ initialClassT →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p →
                (∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm 1 (fun x ↦ u (t, x)) ≤ K) →
                    ∃ v : ClassicalSolutionT ν a f (S + δ),
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.velocity (t, x) = u (t, x)) ∧
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.pressure (t, x) = p (t, x)) := by
  intro ν hν f hf S hS K hK
  obtain ⟨d, hd, hloc⟩ := h1RestartT ν hν f hf S hS.le K hK
  obtain ⟨t₀, ht₀0, ht₀S, ht₀d⟩ : ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < S ∧ S < t₀ + d :=
    ⟨max 0 (S - d / 2), le_max_left _ _, max_lt hS (by linarith),
      by have := le_max_right 0 (S - d / 2); linarith⟩
  refine ⟨t₀ + d - S, by linarith, ?_⟩
  intro a ha u p hsolve hbound
  obtain ⟨w, hwv, hwp⟩ := hsolve ((t₀ + S) / 2) (by linarith) (by linarith)
  have hbmem : t₀ ∈ Ico (0 : ℝ) ((t₀ + S) / 2) := ⟨ht₀0, by linarith⟩
  have hKa : periodicSobolevENorm 1 (fun x => w.velocity (t₀, x)) ≤ K := by
    rw [hwv]
    exact hbound t₀ ⟨ht₀0, ht₀S⟩
  obtain ⟨w₂, -⟩ := hloc t₀ ⟨ht₀0, ht₀S.le⟩ (fun x => w.velocity (t₀, x))
    (velocitySlice_mem_initialClassT w hbmem) hKa
  obtain ⟨v, -, -⟩ := glueClassicalSolutionT hν w hbmem w₂
    (by linarith : (t₀ + S) / 2 < t₀ + d)
  have hrew : S + (t₀ + d - S) = t₀ + d := by ring
  rw [hrew]
  refine ⟨v, ?_, ?_⟩
  · intro t ht x
    obtain ⟨wc, hwcv, -⟩ := hsolve ((t + S) / 2) (by linarith [ht.1])
      (by linarith [ht.2])
    have hag := velocity_unique ν hν a ha f hf (t₀ + d) ((t + S) / 2) v wc t
      ⟨ht.1, lt_min (by linarith [ht.2]) (by linarith [ht.2])⟩ x
    rw [hag, hwcv]
  · intro t ht x
    obtain ⟨wc, -, hwcp⟩ := hsolve ((t + S) / 2) (by linarith [ht.1])
      (by linarith [ht.2])
    have hag := pressure_unique ν hν a ha f hf (t₀ + d) ((t + S) / 2) v wc t
      ⟨ht.1, lt_min (by linarith [ht.2]) (by linarith [ht.2])⟩ x
    rw [hag, hwcp]

end NSFormalization.Section3.T11
