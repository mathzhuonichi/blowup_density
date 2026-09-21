import NSFormalization.Section4.A04.H1Restart

/-!
# H¹-uniform endpoint continuation on R³

The local-theory argument cited at `appendix-a-local-theory.tex:146-151`
chooses one positive duration before the restart time and the smooth datum in
an H¹ ball.  This module feeds that uniform duration into the endpoint
bookkeeping and exports the strict maximal-lifespan conclusion recorded as
`research/P21/Targets.lean:h1UniformEndpointR`.
-/

noncomputable section

namespace NSFormalization.Section4.A04

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
open NSFormalization.Section4.D01 (sobolevENorm)
open scoped ENNReal

/-- One duration is chosen before both the restart time and every smooth datum
in the fixed H¹ ball. -/
def RestartFixedForceH1 (ν : ℝ) (f : SpaceTimeField) (S : ℝ) : Prop :=
  ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ : ℝ, 0 < δ ∧
    ∀ t₀ ∈ Icc (0 : ℝ) S, ∀ a' : SpatialField, a' ∈ initialClassR →
      sobolevENorm 1 a' ≤ K →
        ∃ w : ClassicalSolutionR ν a' (timeShift t₀ f) δ,
          A01.ManuscriptLocalRegularity ν a' (timeShift t₀ f) δ w

/-- The proved H¹ restart theorem in named fixed-force form. -/
theorem restartFixedForceH1 (ν : ℝ) (hν : 0 < ν) (f : SpaceTimeField)
    (hf : MemForceR f) (S : ℝ) (hS : 0 ≤ S) :
    RestartFixedForceH1 ν f S :=
  h1RestartR ν hν f hf S hS

/-- Endpoint bookkeeping before shrinking the common restart margin. -/
theorem restartBeyondH1_le
    (ν : ℝ) (hν : 0 < ν) (f : SpaceTimeField) (hf : MemForceR f)
    (S : ℝ) (hS : 0 < S) (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : SpatialField) (u : SpaceTimeField) (p : SpaceTimeScalar),
        a ∈ initialClassR → SolvesBelow ν a f S u p →
          (∀ t ∈ Ico (0 : ℝ) S,
            sobolevENorm 1 (fun x => u (t, x)) ≤ K) →
              ENNReal.ofReal (S + δ) ≤ maximalLifespanR ν a f := by
  obtain ⟨δ, hδ, hr⟩ := h1RestartAt ν hν f hf S hS.le K hK
  refine ⟨δ, hδ, ?_⟩
  intro a u p _ha hu hbound
  apply restartBeyond_of_restartAt hS hδ
  intro t ht
  exact hr a u p hu t ht (hbound t ht)

/-- The exact whole-space H¹-uniform endpoint target: a single positive
duration works for every admissible solution whose slices stay in the fixed
H¹ ball, and the resulting lifespan inequality is strict. -/
theorem restartBeyondH1 :
    ∀ (ν : ℝ), 0 < ν → ∀ (f : SpaceTimeField), MemForceR f →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField) (u : SpaceTimeField) (p : SpaceTimeScalar),
            a ∈ initialClassR → SolvesBelow ν a f S u p →
              (∀ t ∈ Ico (0 : ℝ) S,
                sobolevENorm 1 (fun x => u (t, x)) ≤ K) →
                  ENNReal.ofReal (S + δ) < maximalLifespanR ν a f := by
  intro ν hν f hf S hS K hK
  obtain ⟨δ, hδ, hr⟩ := restartBeyondH1_le ν hν f hf S hS K hK
  refine ⟨δ / 2, by linarith, ?_⟩
  intro a u p ha hu hbound
  have he := hr a u p ha hu hbound
  exact ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < S + δ)).mpr
    (by linarith : S + δ / 2 < S + δ)).trans_le he

end NSFormalization.Section4.A04
