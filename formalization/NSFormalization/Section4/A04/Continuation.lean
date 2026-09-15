import NSFormalization.Section4.A02.Maximal
import NSFormalization.Section4.A04.ForceShift

/-!
# A04 R1 endpoint bookkeeping and C1 finite-lifespan contradiction

The analytic inputs remain explicit: this file does not establish A02's restart
or A04's integral continuation estimate. See `research/A04/ATTEMPTS_R1C1.md`.
The definitions below reproduce `research/A04/Spec.lean:202,226` verbatim.
-/

noncomputable section

namespace NSFormalization.Section4.A04

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section4.A02
open NSFormalization.Section4.D01 (sobolevENorm)
open scoped ENNReal

def squaredHTwoIntegral (S : ℝ) (u : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (fun x : Space => u (t, x)) ^ 2

def SolvesBelow (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  ∀ b : ℝ, 0 < b → b < S →
    ∃ w : ClassicalSolutionR ν a f b, w.velocity = u ∧ w.pressure = p

/-- A solution family reaching every shorter horizon reaches `S` in the
supremum defining the maximal lifespan; no endpoint solution is asserted. -/
theorem lifespan_ge_of_solvesBelow {ν S : ℝ} {a : SpatialField}
    {f u : SpaceTimeField} {p : SpaceTimeScalar} (hS : 0 < S)
    (hu : SolvesBelow ν a f S u p) :
    ENNReal.ofReal S ≤ maximalLifespanR ν a f := by
  apply lifespan_ge_of_forall_shorter ν a f S hS
  intro b hb hbS
  obtain ⟨w, _, _⟩ := hu b hb hbS
  exact ⟨w⟩

/-- R1's endpoint step: one uniform restart length works as `t₀` approaches
`S`. The conclusion retains the full length (no halving of the final margin).
`restartAt` is the bound after the A02 restart hypotheses have been discharged.
It is a hypothesis, not a replacement proof of A02's analytic restart. -/
theorem restartBeyond_of_restartAt {ν S δ : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (hS : 0 < S) (_hδ : 0 < δ)
    (restartAt : ∀ t₀ ∈ Ico (0 : ℝ) S,
      ENNReal.ofReal (t₀ + δ) ≤ maximalLifespanR ν a f) :
    ENNReal.ofReal (S + δ) ≤ maximalLifespanR ν a f := by
  apply le_of_forall_lt
  intro c hc
  have hcR : c.toReal < S + δ := ENNReal.toReal_lt_of_lt_ofReal hc
  let t₀ : ℝ := (max 0 (c.toReal - δ) + S) / 2
  have hm : max 0 (c.toReal - δ) < S := max_lt hS (by linarith)
  have ht0 : 0 ≤ t₀ := by dsimp [t₀]; linarith [le_max_left (0 : ℝ) (c.toReal - δ)]
  have htS : t₀ < S := by dsimp [t₀]; linarith
  have hct : c.toReal < t₀ + δ := by
    dsimp [t₀]
    linarith [le_max_right (0 : ℝ) (c.toReal - δ)]
  have hlt : c < ENNReal.ofReal (t₀ + δ) :=
    (ENNReal.lt_ofReal_iff_toReal_lt hc.ne_top).mpr hct
  exact hlt.trans_le (restartAt t₀ ⟨ht0, htS⟩)

/-- C1, exactly the draft's lifespan clause, conditional on the named
`extendsBeyond` analytic input. This is the contradiction at the finite
supremum used in `04-whole-space.tex:129-134` (Proposition 4.3). -/
theorem lifespanInfiniteOfLocallyFinite_of_extendsBeyond
    (extendsBeyond : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
        ∀ S : ℝ, 0 < S → ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
          SolvesBelow ν a f S u p → squaredHTwoIntegral S u ≠ ⊤ →
            ENNReal.ofReal S < maximalLifespanR ν a f) :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
      0 < maximalLifespanR ν a f →
      ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        (∀ b : ℝ, 0 < b → ENNReal.ofReal b < maximalLifespanR ν a f →
          ∃ w : ClassicalSolutionR ν a f b, w.velocity = u ∧ w.pressure = p) →
        (∀ S : ℝ, 0 < S → ENNReal.ofReal S ≤ maximalLifespanR ν a f →
          squaredHTwoIntegral S u ≠ ⊤) →
        maximalLifespanR ν a f = ⊤ := by
  intro ν a f hν ha hf hf1 hpos u p hu hfinite
  by_contra htop
  have heq : ENNReal.ofReal (maximalLifespanR ν a f).toReal =
      maximalLifespanR ν a f := ENNReal.ofReal_toReal htop
  have hT : 0 < (maximalLifespanR ν a f).toReal :=
    ENNReal.toReal_pos hpos.ne' htop
  have hbelow : SolvesBelow ν a f (maximalLifespanR ν a f).toReal u p := by
    intro b hb hbT
    apply hu b hb
    rw [← heq]
    exact (ENNReal.ofReal_lt_ofReal_iff hT).mpr hbT
  have hbad := extendsBeyond ν a f hν ha hf hf1 _ hT u p hbelow
    (hfinite _ hT heq.le)
  rw [heq] at hbad
  exact (lt_irrefl _ hbad)


/-- The exact `MaximalSolutionAPI.restart` statement, an explicit upstream
input. Its analytic existence and patching content is not proved here. -/
def Restart : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : SpatialField) (f u : SpaceTimeField) (p : SpaceTimeScalar),
        a ∈ initialClassR → MemForceR f → IsMaximalSolution ν a f u p →
          ∀ t₀ ∈ presingularTimes ν a f,
            sobolevENorm 1 (fun x : Space => u (t₀, x)) ≤ K →
            forceSobolevENormL1 1 (timeShift t₀ f) ≤ K →
              ENNReal.ofReal (t₀ + δ) ≤ maximalLifespanR ν a f

/-- Directed-union construction from A02, with positivity supplied by an
existing shorter solution rather than the still-open A01 local theory. -/
theorem maximal_fields_of_solvesBelow {ν S : ℝ} {a : SpatialField}
    {f u : SpaceTimeField} {p : SpaceTimeScalar} (hν : 0 < ν) (hS : 0 < S)
    (hu : SolvesBelow ν a f S u p) :
    IsMaximalSolution ν a f (uField ν a f) (pField ν a f) := by
  have hge := lifespan_ge_of_solvesBelow hS hu
  refine ⟨(ENNReal.ofReal_pos.mpr hS).trans_le hge, ?_⟩
  intro b hb hbl
  obtain ⟨S', hbS', hne⟩ := exists_horizon_gt_of_lt_lifespan hb.le hbl
  let w := hne.some.restrict hb hbS'.le
  refine exists_eq_fields_of_agree (w.normalizePressure (0 : Space))
    (uField ν a f) (pField ν a f) ?_ ?_
  · intro t ht x
    exact uField_eq hν w ht x
  · intro t ht x
    exact pField_eq hν w ht x

/-- R1 assembly with precisely A02's restart and the separately named
positive-time force translation estimate. The final theorem's conclusion and
quantifier order are `ContinuationAPI.restartBeyond` verbatim. -/
theorem restartBeyond_of_restart_and_forceShift (restart : Restart)
    (forceShift : ∀ (f : SpaceTimeField), MemForceR f → ∀ t₀ : ℝ, 0 ≤ t₀ →
      forceSobolevENormL1 1 (timeShift t₀ f) ≤ forceSobolevENormL1 1 f) :
    ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
        (u : SpaceTimeField) (p : SpaceTimeScalar),
        a ∈ initialClassR → MemForceR f → 0 < S → SolvesBelow ν a f S u p →
          (∀ t ∈ Ico (0 : ℝ) S,
            sobolevENorm 1 (fun x : Space => u (t, x)) ≤ K) →
          BoundedIntoHOne (Icc (0 : ℝ) (S + 1)) K f →
          forceSobolevENormL1 1 f ≤ K →
            ENNReal.ofReal (S + δ) ≤ maximalLifespanR ν a f := by
  intro ν hν K hK
  obtain ⟨δ, hδ, hr⟩ := restart ν hν K hK
  refine ⟨δ, hδ, ?_⟩
  intro a f S u p ha hf hS hu hbound _hforceBound hfK
  have hmax := maximal_fields_of_solvesBelow hν hS hu
  have hge := lifespan_ge_of_solvesBelow hS hu
  apply restartBeyond_of_restartAt hS hδ
  intro t ht
  have htL : ENNReal.ofReal t < maximalLifespanR ν a f :=
    ((ENNReal.ofReal_lt_ofReal_iff hS).mpr ht.2).trans_le hge
  apply hr a f (uField ν a f) (pField ν a f) ha hf hmax t ⟨ht.1, htL⟩
  · obtain ⟨w, hw, _⟩ := hu ((t + S) / 2) (by linarith [ht.1]) (by linarith [ht.2])
    have heq : (fun x : Space => uField ν a f (t, x)) =
        (fun x : Space => u (t, x)) := by
      funext x
      rw [← hw]
      exact uField_eq hν w ⟨ht.1, by linarith [ht.2]⟩ x
    rw [heq]
    exact hbound t ht
  · exact (forceShift f hf t ht.1).trans hfK

/-- **R1: `ContinuationAPI.restartBeyond`**, with only the exact upstream
`MaximalSolutionAPI.restart` retained as a named hypothesis. The force-tail
estimate and maximal-field transfer are proved locally. The same `δ` works
for every datum, endpoint and solution family. -/
theorem restartBeyond (restart : Restart) :
    ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
        (u : SpaceTimeField) (p : SpaceTimeScalar),
        a ∈ initialClassR → MemForceR f → 0 < S → SolvesBelow ν a f S u p →
          (∀ t ∈ Ico (0 : ℝ) S,
            sobolevENorm 1 (fun x : Space => u (t, x)) ≤ K) →
          BoundedIntoHOne (Icc (0 : ℝ) (S + 1)) K f →
          forceSobolevENormL1 1 f ≤ K →
            ENNReal.ofReal (S + δ) ≤ maximalLifespanR ν a f :=
  restartBeyond_of_restart_and_forceShift restart
    (fun f _ t₀ ht₀ => forceSobolevENormL1_timeShift_le 1 f t₀ ht₀)

/-- Exact G3 input `ContinuationAPI.higherOrderBound`. The analytic derivation
from high-order energy estimates remains outside R1/C1. -/
def HigherOrderBound : Prop :=
  ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
      ∀ S : ℝ, 0 < S → ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        SolvesBelow ν a f S u p → squaredHTwoIntegral S u ≠ ⊤ →
          ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
            ∀ t ∈ Ico (0 : ℝ) S,
              sobolevENorm (m : ℝ) (fun x : Space => u (t, x)) ≤ M

/-- C1's continuation criterion from G3 and R1: combine the velocity, compact
force, and time-integrated force bounds using one finite maximum. -/
theorem extendsBeyond (restart : Restart) (higherOrderBound : HigherOrderBound) :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
        ∀ S : ℝ, 0 < S → ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
          SolvesBelow ν a f S u p → squaredHTwoIntegral S u ≠ ⊤ →
            ENNReal.ofReal S < maximalLifespanR ν a f := by
  intro ν a f hν ha hf hf1 S hS u p hu hint
  obtain ⟨M, hM, huM⟩ := higherOrderBound ν a f hν ha hf hf1 S hS u p hu hint 1
  simp only [Nat.cast_one] at huM
  have hf1one : forceSobolevENormL1 (1 : ℝ) f ≠ ⊤ := by
    simpa only [Nat.cast_one] using hf1 1
  obtain ⟨F, hF, hfF⟩ := exists_boundedIntoHOne_of_memForceR hf (S + 1)
  let K : ℝ≥0∞ := max M (max F (forceSobolevENormL1 1 f))
  have hK : K ≠ ⊤ := by
    dsimp [K]
    exact (max_lt hM.lt_top (max_lt hF.lt_top hf1one.lt_top)).ne
  obtain ⟨δ, hδ, hr⟩ := restartBeyond restart ν hν K hK
  have hle := hr a f S u p ha hf hS hu
    (fun t ht => (huM t ht).trans (le_max_left _ _))
    (fun t ht => (hfF t ht).trans ((le_max_left _ _).trans (le_max_right _ _)))
    ((le_max_right _ _).trans (le_max_right _ _))
  exact ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < S + δ)).mpr
    (by linarith : S < S + δ)).trans_le hle

/-- C1, the exact global-lifespan clause, with only its unproved analytic
owners G3 and A02 restart explicit. -/
theorem lifespanInfiniteOfLocallyFinite (restart : Restart)
    (higherOrderBound : HigherOrderBound) :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
      0 < maximalLifespanR ν a f →
      ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        (∀ b : ℝ, 0 < b → ENNReal.ofReal b < maximalLifespanR ν a f →
          ∃ w : ClassicalSolutionR ν a f b, w.velocity = u ∧ w.pressure = p) →
        (∀ S : ℝ, 0 < S → ENNReal.ofReal S ≤ maximalLifespanR ν a f →
          squaredHTwoIntegral S u ≠ ⊤) →
        maximalLifespanR ν a f = ⊤ :=
  lifespanInfiniteOfLocallyFinite_of_extendsBeyond (extendsBeyond restart higherOrderBound)

end NSFormalization.Section4.A04
