import Contracts.V1.Data

/-! Whole-space integral continuation with fixed-force H7 restart. No H1-uniform or cross-force restart statement is exported. -/

noncomputable section

namespace BlowupDensity.Contracts.V2.Continuation

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-- Positive-time translation of a force, verbatim from
`research/A02/Spec.lean:157-158`. -/
def timeShift (t₀ : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  fun z => f (z.1 + t₀, z.2)

/-- The squared `H²` continuation integral, verbatim from
`research/A04/Spec.lean:202-203`. -/
def squaredHTwoIntegral (S : ℝ) (u : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (fun x : Space => u (t, x)) ^ 2

/-- A common pair of fields solves the equation on every shorter horizon,
verbatim from `research/A04/Spec.lean:223-226`. -/
def SolvesBelow (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  ∀ b : ℝ, 0 < b → b < S →
    ∃ w : ClassicalSolutionR ν a f b, w.velocity = u ∧ w.pressure = p

/-- The `L¹_t H^m_x` part of the manuscript force class, verbatim from
`research/A04/Spec.lean:268-269`. -/
def MemL1Hm (f : SpaceTimeField) : Prop :=
  ∀ m : ℕ, forceSobolevENormL1 (m : ℝ) f ≠ ⊤

/-- The maximal-solution predicate, verbatim from
`research/A02/Spec.lean:210-214`. -/
def IsMaximalSolution (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  0 < maximalLifespanR ν a f ∧
    ∀ S : ℝ, 0 < S → ENNReal.ofReal S < maximalLifespanR ν a f →
      ∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p

/-- The owner-approved version-two restart predicate.  The force and compact
restart horizon precede `δ`; the datum bound is `H⁷`; the resulting duration is
uniform over all restart times `t₀ ∈ [0,S]` and all admissible data in that
ball.  This is exactly `Section4/A04/RestartFixedForce.lean`'s
`RestartFixedForce` after the binding supplies its `localHorizon'`.

Exact difference from the paper/V1 restart: this predicate is for one fixed
force rather than uniform in the force, and assumes an `H⁷` datum bound rather
than an `H¹` bound.  It retains the paper's needed uniformity over restart times
in `[0,S]`. -/
def RestartFixedForce
    (horizon : ℝ → SpatialField → SpaceTimeField → ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ f : SpaceTimeField, MemForceR f →
    ∀ S : ℝ, 0 ≤ S → ∀ K : ℝ≥0∞, K ≠ ⊤ →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ t₀ ∈ Icc (0 : ℝ) S, ∀ a' : SpatialField, a' ∈ initialClassR →
          sobolevENorm 7 a' ≤ K → δ ≤ horizon ν a' (timeShift t₀ f)

/-- The proved A04 continuation interface with the owner-approved restart
recut.  It is intentionally independent of the open manuscript/V1 `H¹`,
cross-force restart field; see the module docstring and
`research/A04/REPORT_215.md` §3.

No field is a placeholder proposition.  `restart` is the approved V2 wording;
`higherOrderBound` is copied verbatim from `research/A04/Spec.lean`; the last
three fields have exactly the unconditional lane-217 theorem shapes. -/
structure ContinuationV2API
    (horizon : ℝ → SpatialField → SpaceTimeField → ℝ) : Prop where
  /-- Fixed-force, `H⁷`, restart-time-uniform local existence.  The force and
  `S` are quantified before `∃ δ`, and the same positive real `δ` works for
  every `t₀ ∈ [0,S]` and every admissible `H⁷`-bounded datum.

  Exact difference from the paper/V1 field: fixed force instead of uniformity
  across forces, and `H⁷` instead of `H¹`; uniformity over restart times is
  retained. -/
  restart : RestartFixedForce horizon

  /-- The Grönwall consequence, copied verbatim from
  `research/A04/Spec.lean:535-542`: a finite squared-`H²` integral bounds every
  integer Sobolev order uniformly on `[0,S)`.

  This field itself is not narrowed: it remains the manuscript/V1 statement.
  In the downstream restart proof order `m = 7` is used because the available
  local theory is fixed-force `H⁷`; no cross-force uniformity is claimed. -/
  higherOrderBound : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
      ∀ S : ℝ, 0 < S → ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        SolvesBelow ν a f S u p → squaredHTwoIntegral S u ≠ ⊤ →
          ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
            ∀ t ∈ Ico (0 : ℝ) S,
              sobolevENorm (m : ℝ) (fun x : Space => u (t, x)) ≤ M

  /-- The fixed-force endpoint restart theorem in lane 217's exact shape.
  For one `f ∈ F_R` and one positive `S`, a finite `H⁷` bound on `[0,S)`
  gives a genuine `δ > 0` and lifespan through `S+δ`.

  Exact difference from the paper/V1 restart step: the force is fixed before
  `δ` rather than quantified after it, and the datum/trajectory bound is `H⁷`
  rather than `H¹`; `δ` is still uniform over all restart times approaching
  `S`. -/
  restartBeyond :
    ∀ (ν : ℝ), 0 < ν → ∀ (f : SpaceTimeField), MemForceR f →
      ∀ (S : ℝ), 0 < S → ∀ K : ℝ≥0∞, K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField) (u : SpaceTimeField) (p : SpaceTimeScalar),
            a ∈ initialClassR → SolvesBelow ν a f S u p →
              (∀ t ∈ Ico (0 : ℝ) S,
                sobolevENorm 7 (fun x : Space => u (t, x)) ≤ K) →
              ENNReal.ofReal (S + δ) ≤ maximalLifespanR ν a f

  /-- The integral continuation criterion in lane 217's exact, unconditional
  `MemForceR` shape: finite `∫₀ˢ‖u‖²_{H²}` implies strict extension past
  `S`.

  The conclusion is the paper's continuation conclusion.  Its implementation
  uses the fixed-force `H⁷` restart (force before `δ`, rather than cross-force
  uniformity; `H⁷`, rather than `H¹`) and remains uniform over restart times.
  No paper `H¹` restart field is asserted here. -/
  extendsBeyond : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ S : ℝ, 0 < S → ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        SolvesBelow ν a f S u p → squaredHTwoIntegral S u ≠ ⊤ →
          ENNReal.ofReal S < maximalLifespanR ν a f

  /-- The lane-217 maximal-lifespan packaging: local finiteness of the squared
  `H²` integral at every finite endpoint within or at the lifespan forces the
  lifespan to be infinite.

  The conclusion matches the paper.  The proof uses the registered fixed-force
  `H⁷` restart (force fixed before `δ`, `H⁷` rather than `H¹`, uniform over
  restart times); it does not assert or imply the paper/V1 cross-force `H¹`
  restart. -/
  lifespanInfiniteOfLocallyFinite :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalSolution ν a f u p →
            (∀ S : ℝ, 0 < S → ENNReal.ofReal S ≤ maximalLifespanR ν a f →
              squaredHTwoIntegral S u ≠ ⊤) →
            maximalLifespanR ν a f = ⊤

end BlowupDensity.Contracts.V2.Continuation
