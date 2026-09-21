import Contracts.V1.Data

/-!
# Draft A specification: Corollary 4.x (`cor:Rclasses`)

This file independently transcribes
`paper/sections/04-whole-space.tex:194-199`.  The corollary says that every
clause of Theorem 4.1 remains valid after replacing the ambient force class by
either `F_c` or `F_rd`; consequently the inherited clauses at
`04-whole-space.tex:8-13` are written out below for each class.

The two classes are separate fields rather than values of a quantified `Y`.
That prevents this specification from asserting the result for an arbitrary
force subclass.  The registered `breakdownSetIn` and `RelativelyDense` still
make the relative ambient class explicit in every conclusion.
-/

noncomputable section

namespace BlowupDensity.Research.R45.DraftA

open BlowupDensity.Contracts.V1.Data
open Set
open scoped ENNReal

/-- `04-whole-space.tex:8`: for `q in {1,2}`, the threshold is
`s_q = 2/q - 3/2`.  The manuscript's two exponents are represented by a
natural number so the same `q` has canonical casts both to `ℝ` in the formula
and to `ℝ≥0∞` in `forceSobolevENorm`. -/
def rClassesThreshold (q : ℕ) : ℝ :=
  2 / (q : ℝ) - 3 / 2

/-- `04-whole-space.tex:13,31-42,177-179`: a concrete neighborhood form of
the rider "around every reference regular through `T`".

For every force-norm tolerance, energy-norm tolerance, and earlier time
`S < T`, one approximant stays in the selected force class, is force-close,
has maximal lifespan exactly `T`, has the same initial datum (because `u` is a
`ClassicalSolutionR ν a f T`), agrees with the chosen reference velocity on
`[0,S]`, and is energy-close on `(0,T)`.  Quantifying over all tolerances and
all `S < T` is the epsilon-neighborhood rendering of "difference tending to
zero" and "same earlier history"; no new mathematical predicate is left
abstract. -/
def HasReferenceApproximationRider
    (Y : Set SpaceTimeField) (ν T : ℝ) (q : ℕ) (s : ℝ)
    (a : SpatialField) (g : SpaceTimeField) (δ : ℝ)
    (v : ClassicalSolutionR ν a g (T + δ)) : Prop :=
  ∀ forceRadius energyRadius : ℝ≥0∞,
    0 < forceRadius →
    0 < energyRadius →
    ∀ S : ℝ, 0 ≤ S → S < T →
      ∃ f : SpaceTimeField,
        f ∈ Y ∧
        forceSobolevENorm (q : ℝ≥0∞) s (f - g) < forceRadius ∧
        maximalLifespanR ν a f = ENNReal.ofReal T ∧
        ∃ u : ClassicalSolutionR ν a f T,
          (∀ t ∈ Icc (0 : ℝ) S, ∀ x,
            u.velocity (t, x) = v.velocity (t, x)) ∧
          energyENorm T (u.velocity - v.velocity) < energyRadius

/-- **Corollary 4.x** (`cor:Rclasses`),
`paper/sections/04-whole-space.tex:194-199`: Theorem 4.1, including its
approximation rider, for the compactly supported and rapidly decaying force
classes. -/
structure RClassesAPI where
  /-- `04-whole-space.tex:195`, inheriting `:8-10`: for compactly supported
  forces, for every `ν,T > 0`, `q ∈ {1,2}`, `s < 2/q-3/2`, and every fixed
  `a ∈ X_R`, the exact ambient-relative breakdown set is dense.

  Quantifier order: `ν, T`, positivity, `q`, membership of `q`, `s`, `a`,
  membership of `a`, then the strict threshold hypothesis. -/
  compactDenseBelow :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ q : ℕ, (q = 1 ∨ q = 2) →
        ∀ s : ℝ, ∀ a : SpatialField, a ∈ initialClassR →
          s < rClassesThreshold q →
            RelativelyDense (q : ℝ≥0∞) s forceClassCompact
              (breakdownSetIn forceClassCompact ν a T)

  /-- `04-whole-space.tex:195`, inheriting `:8,11`: for compactly supported
  forces and zero initial velocity, relative density holds **if and only if**
  `s < 2/q-3/2`.

  Quantifier order: `ν, T`, positivity, `q`, membership of `q`, then `s`;
  unlike the one-way clause, there is no threshold hypothesis outside the
  equivalence. -/
  compactZeroIff :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ q : ℕ, (q = 1 ∨ q = 2) →
        ∀ s : ℝ,
          RelativelyDense (q : ℝ≥0∞) s forceClassCompact
              (breakdownSetIn forceClassCompact ν (fun _ => 0) T) ↔
            s < rClassesThreshold q

  /-- `04-whole-space.tex:195`, inheriting `:13`, with the mechanism explained
  at `:198`: around every compact-force reference regular beyond `T`, the
  approximants remain in `F_c`, preserve the datum and arbitrarily long
  earlier history, break down exactly at `T`, and approach in both the force
  norm and `E_T`.

  Quantifier order: theorem parameters through the subcritical hypothesis,
  datum, reference force, extension length, chosen reference solution, then
  the tolerances and history cutoff inside `HasReferenceApproximationRider`. -/
  compactReferenceApproximation :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ q : ℕ, (q = 1 ∨ q = 2) →
        ∀ s : ℝ, s < rClassesThreshold q →
          ∀ a : SpatialField, a ∈ initialClassR →
            ∀ g : SpaceTimeField, g ∈ forceClassCompact →
              ∀ δ : ℝ, 0 < δ →
                ∀ v : ClassicalSolutionR ν a g (T + δ),
                  HasReferenceApproximationRider
                    forceClassCompact ν T q s a g δ v

  /-- `04-whole-space.tex:195`, inheriting `:8-10`: for rapidly decaying
  forces, for every fixed `a ∈ X_R`, the breakdown set is relatively dense
  below the same threshold.

  Quantifier order is identical to `compactDenseBelow`, with only the ambient
  force class changed. -/
  rapidDenseBelow :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ q : ℕ, (q = 1 ∨ q = 2) →
        ∀ s : ℝ, ∀ a : SpatialField, a ∈ initialClassR →
          s < rClassesThreshold q →
            RelativelyDense (q : ℝ≥0∞) s forceClassRapid
              (breakdownSetIn forceClassRapid ν a T)

  /-- `04-whole-space.tex:195`, inheriting `:8,11`: for rapidly decaying
  forces and zero initial velocity, relative density holds **if and only if**
  `s < 2/q-3/2`; this is the corollary's emphasized "complete
  if-and-only-if classification at `a=0`".

  Quantifier order is identical to `compactZeroIff`. -/
  rapidZeroIff :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ q : ℕ, (q = 1 ∨ q = 2) →
        ∀ s : ℝ,
          RelativelyDense (q : ℝ≥0∞) s forceClassRapid
              (breakdownSetIn forceClassRapid ν (fun _ => 0) T) ↔
            s < rClassesThreshold q

  /-- `04-whole-space.tex:195`, inheriting `:13`, with preservation of the
  rapid class justified at `:198`: the reference and every approximating force
  are in `F_rd`, including all of its decay seminorm conditions.

  Quantifier order is identical to `compactReferenceApproximation`, with only
  the ambient force class changed. -/
  rapidReferenceApproximation :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ q : ℕ, (q = 1 ∨ q = 2) →
        ∀ s : ℝ, s < rClassesThreshold q →
          ∀ a : SpatialField, a ∈ initialClassR →
            ∀ g : SpaceTimeField, g ∈ forceClassRapid →
              ∀ δ : ℝ, 0 < δ →
                ∀ v : ClassicalSolutionR ν a g (T + δ),
                  HasReferenceApproximationRider
                    forceClassRapid ν T q s a g δ v

  /-- `04-whole-space.tex:192,195,198`: the explicitly highlighted
  rapid-decay formulation for every fixed Schwartz solenoidal initial datum.
  This is stated directly with `a ∈ S_σ`, rather than requiring the consumer
  first to prove the inclusion `S_σ ⊆ X_R`.

  Quantifier order: `ν, T`, positivity, `q`, membership of `q`, `s`, `a`,
  membership of `a` in `S_σ`, then the strict threshold hypothesis. -/
  rapidSchwartzDenseBelow :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ q : ℕ, (q = 1 ∨ q = 2) →
        ∀ s : ℝ, ∀ a : SpatialField, a ∈ initialClassSchwartz →
          s < rClassesThreshold q →
            RelativelyDense (q : ℝ≥0∞) s forceClassRapid
              (breakdownSetIn forceClassRapid ν a T)

  /-- `04-whole-space.tex:195`, inheriting `:13`, specialized to the
  corollary's explicitly named Schwartz solenoidal data in the rapid-decay
  class.  The zero-datum iff is already the stronger standalone
  `rapidZeroIff` clause above.

  Quantifier order follows `rapidReferenceApproximation`, replacing
  `a ∈ X_R` by `a ∈ S_σ`. -/
  rapidSchwartzReferenceApproximation :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ q : ℕ, (q = 1 ∨ q = 2) →
        ∀ s : ℝ, s < rClassesThreshold q →
          ∀ a : SpatialField, a ∈ initialClassSchwartz →
            ∀ g : SpaceTimeField, g ∈ forceClassRapid →
              ∀ δ : ℝ, 0 < δ →
                ∀ v : ClassicalSolutionR ν a g (T + δ),
                  HasReferenceApproximationRider
                    forceClassRapid ν T q s a g δ v

end BlowupDensity.Research.R45.DraftA
