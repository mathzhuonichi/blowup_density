import Contracts.V1.Data

/-!
# R45 reconciled specification: Corollary `cor:Rclasses`

Statement and proof: `paper/sections/04-whole-space.tex:194-199`; inherited
Theorem 4.1 clauses: `:8-13`.  This is the binding reconciliation of the two
independent statement drafts `DraftA.lean` (lane 238) and `DraftB.lean` (lane
239), following `research/R45/RECONCILIATION.md` exactly.

The record has the four reconciled fields `density`, `zeroIff`,
`schwartzDensity`, and `regularReference`.  The first, second, and fourth are
parametric in an ambient class `Y`, with an explicit proof that `Y` is exactly
`forceClassCompact` or `forceClassRapid`; this does not assert anything for an
arbitrary force subclass.  Every exponent is `q : ℝ≥0∞`, restricted by
`q = 1 ∨ q = 2`, and every threshold is the registered
`criticalOrder q.toReal` (`Contracts/V1/Data.lean:259`).

The rider is the reconciled inline epsilon form.  It retains a given datum in
`initialClassR`, a reference solution beyond `T`, arbitrary earlier cutoff
`τ < T`, exact approximating lifespan `T`, force closeness, `E_T` closeness, and
pointwise velocity agreement on `[0,τ]`.  It deliberately does not repeat
terminal unbounded speed: that is Theorem 4.2's blow-up clause
(`04-whole-space.tex:35`) and belongs to the R42 contract, while the corollary's
text only inherits Theorem 4.1's rider (`:13`).

This file is a specification.  It introduces one structure, no abstract
proposition parameter, no placeholder field, and no mathematical proof.  The
two `example ... := rfl` declarations after the record are only the requested
definitional checks for the registered completed-space abbreviations; neither
completed-space predicate is a clause of this corollary.
-/

noncomputable section

namespace BlowupDensity.R45.Draft

open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-! ## The reconciled contract -/

/-- **Corollary `cor:Rclasses`**
(`paper/sections/04-whole-space.tex:194-199`): all clauses of Theorem 4.1
(`:8-13`) with the ambient force class replaced by either compactly supported
forces `F_c` or rapidly decaying forces `F_rd`, together with the explicitly
stated Schwartz-datum specialization for `F_rd` (`:195,198`).

The structure itself asserts no theorem; an inhabitant must supply all four
fully expanded conclusions below. -/
structure RClassesAPI where
  /-- `04-whole-space.tex:195`, inheriting Theorem 4.1(i) at `:8-10`: in either
  `F_c` or `F_rd`, the by-time-`T` breakdown forces are relatively dense below
  `s_q = 2/q - 3/2` for every fixed `a ∈ X_R`.

  Exact quantifier order: `Y`; proof that `Y = F_c` or `Y = F_rd`; `ν`; `ν>0`;
  `T`; `T>0`; `q : ℝ≥0∞`; `q=1 ∨ q=2`; `s`; `a`; `a∈X_R`; the strict
  threshold hypothesis; then relative density.

  Non-vacuity: `RelativelyDense` (`Data.lean:702-703`) requires, for every
  target `g ∈ Y` and every positive radius, an `f` in
  `breakdownSetIn Y ν a T`; that membership simultaneously forces `f ∈ Y` and
  `maximalLifespanR ν a f ≤ ENNReal.ofReal T` (`Data.lean:672-674`). -/
  density :
    ∀ Y : Set SpaceTimeField, (Y = forceClassCompact ∨ Y = forceClassRapid) →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
          ∀ a : SpatialField, a ∈ initialClassR →
            s < criticalOrder q.toReal →
              RelativelyDense q s Y (breakdownSetIn Y ν a T)

  /-- `04-whole-space.tex:195`, inheriting Theorem 4.1(ii) at `:8,11`: in
  either `F_c` or `F_rd`, the zero-datum breakdown set is relatively dense if
  and only if `s < s_q`.

  Exact quantifier order: `Y`; proof that `Y = F_c` or `Y = F_rd`; `ν`; `ν>0`;
  `T`; `T>0`; `q : ℝ≥0∞`; `q=1 ∨ q=2`; `s`; then the equivalence.  In
  particular, the threshold inequality is not an outer hypothesis.

  Non-vacuity: the reverse implication is retained, so the field includes
  non-density at the critical order and above; it cannot be discharged merely
  by reusing the subcritical `density` field.  The zero datum is the concrete
  spatial field `fun _ => 0`, not an unspecified initial datum. -/
  zeroIff :
    ∀ Y : Set SpaceTimeField, (Y = forceClassCompact ∨ Y = forceClassRapid) →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
          RelativelyDense q s Y
              (breakdownSetIn Y ν (fun _ => 0) T) ↔
            s < criticalOrder q.toReal

  /-- `04-whole-space.tex:195,198`: the explicitly highlighted rapid-decay
  specialization for every fixed Schwartz solenoidal datum `a ∈ S_σ`, below
  the same threshold.

  Exact quantifier order: `ν`; `ν>0`; `T`; `T>0`; `q : ℝ≥0∞`;
  `q=1 ∨ q=2`; `s`; `a`; `a∈S_σ`; the strict threshold hypothesis; then
  relative density in `F_rd`.  There is no extra `a ∈ X_R` premise; proving
  `S_σ ⊆ X_R` is the G4 proof dependency, not a caller obligation.

  Non-vacuity: the conclusion uses `breakdownSetIn forceClassRapid`, hence each
  witness must itself be rapidly decaying and must break down by `T`; it is not
  merely an approximation by an arbitrary `F_R` force. -/
  schwartzDensity :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        ∀ a : SpatialField, a ∈ initialClassSchwartz →
          s < criticalOrder q.toReal →
            RelativelyDense q s forceClassRapid
              (breakdownSetIn forceClassRapid ν a T)

  /-- `04-whole-space.tex:195,198`, inheriting Theorem 4.1's regular-reference
  rider at `:13`; the arbitrary history cutoff is the parameter-free rendering
  of Theorem 4.2's expanding common history at `:36`.

  Exact quantifier order: `Y`; proof that `Y = F_c` or `Y = F_rd`; `ν`; `ν>0`;
  `T`; `T>0`; `q : ℝ≥0∞`; `q=1 ∨ q=2`; `s`; the strict threshold hypothesis;
  `a`; `a∈X_R`; `g`; `g∈Y`; `δ`; `δ>0`; a reference solution `v` on
  `[0,T+δ)`; `τ`; `0≤τ`; `τ<T`; force and energy radii `r,η`; `0<r`; `0<η`;
  then one approximating force `f` and one classical solution `u` satisfying
  all five retained conclusions for those same witnesses.

  Non-vacuity: `f ∈ Y`, exact equality
  `maximalLifespanR ν a f = ENNReal.ofReal T`, and both strict norm bounds are
  simultaneous.  The solution indices force the reference and approximant to
  have the same initial datum `a`, while the last conjunct gives pointwise
  velocity equality throughout `[0,τ]`.  Positive independent radii express
  genuine convergence in both norms.  No unbounded-speed conjunct is present,
  exactly as the reconciliation requires. -/
  regularReference :
    ∀ Y : Set SpaceTimeField, (Y = forceClassCompact ∨ Y = forceClassRapid) →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) →
          ∀ s : ℝ, s < criticalOrder q.toReal →
            ∀ a : SpatialField, a ∈ initialClassR →
              ∀ g : SpaceTimeField, g ∈ Y → ∀ δ : ℝ, 0 < δ →
                ∀ v : ClassicalSolutionR ν a g (T + δ),
                  ∀ τ : ℝ, 0 ≤ τ → τ < T →
                    ∀ r η : ℝ≥0∞, 0 < r → 0 < η →
                      ∃ f : SpaceTimeField, f ∈ Y ∧
                        ∃ u : ClassicalSolutionR ν a f T,
                          maximalLifespanR ν a f = ENNReal.ofReal T ∧
                          forceSobolevENorm q s (f - g) < r ∧
                          energyENorm T (u.velocity - v.velocity) < η ∧
                          (∀ t : ℝ, 0 ≤ t → t ≤ τ →
                            ∀ x : NavierStokes.ProblemStatement.Space,
                            u.velocity (t, x) = v.velocity (t, x))

/-! ## Requested definitional checks

`CompletedDense` and `CompletedDenseHomogeneous` are registered abbreviations
for the two corresponding `CompletedDenseVia` realizations
(`Contracts/V1/Data.lean:732-753`).  These checks are deliberately outside
`RClassesAPI`: Corollary `cor:Rclasses` concerns relative density inside the
smooth classes, not density in either completed force space. -/

example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDense q s S = CompletedDenseVia q s (IsSobolevPath s) S := rfl

example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDenseHomogeneous q s S =
      CompletedDenseVia q s (IsHomogeneousPath s) S := rfl

end BlowupDensity.R45.Draft
