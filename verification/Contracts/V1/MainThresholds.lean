import Contracts.V1.Data

/-! Theorem 4.1 for Y = F_R. The four-field structure below is copied verbatim
from research/R41/Spec.lean, apart from the registry-conventional name. -/
noncomputable section
namespace BlowupDensity.Contracts.V1.MainThresholds
open Filter Set
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal Topology

structure MainThresholdsAPI where
  /-- Clause (i), `04-whole-space.tex:8-10`.

  Exact order: for every `ν : ℝ`, assume `0 < ν`; for every `T : ℝ`, assume
  `0 < T`; for every `q : ℝ≥0∞`, assume `q = 1 ∨ q = 2`; for every `s : ℝ`;
  for every `a : SpatialField`, assume `a ∈ initialClassR`; finally assume
  `s < criticalOrder q.toReal`, and conclude relative density of the breakdown
  set in `forceClassR`.

  Non-vacuity: `BreakdownDenseR` expands to approximation of every registered
  reference force at every positive radius by a force whose registered maximal
  lifespan is at most `T`; it is not an unconstrained proposition. -/
  fixedInitialDensity :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        ∀ a : SpatialField, a ∈ initialClassR →
          s < criticalOrder q.toReal → BreakdownDenseR ν a T q s

  /-- Clause (ii), `04-whole-space.tex:8,11`.

  Exact order: for every `ν : ℝ`, assume `0 < ν`; for every `T : ℝ`, assume
  `0 < T`; for every `q : ℝ≥0∞`, assume `q = 1 ∨ q = 2`; then for every
  `s : ℝ`, density at the zero initial velocity holds if and only if
  `s < criticalOrder q.toReal`.  The single biconditional keeps both directions
  under exactly the same hypotheses and includes non-density at equality.

  Non-vacuity: the left side is the registered positive-radius definition of
  relative density in `forceClassR`, specialized to the concrete registered
  zero-data breakdown set. -/
  zeroInitialDensityIff :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        RelativelyDense q s forceClassR (breakdownSetRZero ν T) ↔
          s < criticalOrder q.toReal

  /-- The numerical sentence of `04-whole-space.tex:13`: the thresholds are
  `1/2` for `L¹_t H^s_x` and `-1/2` for `L²_t H^s_x`.

  Exact order: there are no quantifiers; this is the conjunction of the two
  values of the same registered function used by the density fields.

  Non-vacuity: both conjuncts are explicit real equalities, rather than an
  imported arithmetic API or an opaque proposition. -/
  thresholdValues :
    criticalOrder 1 = (1 : ℝ) / 2 ∧ criticalOrder 2 = -(1 : ℝ) / 2

  /-- The regular-reference rider of `04-whole-space.tex:13`, expanded using
  the same-family conclusions at `04-whole-space.tex:32-42`.

  Exact order: for every `ν > 0`, `T > 0`, `q : ℝ≥0∞` with `q = 1 ∨ q = 2`,
  and `s < criticalOrder q.toReal`; for every `a ∈ initialClassR` and every
  `g` satisfying `MemForceR`; for every `δ > 0` and every named reference
  `v : ClassicalSolutionR ν a g (T + δ)`; there exist `ε₀ > 0` and one pair of
  total families `f,u`.  For every `ε ∈ (0,ε₀)`, that family has a force in
  `forceClassR`, exact lifespan `T`, and a classical solution with datum `a`
  whose velocity is `u ε` and agrees with `v` on `[0,T-2ε²]`.  The force and
  velocity differences for those same families tend to zero as `ε ↓ 0` in the
  stated `L^q_tH^s_x` and `E_T` norms.

  The explicit `ClassicalSolutionR ν a (f ε) T` carries the unchanged initial
  velocity; exact lifespan represents “singularity exactly at `T`.”  The
  separate unbounded-speed display of `04-whole-space.tex:35`, support claims,
  and quantitative rate are not restated here.

  Non-vacuity: the existential witnesses are jointly constrained by force-class
  membership, exact registered lifespan, a full registered solution, pointwise
  history, and two one-sided norm limits; no witness can discharge the field by
  inhabiting an unconstrained proposition. -/
  regularReferenceApproximation :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        s < criticalOrder q.toReal →
          ∀ a : SpatialField, a ∈ initialClassR →
            ∀ g : SpaceTimeField, MemForceR g →
              ∀ δ : ℝ, 0 < δ → ∀ v : ClassicalSolutionR ν a g (T + δ),
                ∃ ε₀ : ℝ, 0 < ε₀ ∧
                  ∃ f u : ℝ → SpaceTimeField,
                    (∀ ε ∈ Ioo 0 ε₀,
                      MemForceR (f ε) ∧
                      maximalLifespanR ν a (f ε) = ENNReal.ofReal T ∧
                      ∃ U : ClassicalSolutionR ν a (f ε) T,
                        U.velocity = u ε ∧
                        ∀ t ∈ Icc 0 (T - 2 * ε ^ 2), ∀ x,
                          u ε (t, x) = v.velocity (t, x)) ∧
                    Tendsto (fun ε => forceSobolevENorm q s (f ε - g))
                      (𝓝[>] 0) (𝓝 0) ∧
                    Tendsto (fun ε => energyENorm T (u ε - v.velocity))
                      (𝓝[>] 0) (𝓝 0)


end BlowupDensity.Contracts.V1.MainThresholds
