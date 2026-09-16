import Contracts.V1.Data
import Contracts.V1.Thresholds

/-!
Independent statement of `cor:Rclasses`, paper/sections/04-whole-space.tex:194-198.
Only registered vocabulary is imported. No implementation or other draft is used.
The two choices of ambient class are explicit equalities, not arbitrary subclasses.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.RClassesDraftB

open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-- Corollary 4.x, `04-whole-space.tex:194-198`, including the conclusions
inherited from Theorem 4.1 (`04-whole-space.tex:8-13`). This is a specification
record, not an assertion that the record has an inhabitant. -/
structure RClassesAPI where
  /-- `04-whole-space.tex:195`, inheriting `:8-10`.
  Quantifier order: ambient Y, choice of class, ν > 0, T > 0, real q ∈ {1,2},
  real s, fixed a ∈ X_R, s < 2/q - 3/2; then relative density in Y.
  In particular the target and the approximating force both belong to Y. -/
  density :
    ∀ Y : Set SpaceTimeField, (Y = forceClassCompact ∨ Y = forceClassRapid) →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ q : ℝ, (q = 1 ∨ q = 2) → ∀ s : ℝ,
          ∀ a : SpatialField, a ∈ initialClassR → s < 2 / q - 3 / 2 →
            RelativelyDense (ENNReal.ofReal q) s Y (breakdownSetIn Y ν a T)
  /-- `04-whole-space.tex:195`, inheriting `:8,11`.
  Quantifier order: Y, class choice, ν > 0, T > 0, real q ∈ {1,2}, real s;
  density at the zero datum iff s < 2/q - 3/2. Includes equality and every
  supercritical s in the nondensity direction, for each of the two classes. -/
  zeroIff :
    ∀ Y : Set SpaceTimeField, (Y = forceClassCompact ∨ Y = forceClassRapid) →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ q : ℝ, (q = 1 ∨ q = 2) → ∀ s : ℝ,
          RelativelyDense (ENNReal.ofReal q) s Y
              (breakdownSetIn Y ν (fun _ => 0) T) ↔ s < 2 / q - 3 / 2
  /-- `04-whole-space.tex:195,198`: explicit Schwartz-data specialization.
  Quantifier order: ν > 0, T > 0, q ∈ {1,2}, s, fixed a ∈ S_σ, subcriticality;
  then density in F_rd. There is no extra X_R hypothesis on the Schwartz datum.
  The complete zero-datum classification is the F_rd instance of zeroIff. -/
  schwartzDensity :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        ∀ a : SpatialField, a ∈ initialClassSchwartz → s < 2 / q - 3 / 2 →
          RelativelyDense (ENNReal.ofReal q) s forceClassRapid
            (breakdownSetIn forceClassRapid ν a T)
  /-- `04-whole-space.tex:195,198`, inheriting `:13`; earlier history is
  made precise by `:36`, and terminal unbounded speed by `:35`.
  Quantifier order: Y and its class choice; ν > 0; T > 0; q ∈ {1,2}; s below
  threshold; fixed a in X_R or S_σ; g ∈ Y; δ > 0; a reference solution v on
  [0,T+δ); any history cutoff 0 ≤ τ < T; positive force and energy radii r, η;
  then ONE force f ∈ Y and ONE classical solution u with datum a on [0,T).
  Both norm bounds, exact lifespan T, and pointwise velocity history on [0,τ]
  hold for these same witnesses. The last quantifiers say that arbitrarily
  large speeds occur arbitrarily close to T from below (the displayed limsup).
  Arbitrary η is the epsilon formulation of the E_T limit. -/
  regularReference :
    ∀ Y : Set SpaceTimeField, (Y = forceClassCompact ∨ Y = forceClassRapid) →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ q : ℝ, (q = 1 ∨ q = 2) → ∀ s : ℝ, s < 2 / q - 3 / 2 →
          ∀ a : SpatialField, (a ∈ initialClassR ∨ a ∈ initialClassSchwartz) →
            ∀ g : SpaceTimeField, g ∈ Y → ∀ δ : ℝ, 0 < δ →
              ∀ v : ClassicalSolutionR ν a g (T + δ),
                ∀ τ : ℝ, 0 ≤ τ → τ < T →
                  ∀ r η : ℝ≥0∞, 0 < r → 0 < η →
                    ∃ f : SpaceTimeField, f ∈ Y ∧
                      ∃ u : ClassicalSolutionR ν a f T,
                        maximalLifespanR ν a f = ENNReal.ofReal T ∧
                        forceSobolevENorm (ENNReal.ofReal q) s (f - g) < r ∧
                        energyENorm T (u.velocity - v.velocity) < η ∧
                        (∀ t : ℝ, 0 ≤ t → t ≤ τ → ∀ x : NavierStokes.ProblemStatement.Space,
                          u.velocity (t, x) = v.velocity (t, x)) ∧
                        (∀ M : ℝ, ∀ t₀ : ℝ, t₀ < T →
                          ∃ t : ℝ, max 0 t₀ < t ∧ t < T ∧
                            ∃ x : NavierStokes.ProblemStatement.Space, M < ‖u.velocity (t, x)‖)

end BlowupDensity.Contracts.V1.RClassesDraftB
