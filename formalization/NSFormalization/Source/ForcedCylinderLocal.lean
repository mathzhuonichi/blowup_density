import Euler.QuadraticHeatConstraint
import Euler.SobolevWordConstraints
import Euler.LiftedTransportComponents

/-!
# Reuse of the source heat solver for the actual forced transport equation

This is an adapter to the existing complete cylinder Sobolev spaces. The
projection, transport product, heat kernel and Picard argument are all source
constructions. No nonlinear estimate or local solution is assumed.

Ordinary whole-space data require a separate angle-independent-subspace
bridge. This module alone does not assert the manuscripts' local theorem.
-/
noncomputable section
namespace NSFormalization.Source.ForcedCylinderLocal
open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
open EulerSobolevWordConstraints EulerSobolevTransport EulerQuadraticSource
open EulerSobolevHeat EulerDivergenceFreeHeat
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine Leray projection at ordinary spatial scale, lifted to the
source's complete Sobolev derivative graph. -/
def leray (q : ℕ) : SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  ContinuousLinearMap.id ℝ _ - sobolevGradientProjection period q 1 0

theorem leray_value {q : ℕ} (u : SobolevSpace period q) :
    value period (leray period q u) = value period u - gradientProjection period 1 0 (value period u) := rfl

theorem leray_gradient_zero {q : ℕ} (u : SobolevSpace period q) :
    gradientProjection period 1 0 (value period (leray period q u)) = 0 := by
  rw [leray_value, map_sub]
  change (gradientSpace period 1 0).starProjection (value period u) -
    (gradientSpace period 1 0).starProjection
      ((gradientSpace period 1 0).starProjection (value period u)) = 0
  have h := congrArg (fun p => p (value period u))
    (gradientSpace period 1 0).isIdempotentElem_starProjection.eq
  apply sub_eq_zero.mpr
  simpa only [mul_apply_eq_comp] using h.symm

/-- Literal spatial advection, with zero coefficient for the auxiliary angle
derivative. The existing algebra proof supplies its bounded bilinear map. -/
def advection {q : ℕ} (hq : 6 ≤ q) :
    SobolevSpace period (q + 1) →L[ℝ]
      SobolevSpace period (q + 1) →L[ℝ] SobolevSpace period q :=
  transportBilinear period hq (velocityComponents 1 0)
    (velocityComponents_norm 1 0 (by norm_num) (by simp))

/-- Coefficients have source term P f - P ((u·∇)u). -/
def coefficients {q : ℕ} (hq : 6 ≤ q) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace period q)) :
    Coefficients (Icc (0 : ℝ) S) (SobolevSpace period (q + 1)) (SobolevSpace period q) where
  projection := ContinuousMap.const _ (leray period q)
  forcing := -f
  linear := 0
  quadratic := ContinuousMap.const _ (advection period hq)

theorem source_eq {q : ℕ} (hq : 6 ≤ q) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace period q))
    (t : Icc (0 : ℝ) S) (u : SobolevSpace period (q + 1)) :
    (coefficients period hq f).apply t u =
      leray period q (f t - advection period hq u u) := by
  simp only [Coefficients.apply, coefficients, source, ContinuousMap.const_apply,
    ContinuousMap.neg_apply, ContinuousMap.zero_apply, zero_apply, add_zero, map_add,
    map_neg, map_sub]
  abel

/-- The existing Gaussian heat and quadratic Picard theorems directly give
positive-time existence for actual projected forced spatial advection. -/
theorem exists_local_forced_mild {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    (hν : 0 < ν) (hS : 0 < S)
    (u₀ : SobolevSpace period (q + 1))
    (hu₀ : value period u₀ ∈ divergenceFreeSpace period 1 0)
    (f : C(Icc (0 : ℝ) S, SobolevSpace period q)) :
    ∃ (T : ℝ) (hT : 0 < T) (hTS : T ≤ S),
      ∃ u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)),
        ‖u‖ ≤ ‖u₀‖ + 1 ∧ u ⟨0, le_rfl, hT.le⟩ = u₀ ∧
        (∀ t, value period (u t) ∈ divergenceFreeSpace period 1 0) ∧
        ∀ t, u t = quadraticDuhamel period ν hν hT.le hTS
          (coefficients period hq f) u₀ u t := by
  apply exists_local_quadratic_divergenceFree period q ν hν S hS 1 0 u₀
    ((gradientEvaluation_zero_iff period 1 0 u₀).mpr hu₀) (coefficients period hq f)
  intro t u
  rw [source_eq]
  exact leray_gradient_zero period _

end NSFormalization.Source.ForcedCylinderLocal
