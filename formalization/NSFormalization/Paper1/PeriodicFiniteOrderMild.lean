import NSFormalization.Paper1.PeriodicOrdinaryLocal
import NSFormalization.Paper1.PeriodicOrdinaryObstruction
import Euler.SobolevJointEvaluation

/-!
# Finite-order periodic mild data and the missing classical bridge

`OrdinaryForcedLocal` already returns a genuine finite-order cylinder mild
path.  This file packages that output without changing its status.  The
pointwise periodic representative below is canonical at Sobolev order at
least three: angle invariance identifies every cylinder representative with
its value at angle zero.  The final bridge to `PeriodicLifespan.Flow` is kept
as an explicit structure.  In particular, continuity of an `H^q` path does
not by itself provide spacetime `C^∞` regularity, pressure recovery, or the
pointwise Navier--Stokes equation.
-/

noncomputable section

namespace NSFormalization.Paper1.PeriodicFiniteOrderMild

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1.PeriodicInitialData
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicOrdinaryLocal
open NSFormalization.Paper1.PeriodicOrdinaryObstruction
open NSFormalization.Source
open EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSobolevSpace
open EulerSobolevPointEvaluation EulerSobolevJointEvaluation
open scoped ContDiff Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-! ## The actual finite-order output -/

/-- The complete finite-order output of the existing ordinary cylinder solver.

The fields deliberately mirror `OrdinaryForcedLocal.exists_local`: `u` is a
continuous path in a cylinder Sobolev space, `U` is its ordinary `L²`
observation, and the last three fields retain divergence, the Duhamel law,
and angle invariance.  No classical spacetime field is hidden in this
structure.
-/
structure CylinderMildWitness
    {q : ℕ} (hq : 6 ≤ q) (ν S : ℝ)
    (a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space)
    (A : OrdinaryRepresentative a)
    (F : Icc (0 : ℝ) S → EulerLpTranslation.SmoothL2Field EulerSmoothLimit.Space)
    (hF : ∀ n, Continuous (fun t => (F t).jetLp n)) where
  T : ℝ
  hT : 0 < T
  hTS : T ≤ S
  viscosity_pos : 0 < ν
  u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))
  U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2)
  norm_bound :
    ‖u‖ ≤ ‖EulerMeanSmoothRepresentative.ordinarySobolev (q + 1)
      A.field.toLp A.field.translation_contDiff‖ + 1
  initial :
    u ⟨0, le_rfl, hT.le⟩ =
      EulerMeanSmoothRepresentative.ordinarySobolev (q + 1)
        A.field.toLp A.field.translation_contDiff
  initial_L2 : U ⟨0, le_rfl, hT.le⟩ = A.field.toLp
  realization : ∀ t, EulerMeanOrdinaryLift.ordinaryLift (U t) =
    EulerCylinderSobolevSpace.value 1 (u t)
  divergence : ∀ t, EulerCylinderSobolevSpace.value 1 (u t) ∈
    EulerLiftedGradientSpace.divergenceFreeSpace 1 1 0
  mild : ∀ t, u t = EulerQuadraticSource.quadraticDuhamel 1 ν viscosity_pos hT.le hTS
    (NSFormalization.Source.ForcedCylinderLocal.coefficients 1 hq
      (EulerSmoothFieldSobolevTime.sobolevPath F hF q))
    (EulerMeanSmoothRepresentative.ordinarySobolev (q + 1)
      A.field.toLp A.field.translation_contDiff) u t
  angleInvariant : ∀ (θ : AddCircle (1 : ℝ)) t,
    EulerCylinderSobolevSpace.sobolevTranslation 1 (q + 1) (0, θ)
      (u t) = u t

/-! ## Packaging of the finite-order bridge -/

theorem exists_cylinderMildWitness
    {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    (ha : IsAdmissibleInitialData a)
    (A : OrdinaryRepresentative a)
    (F : Icc (0 : ℝ) S → EulerLpTranslation.SmoothL2Field EulerSmoothLimit.Space)
    (hF : ∀ n, Continuous (fun t => (F t).jetLp n)) :
    Nonempty (CylinderMildWitness hq ν S a A F hF) := by
  obtain ⟨T, hT, hTS, u, U, hnorm, hi, hiL2, hreal, hdiv, hmild, hinv⟩ :=
    exists_finiteOrder_local_of_representative hq hν hS ha A F hF
  exact ⟨{
    T := T
    hT := hT
    hTS := hTS
    viscosity_pos := hν
    u := u
    U := U
    norm_bound := hnorm
    initial := hi
    initial_L2 := hiL2
    realization := hreal
    divergence := hdiv
    mild := hmild
    angleInvariant := hinv
  }⟩

/-! ## Energy-facing consequences

These estimates are deliberately modest: they expose the uniform-in-time
bound already carried by `CylinderMildWitness`.  They are useful as the
bounded-input side of a future Picard/continuation theorem, while making no
claim that the nonlinear contraction estimate has been formalised.
-/

theorem witness_pointwise_norm_le
    {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {A : OrdinaryRepresentative a}
    {F : Icc (0 : ℝ) S → EulerLpTranslation.SmoothL2Field EulerSmoothLimit.Space}
    {hF : ∀ n, Continuous (fun t => (F t).jetLp n)}
    (W : CylinderMildWitness hq ν S a A F hF) (t : Icc (0 : ℝ) W.T) :
    ‖W.u t‖ ≤ ‖EulerMeanSmoothRepresentative.ordinarySobolev (q + 1)
      A.field.toLp A.field.translation_contDiff‖ + 1 := by
  exact le_trans (W.u.norm_coe_le_norm t) W.norm_bound

theorem witness_pointwise_sq_norm_le
    {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {A : OrdinaryRepresentative a}
    {F : Icc (0 : ℝ) S → EulerLpTranslation.SmoothL2Field EulerSmoothLimit.Space}
    {hF : ∀ n, Continuous (fun t => (F t).jetLp n)}
    (W : CylinderMildWitness hq ν S a A F hF) (t : Icc (0 : ℝ) W.T) :
    ‖W.u t‖ ^ 2 ≤
      (‖EulerMeanSmoothRepresentative.ordinarySobolev (q + 1)
        A.field.toLp A.field.translation_contDiff‖ + 1) ^ 2 := by
  have h := witness_pointwise_norm_le hq W t
  have hu : 0 ≤ ‖W.u t‖ := norm_nonneg _
  have hr : 0 ≤ ‖EulerMeanSmoothRepresentative.ordinarySobolev (q + 1)
      A.field.toLp A.field.translation_contDiff‖ + 1 := by positivity
  nlinarith [h]

end NSFormalization.Paper1.PeriodicFiniteOrderMild

namespace NSFormalization.Paper1.PeriodicFiniteOrderMild
open Set MeasureTheory
open NSFormalization.Paper1.PeriodicInitialData
open NSFormalization.Paper1.PeriodicOrdinaryLocal
open NSFormalization.Paper1.PeriodicLifespan
open EulerSmoothLimit EulerLpTranslation

/-- The canonical time measure on the subtype of a closed finite interval.

This is the explicit pullback of restricted Lebesgue measure used whenever a
path is represented as a function on `Icc 0 T`.  Naming it avoids repeatedly
reconstructing the measure and makes downstream integrability statements
independent of typeclass inference for subtype measures. -/
def intervalSubtypeMeasure (T : ℝ) : Measure (Set.Icc (0 : ℝ) T) :=
  Measure.comap Subtype.val (volume.restrict (Set.Icc (0 : ℝ) T))

/-- A continuous real-valued profile on a closed time interval is integrable on
the whole subtype for the canonical explicit time measure.  The `IntegrableOn`
form avoids requiring a global finite-measure instance for the subtype. -/
theorem continuous_intervalSubtypeMeasure_integrableOn
    {T : ℝ} {g : Set.Icc (0 : ℝ) T → ℝ}
    (hg : Continuous g) :
    IntegrableOn g Set.univ
      (Measure.comap Subtype.val (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  apply ContinuousOn.integrableOn_compact
    (μ := Measure.comap Subtype.val (volume.restrict (Set.Icc (0 : ℝ) T))) isCompact_univ
  exact hg.continuousOn

/-- The Sobolev norm along a finite-order mild path is continuous in time.
This is the time-regularity interface needed before integrating Picard energy
bounds; it uses only the continuous-map component of the witness. -/
theorem witness_norm_continuous
    {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {A : OrdinaryRepresentative a}
    {F : Set.Icc (0 : ℝ) S → EulerLpTranslation.SmoothL2Field EulerSmoothLimit.Space}
    {hF : ∀ n, Continuous (fun t => (F t).jetLp n)}
    (W : CylinderMildWitness hq ν S a A F hF) :
    Continuous (fun t : Set.Icc (0 : ℝ) W.T => ‖W.u t‖) := by
  exact W.u.continuous.norm

end NSFormalization.Paper1.PeriodicFiniteOrderMild


namespace NSFormalization.Paper1.PeriodicFiniteOrderMild
open Set MeasureTheory
open NSFormalization.Paper1.PeriodicInitialData
open NSFormalization.Paper1.PeriodicOrdinaryLocal
open NSFormalization.Paper1.PeriodicLifespan
open EulerSmoothLimit EulerLpTranslation

/-- Square norm is integrable for the explicit pullback of restricted Lebesgue
measure along the subtype inclusion.  This keeps the measure visible instead
of relying on a missing default measure-space instance on `Icc`. -/
theorem witness_sq_norm_integrable_restrict
    {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {A : OrdinaryRepresentative a}
    {F : Set.Icc (0 : ℝ) S → EulerLpTranslation.SmoothL2Field EulerSmoothLimit.Space}
    {hF : ∀ n, Continuous (fun t => (F t).jetLp n)}
    (W : CylinderMildWitness hq ν S a A F hF) :
    IntegrableOn (fun t : Set.Icc (0 : ℝ) W.T => ‖W.u t‖ ^ 2) Set.univ
      (intervalSubtypeMeasure W.T) := by
  change IntegrableOn (fun t : Set.Icc (0 : ℝ) W.T => ‖W.u t‖ ^ 2)
    Set.univ (Measure.comap Subtype.val (volume.restrict (Set.Icc (0 : ℝ) W.T)))
  apply ContinuousOn.integrableOn_compact
    (μ := Measure.comap Subtype.val (volume.restrict (Set.Icc (0 : ℝ) W.T))) isCompact_univ
  exact ((witness_norm_continuous hq W).pow 2).continuousOn
