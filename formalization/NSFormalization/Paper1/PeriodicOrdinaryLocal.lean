import NSFormalization.Paper1.PeriodicInitialData
import NSFormalization.Source.OrdinaryForcedLocal

/-!
# The exact periodic-to-ordinary local-existence bridge

`OrdinaryForcedLocal.exists_local` is a genuine finite-order solver on ordinary
`L²(R³)` data.  The manuscript initial data live on the periodic space, so the
solver cannot be applied by coercion alone.  This file records the missing
coercion as an explicit `SmoothL2Field` representative hypothesis and then
performs only the valid finite-order transport.

No existence of such an ordinary representative is asserted here: for a
nonzero periodic field that assertion would conflict with ordinary `L²`
integrability.  Thus the theorem below is an interface, rather than an
unproved periodic local-existence theorem.
-/

noncomputable section
namespace NSFormalization.Paper1.PeriodicOrdinaryLocal

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1.PeriodicInitialData
open NSFormalization.Source
open EulerSmoothLimit EulerLpTranslation EulerMeanSmoothRepresentative
open EulerMeanOrdinaryLift EulerLiftedGradientSpace
open scoped ContDiff Topology

/-- The extra datum needed before an ordinary finite-order solver can see a
periodic manuscript initial field.  The equality is pointwise, while `field`
comes with genuine ordinary `L²` jets. -/
structure OrdinaryRepresentative (a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space) where
  field : SmoothL2Field EulerSmoothLimit.Space
  field_eq : field.field = a

/-- The Euler divergence of an ordinary representative is exactly the
manuscript coordinate divergence once the representatives agree. -/
theorem OrdinaryRepresentative.divergence_free
    {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space} (ha : IsAdmissibleInitialData a)
    (A : OrdinaryRepresentative a) :
    ∀ x, EulerSmoothLimit.divergence A.field.field x = 0 := by
  intro x
  rw [A.field_eq]
  rw [EulerSmoothLimit.divergence_eq_coordinate_sum]
  simpa only [NavierStokes.ProblemStatement.spatialDerivative,
    NavierStokes.ProblemStatement.coordinateVector] using ha.divergence_free x

/-- The finite-order ordinary local witness obtained from an explicit
ordinary representative of admissible periodic data.  This is precisely the
output of the existing cylinder solver; no pressure reconstruction or
periodic-flow identification is smuggled into the statement. -/
theorem exists_finiteOrder_local_of_representative
    {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space} (ha : IsAdmissibleInitialData a)
    (A : OrdinaryRepresentative a)
    (F : Icc (0 : ℝ) S → SmoothL2Field EulerSmoothLimit.Space)
    (hF : ∀ n, Continuous (fun t => (F t).jetLp n)) :
    ∃ (T : ℝ) (hT : 0 < T) (hTS : T ≤ S),
      ∃ (u : C(Icc (0 : ℝ) T,
          EulerCylinderSobolevSpace.SobolevSpace 1 (q + 1)))
        (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2)),
        ‖u‖ ≤ ‖EulerMeanSmoothRepresentative.ordinarySobolev (q + 1)
          A.field.toLp A.field.translation_contDiff‖ + 1 ∧
        u ⟨0, le_rfl, hT.le⟩ =
          EulerMeanSmoothRepresentative.ordinarySobolev (q + 1)
            A.field.toLp A.field.translation_contDiff ∧
        U ⟨0, le_rfl, hT.le⟩ = A.field.toLp ∧
        (∀ t, EulerMeanOrdinaryLift.ordinaryLift (U t) =
          EulerCylinderSobolevSpace.value 1 (u t)) ∧
        (∀ t, EulerCylinderSobolevSpace.value 1 (u t) ∈
          EulerLiftedGradientSpace.divergenceFreeSpace 1 1 0) ∧
        (∀ t, u t = EulerQuadraticSource.quadraticDuhamel 1 ν hν hT.le hTS
          (NSFormalization.Source.ForcedCylinderLocal.coefficients 1 hq
            (EulerSmoothFieldSobolevTime.sobolevPath F hF q))
          (EulerMeanSmoothRepresentative.ordinarySobolev (q + 1)
            A.field.toLp A.field.translation_contDiff) u t) ∧
        ∀ (θ : AddCircle (1 : ℝ)) t,
          EulerCylinderSobolevSpace.sobolevTranslation 1 (q + 1) (0, θ)
            (u t) = u t := by
  exact NSFormalization.Source.OrdinaryForcedLocal.exists_local hq hν hS
    A.field (A.divergence_free ha) F hF

end NSFormalization.Paper1.PeriodicOrdinaryLocal
