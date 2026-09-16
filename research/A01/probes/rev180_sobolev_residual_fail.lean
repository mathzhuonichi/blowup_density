import NSFormalization.Section4.A01.ConstructorAssembly

noncomputable section
namespace Rev180SobolevResidual

open Set MeasureTheory EulerCylinderSobolevSpace EulerMeanOrdinaryLift
open NSFormalization.Section4.A01 NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)

example {q m : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t)) :
    ∃ A : Icc (0 : ℝ) S → RealVectorSobolev (m : ℝ),
      (∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (A t)) ∧ Continuous A := by
  exact exists_continuous_datumPath u U hu hU m (by omega)

end Rev180SobolevResidual
