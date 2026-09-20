import NSFormalization.Section4.A01.DatumPathContinuous

noncomputable section
namespace Rev161Mutation

open Set MeasureTheory
open NSFormalization.Section4.A01 NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Substantive mutation: widen the proved top-order range from `q + 1` to `q + 2`.
example {q : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (m : ℕ) (hm : m ≤ q + 2) :
    ∃ A : Icc (0 : ℝ) S → RealVectorSobolev (m : ℝ),
      (∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (A t)) ∧ Continuous A := by
  exact exists_continuous_datumPath u U hu hU m hm

end Rev161Mutation
