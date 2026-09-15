import NSFormalization.Section4.A01.CommonHorizon

noncomputable section
namespace NSFormalization.Section4.A01

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open scoped Topology ContDiff NNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/- The `hall` binder copied token-for-token from
   `erenup/178-A01-b1-ladder-r3:DatumPathSmooth.lean:736-745`. -/
def Lane178Hall {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)) : Prop :=
  ∀ (q : ℕ) (hq : 6 ≤ q),
    ∃ (u₀ : SobolevSpace 1 (q + 1))
      (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
      (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
      ContDiffOn ℝ ∞ (extendPath S hS.le f) (Icc (0 : ℝ) S) ∧
      (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
      (∀ (θ : AddCircle (1 : ℝ)) t,
        sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
      ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq f) u₀ u t

-- Lane 186's output supplies exactly lane 178's `hall` interface.
example (huniq : MildUniqueness)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R : ℕ → ℝ) (hb : ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF (R q))
    (hfs : ∀ q (_hq : 6 ≤ q),
      ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S)) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧ Lane178Hall hν hS U := by
  simpa only [Lane178Hall] using
    compatible_carriers_hall huniq hν hS a ha F hF R hb hfs

-- The fixed-point premises of `MildUniqueness` are inhabited at canonical zero data.
example :
    ∃ (a : SobolevSpace 1 7)
      (f : C(Icc (0 : ℝ) 1, SobolevSpace 1 6))
      (u v : C(Icc (0 : ℝ) 1, SobolevSpace 1 7)),
      (∀ t, u t = quadraticDuhamel 1 1 (by norm_num) (by norm_num) le_rfl
        (coefficients 1 le_rfl f) a u t) ∧
      (∀ t, v t = quadraticDuhamel 1 1 (by norm_num) (by norm_num) le_rfl
        (coefficients 1 le_rfl f) a v t) := by
  refine ⟨0, 0, 0, 0, ?_, ?_⟩
  · intro t
    simp [quadraticDuhamel, source_eq]
  · intro t
    simp [quadraticDuhamel, source_eq]

-- In particular the named uniqueness input specializes without proof-instance mismatch.
example (huniq : MildUniqueness) :
    (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 7)) = 0 := by
  apply huniq 1 1 (by norm_num) (by norm_num) 0 0 0 0
  · intro t
    simp [quadraticDuhamel, source_eq]
  · intro t
    simp [quadraticDuhamel, source_eq]

end NSFormalization.Section4.A01
