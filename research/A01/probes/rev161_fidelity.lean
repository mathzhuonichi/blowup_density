import NSFormalization.Section4.A01.DatumPathContinuous

noncomputable section
namespace Rev161

open Set MeasureTheory
open NSFormalization.Section4.A01 NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement (Space coordinateVector)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity
open scoped LineDeriv SchwartzMap

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

example {q n : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 q)) (hn : n ≤ q) (w : Fin n → Fin 4) :
    Continuous (fun t => word 1 (u t) hn w) :=
  continuous_cylinder_word u hn w

example {q : ℕ} (u : SobolevSpace 1 q)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 q (0, θ) u = u) :
    ∀ (m n : ℕ) (hn : n ≤ q), n + m ≤ q → ∀ (w : Fin n → Fin 4)
      (Z : EulerMeanSolenoidal.L2), ordinaryLift Z = word 1 u hn w →
      HasWeakDerivsL2Bound (⇑Z) (‖u‖ ^ 2) m :=
  weakDerivsBound_word_top u hu

example {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (m : ℕ) (hm : m ≤ q + 1) : HasWeakDerivsL2Bound (⇑U) (‖u‖ ^ 2) m :=
  weakDerivsBound_cylinder_top u hu U hU m hm

example {q m : ℕ} (hm : m ≤ q + 1)
    (u v : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (hv : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) v = v)
    (U V : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (hV : ordinaryLift V = value 1 v)
    (A B : RealVectorSobolev (m : ℝ))
    (hA : IsSobolevDatum (m : ℝ) (⇑U) A) (hB : IsSobolevDatum (m : ℝ) (⇑V) B) :
    ‖A - B‖ ^ 2 ≤ (4 : ℝ) ^ m * ‖u - v‖ ^ 2 :=
  datum_sub_norm_sq_le hm u v hu hv U V hU hV A B hA hB

example {q : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (m : ℕ) (hm : m ≤ q + 1) :
    ∃ A : Icc (0 : ℝ) S → RealVectorSobolev (m : ℝ),
      (∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (A t)) ∧ Continuous A :=
  exists_continuous_datumPath u U hu hU m hm

-- The interval is genuinely inhabited, and the claimed top-order zero instance fires.
example : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0, by norm_num, by norm_num⟩⟩

example (q : ℕ) :
    ∃ A : Icc (0 : ℝ) 1 → RealVectorSobolev ((q + 1 : ℕ) : ℝ),
      (∀ t, IsSobolevDatum ((q + 1 : ℕ) : ℝ)
        (⇑((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) t)) (A t)) ∧ Continuous A := by
  exact exists_continuous_datumPath
    (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 (q + 1)))
    (0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2))
    (fun θ t => by simp) (fun t => by simp [value]) (q + 1) le_rfl

end Rev161
