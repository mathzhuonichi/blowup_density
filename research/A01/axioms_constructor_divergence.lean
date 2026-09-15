import NSFormalization.Section4.A01.ConstructorDivergence
import NSFormalization.Section4.A01.Horizon

noncomputable section
namespace Axioms163Divergence

open Set MeasureTheory
open NSFormalization.Section4.A01
open NSFormalization.Section4.A02 (SpaceTimeField)
open NavierStokes.ProblemStatement (Space spatialDivergence)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerLpTranslation EulerMeanSmoothRepresentative
open scoped ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

#print axioms ordinaryLift_eq_embedding
#print axioms ordinaryLift_gradient_mem
#print axioms solenoidal_of_ordinaryLift
#print axioms divergence_eq_zero_of_ordinaryLift
#print axioms solenoidal_path_of_cylinder
#print axioms spatialDivergence_eq_zero_of_cylinder

/-- The construction applies on the nonempty q=6 slab without assuming
ordinary solenoidality; the zero carrier's cylinder constraint supplies it. -/
theorem zero_cylinder_pointwise_divergence :
    ∀ (t : Icc (0 : ℝ) 1) x, spatialDivergence (0 : SpaceTimeField) t x = 0 :=
  spatialDivergence_eq_zero_of_cylinder (q := 6) (S := 1)
    (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 7))
    (0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2))
    (by intro t; simp [value])
    (by intro t; simp [value])
    (0 : SpaceTimeField)
    (by intro t; exact contDiff_const)
    (by
      intro t
      simp only [ContinuousMap.zero_apply]
      filter_upwards [Lp.coeFn_zero (E := Space) (p := 2) (μ := volume)] with x hx
      rw [hx]; rfl)

/-- Consume the actual local-theory theorem, retaining all its hypotheses.
Ordinary solenoidality and the initial ordinary datum are both conclusions. -/
theorem localTheory_solenoidal {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hb : HasAprioriBound hq hν a F hF R) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      ∀ t, U t ∈ EulerMeanSolenoidal.solenoidalSpace := by
  obtain ⟨u, U, _hbound, _huinit, hUinit, hU, hdiv, _hduhamel, _hang⟩ :=
    localTheory_on_prescribed_horizon hq hν hS hR a ha F hF hu₀ hb
  exact ⟨U, hUinit, solenoidal_path_of_cylinder u U hU hdiv⟩

#print axioms zero_cylinder_pointwise_divergence
#print axioms localTheory_solenoidal

end Axioms163Divergence
