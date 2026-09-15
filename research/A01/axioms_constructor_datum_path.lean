import NSFormalization.Section4.A01.ConstructorDatumPath

noncomputable section
namespace Axioms161DatumPath

open Set MeasureTheory
open NSFormalization.Section4.A01
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerLpTranslation

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

#print axioms hasWeakDerivsL2Bound_of_word_full
#print axioms hasWeakDerivsL2Bound_of_cylinder_full
#print axioms norm_datum_sub_sq_le_of_cylinder
#print axioms datum_path_continuous_of_cylinder
#print axioms exists_continuous_datum_path_of_cylinder
#print axioms exists_continuous_datum_slice_of_cylinder

/-- The top-order output is an actual continuous datum path on a nonempty interval. -/
theorem nonvacuous_top_order_path :
    ∃ A : C(Icc (0 : ℝ) 1, RealVectorSobolev ((7 : ℕ) : ℝ)),
      ∀ t : Icc (0 : ℝ) 1, NSFormalization.Section4.A02.IsSobolevDatum ((7 : ℕ) : ℝ)
        (fun x : Space => (0 : SpaceTimeField) (↑t, x)) (A t) :=
  exists_continuous_datum_slice_of_cylinder (q := 6) (S := 1)
    (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 7))
    (0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2))
    (by intro θ t; simp)
    (by intro t; simp [value])
    (0 : SpaceTimeField)
    (by
      intro t
      simp only [ContinuousMap.zero_apply]
      filter_upwards [Lp.coeFn_zero (E := Space) (p := 2) (μ := volume)] with x hx
      rw [hx]; rfl)
    (m := 7) (by norm_num)

#print axioms nonvacuous_top_order_path

end Axioms161DatumPath
