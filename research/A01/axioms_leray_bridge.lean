import NSFormalization.Section4.A01.LerayBridge

open NSFormalization.Section4.A01 NSFormalization.Section4.D01
open NSFormalization.Paper3 MeasureTheory
open NavierStokes.ProblemStatement

#print axioms physicalResidual_datum_eq
#print axioms gradient_datum_fixed
#print axioms solenoidal_datum_zero
#print axioms solenoidal_datum_zero_of_cylinder
#print axioms gradient_datum_fixed_of_cylinder
#print axioms projected_datum_of_decomposition
#print axioms lowered_projected_datum_of_cylinder
#print axioms hprojected_of_cylinder
#print axioms cylinder_source_complement_value

example : (0 : RealVectorSobolev 0) = 0 - Leray.lerayComplement 0 0 := by
  exact projected_datum_of_decomposition 0 0 0 (by simp) (by simp) (by simp)

example : Leray.lerayComplement 0
    (orderZeroDatum (memLp_zero : MemLp (0 : Space → Space) 2 volume)) =
    orderZeroDatum (memLp_zero : MemLp (0 : Space → Space) 2 volume) := by
  apply gradient_datum_fixed memLp_zero contDiff_const
    (fun i j x => by simp [NSFormalization.Section4.A03.partialDeriv,
      spatialDerivative, NSFormalization.Section4.A03.lift])
  exact isSobolevDatum_orderZeroDatum memLp_zero

-- Zero carriers satisfy the actual cylinder Helmholtz hypotheses.
example : lowerVectorL (↑(0 : ℕ) : ℝ) 0 (Nat.cast_nonneg (0 : ℕ))
    (0 : RealVectorSobolev (↑(0 : ℕ) : ℝ)) =
    0 - Leray.lerayComplement 0 0 := by
  have hrep : (⇑(0 : EulerMeanSolenoidal.L2)) =ᵐ[volume] (0 : Space → Space) :=
    Lp.coeFn_zero Space 2 volume
  have hd : IsSobolevDatum 0 (⇑(0 : EulerMeanSolenoidal.L2)) 0 :=
    IsSobolevDatum.congr_field (isSobolevDatum_zero 0) hrep.symm
  have hdR : IsSobolevDatum (↑(0 : ℕ) : ℝ) (⇑(0 : EulerMeanSolenoidal.L2)) 0 :=
    IsSobolevDatum.congr_field (isSobolevDatum_zero _) hrep.symm
  exact lowered_projected_datum_of_cylinder (m := 0)
    (0 : EulerMeanSolenoidal.L2) 0
    (by simp) (by simp) (0 : Space → Space) 0 contDiff_const contDiff_const
    hrep hrep (0 : RealVectorSobolev (↑(0 : ℕ) : ℝ)) 0 hdR hd

#print axioms leray_value_solenoidal
#print axioms leray_value_complement_gradient
#print axioms laplacianEvaluation_solenoidal
#print axioms cylinderResidual_solenoidal
#print axioms residual_difference_gradient
#print axioms ordinaryLift_unprojectedResidual
#print axioms ordinaryResidual_helmholtz
#print axioms residualDatum_jointRepresentative
#print axioms physicalResidual_eq_residualDatum
#print axioms hprojected_of_canonical_pairs
#print axioms hprojected_of_cylinder''
#print axioms vectorRepresentative_sub
#print axioms vectorRepresentative_hasDerivAt
#print axioms jointRepresentative_temporalDerivative
#print axioms ae_eq_of_isSobolevDatum
#print axioms jointRepresentative_temporalDerivative_of_cylinder

#print axioms NSFormalization.Section4.A01.value_residual_linear
#print axioms NSFormalization.Section4.A01.unprojectedResidual_value
