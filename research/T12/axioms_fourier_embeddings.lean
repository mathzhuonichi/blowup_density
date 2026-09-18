import NSFormalization.Section3.T12.FourierEmbeddings

/-!
# Transitive-axiom conformance for `Section3/T12/FourierEmbeddings.lean` (lane 341)

Every declaration of the module is audited.  Each line must report exactly
`[propext, Classical.choice, Quot.sound]`.
-/

open NSFormalization.Section3.T12

-- §0 weights
#print axioms fourierWeight_pos
#print axioms fourierWeight_eq_one_add_angular
#print axioms one_le_fourierWeight
#print axioms fourierWeight_neg
#print axioms angularFrequencySq_neg
#print axioms four_pi_sq_le_angularFrequencySq
#print axioms angularFrequencySq_pos
#print axioms sqrt_angularFrequencySq_le_weight
#print axioms reweightDatum_enorm_le'

-- §1 registered Laplacian spelling
#print axioms contDiff_laplacian
#print axioms isPeriodicSpatial_laplacian

-- §2 hTwo_le_laplacian
#print axioms hTwoConst
#print axioms hTwoConst_pos
#print axioms laplacianToWeight
#print axioms laplacianToWeight_abs_le
#print axioms laplacianToWeight_neg
#print axioms hTwo_le_laplacian

-- §3 lambda_exists
#print axioms lambdaCoeff
#print axioms lambdaField
#print axioms lambdaCoeff_neg
#print axioms summable_lambdaCoeff_weighted
#print axioms summable_lambdaCoeff
#print axioms contDiff_lambdaSeries
#print axioms lambdaSeries_ofReal_re
#print axioms lambdaField_component
#print axioms lambda_exists

-- §4 boundedRepresentative
#print axioms linftyConst
#print axioms one_le_inverseWeightSum
#print axioms linftyConst_pos
#print axioms continuous_torusScalarSeries
#print axioms norm_torusScalarSeries_le
#print axioms ae_eq_torusScalarSeries
#print axioms boundedRepresentative
