import NSFormalization.Section4.A01.LocalTheoryBundle
import NSFormalization.Section4.A04.ZeroSolution

open NSFormalization.Section4
open NSFormalization.Section4.A01

#print axioms NSFormalization.Section4.A01.LocalCarrier
#print axioms NSFormalization.Section4.A01.localCarrier_of_base
#print axioms NSFormalization.Section4.A01.LocalCarrier.regularity
#print axioms NSFormalization.Section4.A01.uniformBudgetSet
#print axioms NSFormalization.Section4.A01.uniformBudget
#print axioms NSFormalization.Section4.A01.uniformBudgetSet_nonempty
#print axioms NSFormalization.Section4.A01.uniformBudgetSet_bddAbove
#print axioms NSFormalization.Section4.A01.uniformBudget_pos
#print axioms NSFormalization.Section4.A01.uniformBudget_spec
#print axioms NSFormalization.Section4.A01.uniformBudget_antitone
#print axioms NSFormalization.Section4.A01.referenceCoefficients
#print axioms NSFormalization.Section4.A01.uniformBallBound
#print axioms NSFormalization.Section4.A01.uniformLipschitz
#print axioms NSFormalization.Section4.A01.uniformHorizon
#print axioms NSFormalization.Section4.A01.uniformHorizon_pos
#print axioms NSFormalization.Section4.A01.uniformHorizon_antitone
#print axioms NSFormalization.Section4.A01.uniformHorizon_spec
#print axioms NSFormalization.Section4.A01.uniformHorizon_mild
#print axioms NSFormalization.Section4.A01.selectedDatum
#print axioms NSFormalization.Section4.A01.selectedDatum_spec
#print axioms NSFormalization.Section4.A01.referenceForce
#print axioms NSFormalization.Section4.A01.referenceForce_bound
#print axioms NSFormalization.Section4.A01.localHorizon'
#print axioms NSFormalization.Section4.A01.localHorizon'_eq
#print axioms NSFormalization.Section4.A01.localCarrier_nonempty
#print axioms NSFormalization.Section4.A01.localCarrier
#print axioms NSFormalization.Section4.A01.manuscriptLocalRegularity_localCarrier
#print axioms NSFormalization.Section4.A01.datumRadiusConstant
#print axioms NSFormalization.Section4.A01.datumRadiusConstant_nonneg
#print axioms NSFormalization.Section4.A01.cylinderDatum_norm_le
#print axioms NSFormalization.Section4.A01.horizon_lower_bound_H7_fixedForce
#print axioms NSFormalization.Section4.A01.ManuscriptHorizonLowerBoundH1
#print axioms NSFormalization.Section4.A01.LocalTheoryDataShape
#print axioms NSFormalization.Section4.A01.localTheoryData

-- Actual data inhabit the bundle; regularity belongs to the selected solution.
example : ManuscriptLocalRegularity 1 0 0 (localHorizon' 1 0 0)
    (localCarrier 1 0 0 (by norm_num) A04.zero_mem_initialClassR A04.memForceR_zero).w :=
  manuscriptLocalRegularity_localCarrier 1 0 0 (by norm_num)
    A04.zero_mem_initialClassR A04.memForceR_zero

example (ν R R' B B' : ℝ) (hR : R ≤ R') (hB : B ≤ B') :
    uniformHorizon ν R' B' ≤ uniformHorizon ν R B :=
  uniformHorizon_antitone ν hR hB
