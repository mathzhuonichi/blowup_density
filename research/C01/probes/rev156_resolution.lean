import Contracts.V3.EnergyAbsorptionPartial

/-! REVIEW PROBE (lane 156): which constants the two V3 fields actually mention.  Confirms the
vocabulary is inherited (`Contracts.V1…slice/l2Sq/l2Norm`, `Contracts.V2…gradientSq` = the
registered `gradientTensor` Frobenius form), not re-declared, and that `energyBudget` /
`forcePrimitive` are the V3 ones. -/

set_option pp.fullNames true

#check @BlowupDensity.Contracts.V3.EnergyAbsorptionPartial.EnergyAbsorptionPartialV3API.l2Bound
#check @BlowupDensity.Contracts.V3.EnergyAbsorptionPartial.EnergyAbsorptionPartialV3API.energyDifferentialBound
#print BlowupDensity.Contracts.V3.EnergyAbsorptionPartial.energyBudget
#print BlowupDensity.Contracts.V3.EnergyAbsorptionPartial.forcePrimitive
#print BlowupDensity.Contracts.V2.EnergyAbsorptionPartial.gradientSq
