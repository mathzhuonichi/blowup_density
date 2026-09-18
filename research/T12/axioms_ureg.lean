import Tests.MeanZeroCalculus

/-!
# T12 registration axiom audit (lane 427)

Every declaration of `Contracts/V1/MeanZeroCalculus.lean`,
`Bindings/MeanZeroCalculus.lean` and `Tests/MeanZeroCalculus.lean`, plus the
shared helper `Section3/T12/DirDeriv.lean` created by this lane's dedupe, must
print exactly `[propext, Classical.choice, Quot.sound]`.

Run from `verification/`:
`lake env lean ../research/T12/axioms_ureg.lean`.
-/

/-! ## The eleven `rfl` drift guards -/

#print axioms BlowupDensity.Bindings.meanZero_isPeriodicScalarDatum_eq
#print axioms BlowupDensity.Bindings.meanZero_periodicScalarSobolevENorm_eq
#print axioms BlowupDensity.Bindings.meanZero_memPeriodicHmScalar_eq
#print axioms BlowupDensity.Bindings.meanZero_memPeriodicHmVector_eq
#print axioms BlowupDensity.Bindings.meanZero_memPeriodicHomogeneous_eq
#print axioms BlowupDensity.Bindings.meanZero_smoothPeriodicT_eq
#print axioms BlowupDensity.Bindings.meanZero_periodicLpENorm_eq
#print axioms BlowupDensity.Bindings.meanZero_lift_eq
#print axioms BlowupDensity.Bindings.meanZero_gradientTensor_eq
#print axioms BlowupDensity.Bindings.meanZero_laplacian_eq
#print axioms BlowupDensity.Bindings.meanZero_isPeriodicLambda_eq

/-! ## The transported record, the statement and the registered test -/

#print axioms BlowupDensity.Bindings.meanZeroCalculus
#print axioms BlowupDensity.Bindings.meanZeroCalculusStatement_holds
#print axioms BlowupDensity.Tests.checkedMeanZeroCalculus

/-! ## The non-vacuity witness of the acceptance test -/

#print axioms BlowupDensity.Tests.meanZeroProbeMode
#print axioms BlowupDensity.Tests.meanZeroProbeMode_contDiff
#print axioms BlowupDensity.Tests.meanZeroProbe_coordinateVector_apply
#print axioms BlowupDensity.Tests.meanZeroProbeMode_periodic
#print axioms BlowupDensity.Tests.meanZeroProbe
#print axioms BlowupDensity.Tests.meanZeroProbe_smoothPeriodic
#print axioms BlowupDensity.Tests.meanZeroProbe_meanZero
#print axioms BlowupDensity.Tests.meanZeroProbe_ne_zero
#print axioms BlowupDensity.Tests.meanZeroProbe_memHomogeneous

/-! ## The shared helper created by this lane's dedupe -/

#print axioms NSFormalization.Section3.T12.contDiff_dirDeriv
