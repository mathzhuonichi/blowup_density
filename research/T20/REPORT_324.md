# REPORT_324

## 1. The theorem
Reconciled T20 specification of `prop:critical` for zero initial datum, with small inhomogeneous critical force and global maximal lifespan.

## 2. Lean contents
`Spec.lean` contains the copied vocabulary, data-defined mean reduction, critical quantities, and one Type-valued `CriticalRegularityTAPI`. Fields are: `c`, `hc`, `C₀`, `hC₀`, `C₁`, `hC₁`, `CH1`, `hCH1`, `Ccriterion`, `hCcriterion`, `c_lt_C₀`, `c_lt_C₁`, `reductionRegular`, `meanBound`, `meanFreeEquation`, `constantTransportSkew`, `constantTransportCommutesLambda`, `criticalEnergy`, `bIntegral`, `yBound`, `hOneEnergy`, `continuationBound`, `globalRegularity`.

## 3. Gaps
The structure is statement-only; analytic bridge lemmas listed in the reconciliation remain to be proved by later lanes.

## 4. Verification
`cd verification && lake env lean ../research/T20/Spec.lean` elaborates with 0 errors. The file includes definitional `rfl` checks for registered spellings.
