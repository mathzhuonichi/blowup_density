# D01 paper-to-Lean table

Lane 009, 2026-09-13.  Canonical definitions:
`verification/Contracts/V1/Data.lean`, namespace
`BlowupDensity.Contracts.V1.Data`.  Full reconciliation record:
[`RECONCILIATION.md`](RECONCILIATION.md); reviewer notes:
[`REVIEW_RECONCILIATION.md`](REVIEW_RECONCILIATION.md).

| Paper object | Location | `Data.lean` declaration |
|---|---|---|
| real 3-vector spatial field | `01-intro:91` eq:NS | `SpatialField` |
| spacetime vector field (velocity, force) | `01-intro:91` eq:NS | `SpaceTimeField` |
| scalar pressure | `01-intro:91` eq:NS | `SpaceTimeScalar` |
| one-sided time domain `[0,∞)` | `02-prelim:22` | `futureTimes` |
| force time interval `(0,∞)` | `01-intro:140` | `forceTimeMeasure` |
| forces are defined on `[0,∞)` only | `02-prelim:24` | `AgreesOnFuture` |
| order-`s` datum of a field, `H^s(R³)` | `01-intro:94` | `IsSobolevDatum`, `IsSobolevPath` |
| `‖z‖_{H^s(R³)}` | `01-intro:94,103` | `sobolevENorm` |
| `L^q(0,∞;H^s)` Bochner norm / membership | `01-intro:118-129` eq:time-norms | `bochnerDatumENorm`, `MemBochnerDatum` |
| `‖f‖_{L^q_tH^s_x}`, `L^1_tH^s_x`, `L^2_tH^s_x` | `01-intro:125,132` | `forceSobolevENorm`, `forceSobolevENormL1`, `forceSobolevENormL2` |
| `‖f‖_{L^q_tL^p_x}`, `L^∞_tL^p_x` | `01-intro:134` | `IsLebesgueSlicePath`, `mixedLebesgueENorm` |
| `s_q = 2/q − 3/2` | `04:8` thm:Rmain | `criticalOrder` |
| `β(q,s) = 2/q − 3/2 − s` | `04:57` | `scalingExponent` |
| a physical slice read as a tempered vector distribution | `01-intro:99` | `IsSliceDistribution` |
| `Ḣ^s(R³)`, `−3/2 < s < 3/2` | `02-prelim:58-69` eq:homogeneous-realization, `app-B:56-70` | `IsHomogeneousDatum`, `MemHomogeneous`, `homogeneousENorm` |
| `Ḣ^{-1}(R³)` | `02-prelim:59` | `MemDotHNegOne` |
| vector `Ḣ^s` and its norm | `02-prelim:72`, `01-intro:103` | `VectorDistribution`, `MemHomogeneousVector`, `homogeneousVectorENorm`, `IsHomogeneousVectorDatum` |
| homogeneous datum of a slice, and along a trajectory | `04:219,226` prop:Renergy | `IsHomogeneousSliceDatum`, `IsHomogeneousPath` |
| `‖f‖_{L^q_tḢ^s_x}`, in particular `L²_tḢ^{-1}_x` | `04:212,219,226` prop:Renergy | `forceHomogeneousENorm` |
| `‖z‖_{Ḣ^s}` as a quantity on smooth fields | `01-intro:105`, `04:70-72` | `homogeneousFourierENorm` |
| `‖z‖_{Ḣ^{3/2}}`, `‖a‖_{Ḣ^{1/2}}` | `app-B:31,107`, `04:85,91` | `dotHThreeHalvesENorm`, `dotHHalfENorm` |
| `‖z‖_{E_T}` | `01-intro:143` eq:Enorm | `energyENorm` (`energyEssSup`, `spatialGradient`, `energyGradient`) |
| `H^∞(R³;R³)` | `02-prelim:12,15` | `MemHInfty` |
| `L^2_σ(R³)` | `02-prelim:6` | `IsSolenoidal` |
| `X_R = H^∞ ∩ L²_σ` | `02-prelim:12` eq:Rinitial | `initialClassR` |
| `S_σ = 𝓢(R³;R³) ∩ L²_σ` | `04:192` | `initialClassSchwartz` |
| `F_R` | `02-prelim:17` eq:Rclasses | `MemForceR`, `forceClassR` |
| `F_c = C_c^∞(R³×(0,∞);R³)` | `04:185` | `MemForceCompact`, `forceClassCompact` |
| `F_rd` | `04:186-191` | `MemForceRapid`, `forceClassRapid` |
| `p ∼ p + κ(t)`; spatially constant gauge | `02-prelim:31`, `04:320` | `PressureGaugeEquivOn` |
| `p(x,t) = ∫₀¹G(rx,t)·x dr` | `02-prelim:97` | `pressurePotential` |
| classical solution on `[0,T)`, `∇p ∈ L²`, no `p ∈ L²` | `02-prelim` §2.1/§2.3, prop:local | `ClassicalSolutionR` |
| `T^ν_{max,R}(a,f)` | `02-prelim:32` | `maximalLifespanR` |
| regular through `T` | `02-prelim:34` | `RegularThrough` |
| `{f ∈ Y : T^ν_{max,R}(a,f) ≤ T}` for `Y ∈ {F_R, F_c, F_rd}` | `02-prelim:42` eq:Rsingularforces, `04:195,219` | `breakdownSetIn` |
| `B^R_{ν,a,T}`, `B^{R,0}_{ν,T}` | `02-prelim:42` | `breakdownSetR`, `breakdownSetRZero` |
| relative `L^q(0,∞;H^s)` density on a smooth class | `01-intro:137`, `04:8` | `RelativelyDense`, `BreakdownDenseR` |
| density in a completed Bochner space, either realization | `04:219` prop:Renergy | `CompletedDenseVia` |
| density in `L^q(0,∞;H^s(R³))` | `04:219` prop:Renergy, first clause | `CompletedDense` |
| density in `L²(0,∞;Ḣ^{-1}(R³))` | `04:219` prop:Renergy, second clause | `CompletedDenseHomogeneous` |
| complete uniform Cartesian grid | `04:288` | `Grid` (per-axis widths, arbitrary offset, half-open cells) |
| `(A_h z)_C` = cell average `∫_C z` over the cell volume | `04:290-291` | `cellAverage`, `gridObservation` |
