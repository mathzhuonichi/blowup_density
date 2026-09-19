# Lane 481 attempts

Initial audit: the full raw I02 adapter is `T23/WholeSpaceCorrection.lean`.
The registered constructors are in `verification/Bindings/Correction.lean`,
`CorrectionV2.lean`, and `Scaling.lean`, not Section4/I02 or I03.
`grep -rnE 'structure (CorrectionAPI|ScalingAPI|WholeSpaceCorrectionAPI)|def (correction|scaling) .*CorrectionAPI|WholeSpaceCorrectionAPI' formalization/NSFormalization --include='*.lean'`
finds the T15/T17 torus records and the T23 raw correction adapter.
No competing record is introduced. Constructor consumption will be checked in
research, where importing Bindings is allowed; production proves local transport.

The first inspection used large batched output, which was truncated; subsequent
reads target the relevant individual declarations. No proof failure yet.
