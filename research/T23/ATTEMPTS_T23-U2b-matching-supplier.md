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

## Energy restriction: explicit function argument

`eLpNorm_mono_measure` takes the function before the measure inequality.
Exact diagnostics from the failed build:
```text
error: NSFormalization/Section3/T23/CorrectionEstimates.lean:18:6: Type mismatch
  eLpNorm_mono_measure ?m.39
has type
  ?m.30 ≤ ?m.29 → eLpNorm ?m.39 ?m.28 ?m.30 ≤ eLpNorm ?m.39 ?m.28 ?m.29
but is expected to have type
  (fun t => eLpNorm (fun x => w (t, x)) 2 (volume.restrict Ω)) x✝ ≤ (fun t => eLpNorm (fun x => w (t, x)) 2 volume) x✝
error: NSFormalization/Section3/T23/CorrectionEstimates.lean:18:27: Application type mismatch: The argument
  Measure.restrict_le_self
has type
  Measure.restrict ?m.36 ?m.37 ≤ ?m.36
of sort `Prop` but is expected to have type
  ?m.26 → ?m.31
of sort `Type (max ?u.12 ?u.13)` in the application
  eLpNorm_mono_measure Measure.restrict_le_self
error: NSFormalization/Section3/T23/CorrectionEstimates.lean:22:31: Application type mismatch: The argument
  eLpNorm_mono_measure ?m.87
has type
  ?m.78 ≤ ?m.77 → eLpNorm ?m.87 ?m.76 ?m.78 ≤ eLpNorm ?m.87 ?m.76 ?m.77
but is expected to have type
  eLpNorm (fun x => Section4.I02.spatialGradient w t x) 2 (volume.restrict Ω) ≤
    eLpNorm (fun x => Section4.I02.spatialGradient w t x) 2 volume
in the application
  ENNReal.rpow_le_rpow (eLpNorm_mono_measure ?m.87)
error: NSFormalization/Section3/T23/CorrectionEstimates.lean:22:53: Application type mismatch: The argument
  Measure.restrict_le_self
has type
  Measure.restrict ?m.84 ?m.85 ≤ ?m.84
of sort `Prop` but is expected to have type
  ?m.74 → ?m.79
of sort `Type (max ?u.27 ?u.28)` in the application
  eLpNorm_mono_measure Measure.restrict_le_self
Some required targets logged failures:
- NSFormalization.Section3.T23.CorrectionEstimates
error: build failed

```
Repair: `eLpNorm_mono_measure _ Measure.restrict_le_self`.

Inspection error: `rg: research/T23/probes/boundary_closes.lean: IO error for operation on research/T23/probes/boundary_closes.lean: No such file or directory (os error 2)`. Actual file: `boundary_api_on_canonical.lean`.
