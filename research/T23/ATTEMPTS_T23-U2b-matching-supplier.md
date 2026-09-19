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

## Registered probe: constant smoothness
```text
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:106:48: error: Invalid argument name `c` for function `ContDiff.contDiffOn`

Hint: Perhaps you meant one of the following parameter names:
  • `𝕜`: c̵𝕜̲
  • `E`: c̵E̲
  • `F`: c̵F̲
  • `s`: c̵s̲
  • `f`: c̵f̲
  • `n`: c̵n̲
  • `h`: c̵h̲
  • `x`: c̵x̲
```
Fixed by passing `c` to `contDiff_const` before `.contDiffOn`.

## Local energy: redundant simplification
```text
../formalization/NSFormalization/Section3/T23/CorrectionEstimates.lean:42:2: error: `dsimp` made no progress
```
Removed the redundant `dsimp only`; `refine` already reduced the let.

## Packet support interval
```text
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:162:48: error: Application type mismatch: The argument
  P.velocity_support
has type
  ∀ t ∈ Ico 0 1, (tsupport fun x => P.velocity (t, x)) ⊆ P.carrier
but is expected to have type
  ∀ t ∈ Ioo 0 1, (tsupport fun x => P.velocity (t, x)) ⊆ P.carrier
in the application
  @WholeSpaceCorrectionAPI.local_crossTransport ν P.velocity v P.carrier (correctionTo C) P.carrier_compact
    (ContDiffOn.mono hv (prod_mono Subset.rfl hball)) (fun t ht x hx => hdiv t ht x (hball hx)) P.velocity_support
```
Repair: restrict the registered Ico support assertion to Ioo using `⟨ht.1.le, ht.2⟩`.

Inspection error: `rg: verification/Contracts/V1/Threshold.lean: IO error for operation on verification/Contracts/V1/Threshold.lean: No such file or directory (os error 2)`. Actual file: `Thresholds.lean`.

## Supplier cutoff force: let-bound conjunction
```text
../formalization/NSFormalization/Section3/T23/MatchingSupplier.lean:105:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  correctionForce ?ν ?v ?D ?ε
in the target expression
  have D := localCorrectionData v C.x₀ C.T C.θ C.η C.plateau C.θRadius C.ε₀;
  D.correction ε = C.correction ε ∧ correctionForce ν v D ε = C.forceCorrection ε

ν : ℝ
u v : VelocityField
K : Set Space
C : WholeSpaceCorrectionAPI ν u K
heq : EqOn v C.v (Ioo 0 (C.T + C.δ) ×ˢ ball C.x₀ C.r)
ε : ℝ
hε : ε ∈ Ioc 0 C.ε₀
h :
  have D := localCorrectionData v C.x₀ C.T C.θ C.η C.plateau C.θRadius C.ε₀;
  D.correction ε = C.correction ε ∧ correctionForce ν v D ε = C.forceCorrection ε
⊢ correctionForce ν v C.supplierCutoff ε = C.forceCorrection ε
```
Repair: destruct the conjunction before rewriting the force formula.

## Copied cutoff: dependent rewrite
```text
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:191:10: error: invalid `▸` notation, expected result type of cast is 
  D.ε₀ ≤ A.ε₀
however, the equality 
  hcut
of type 
  L.ε₀ = C.ε₀
does not contain the expected result type on either the left or the right hand side
```
Repair: expose the copied threshold with `change`, then rewrite by `hcut`.

## Extended literal probe: scope and omitted section hypotheses
```text
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1172:0: error: Unexpected name `T23U2bPriorChecks` after `end`: The current section is unnamed

Hint: Delete the name `T23U2bPriorChecks` to end the current unnamed scope; outer named scopes can then be closed using additional `end` command(s):
  end ̵T̵2̵3̵U̵2̵b̵P̵r̵i̵o̵r̵C̵h̵e̵c̵k̵s̵
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1260:29: error: Ambiguous term
  VelocityField
Possible interpretations:
  BlowupDensity.Contracts.V1.VelocityField : Type
  
  ProblemStatement.VelocityField : Type
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1260:50: error: Ambiguous term
  Space
Possible interpretations:
  BlowupDensity.Contracts.V1.Space : Type
  
  ProblemStatement.Space : Type
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1285:58: error: Ambiguous term
  Space
Possible interpretations:
  BlowupDensity.Contracts.V1.Space : Type
  
  ProblemStatement.Space : Type
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1342:29: error: Ambiguous term
  VelocityField
Possible interpretations:
  BlowupDensity.Contracts.V1.VelocityField : Type
  
  ProblemStatement.VelocityField : Type
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1342:50: error: Ambiguous term
  Space
Possible interpretations:
  BlowupDensity.Contracts.V1.Space : Type
  
  ProblemStatement.Space : Type
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1370:33: error: Ambiguous term
  Space
Possible interpretations:
  BlowupDensity.Contracts.V1.Space : Type
  
  ProblemStatement.Space : Type
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1370:69: error: Ambiguous term
  VelocityField
Possible interpretations:
  BlowupDensity.Contracts.V1.VelocityField : Type
  
  ProblemStatement.VelocityField : Type
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1371:63: error: Ambiguous term
  Space
Possible interpretations:
  BlowupDensity.Contracts.V1.Space : Type
  
  ProblemStatement.Space : Type
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1379:33: error: unsolved goals
ν T δ r : ℝ
P : PacketAPI ν
th : ThresholdAPI
Ω : Set sorry
a : Data.SpatialField
g : sorry
reference : ClassicalSolutionOmega ν sorry a sorry (T + δ)
x₀ : sorry
hT : 0 < T
hδ : 0 < δ
hr : 0 < r
hball : sorry ⊆ Ω
⊢ ∃ C A D,
    A.correction = C ∧
      C.T = T ∧
        C.δ = δ ∧
          sorry ∧
            0 < D.ε₀ ∧
              D.ε₀ ≤ A.ε₀ ∧
                ∀ ε ∈ Ioc 0 D.ε₀,
                  D.correction ε = C.correction ε ∧ correctionForce ν reference.velocity D ε = C.forceCorrection ε
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1406:32: error(lean.unknownIdentifier): Unknown identifier `hK`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1406:35: error(lean.unknownIdentifier): Unknown identifier `hv`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1406:38: error(lean.unknownIdentifier): Unknown identifier `hd`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1406:41: error(lean.unknownIdentifier): Unknown identifier `hu`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1406:44: error(lean.unknownIdentifier): Unknown identifier `he`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1414:32: error(lean.unknownIdentifier): Unknown identifier `hK`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1414:35: error(lean.unknownIdentifier): Unknown identifier `hv`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1414:38: error(lean.unknownIdentifier): Unknown identifier `hd`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1414:41: error(lean.unknownIdentifier): Unknown identifier `hu`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1414:44: error(lean.unknownIdentifier): Unknown identifier `he`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1423:46: error(lean.unknownIdentifier): Unknown identifier `hK`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1423:49: error(lean.unknownIdentifier): Unknown identifier `hv`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1423:52: error(lean.unknownIdentifier): Unknown identifier `hd`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1423:55: error(lean.unknownIdentifier): Unknown identifier `hu`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1423:58: error(lean.unknownIdentifier): Unknown identifier `he`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1430:46: error(lean.unknownIdentifier): Unknown identifier `hK`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1430:49: error(lean.unknownIdentifier): Unknown identifier `hv`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1430:52: error(lean.unknownIdentifier): Unknown identifier `hd`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1430:55: error(lean.unknownIdentifier): Unknown identifier `hu`
../research/T23/probes/T23-U2b-matching-supplier_closes.lean:1430:58: error(lean.unknownIdentifier): Unknown identifier `he`
```
Repair: close the old probe’s anonymous noncomputable section before its wrapper namespace; explicitly include proof-side section hypotheses in the four field consumers.

## Final whitespace check
`git diff --check` initially reported:
```text
research/T23/probes/T23-U2b-matching-supplier_closes.lean:1467: new blank line at EOF.
```
Removed the trailing blank line; no proof changed.

## Final outcome

All recorded failures are repaired. The registered constructor retains
`A.correction = C` and has `A.ε₀ = C.ε₀` for this actual I02 V2 witness.
Both the localCorrectionData variant and the literal supplier-cutoff variant
carry the same three norm estimates and two cross transports. The guarded
19-declaration audits and final elaborations succeed. Record construction is
in the contract-facing probe, with canonical analytic/transport results in
the two production modules; no competing ScalingAPI was manufactured.
