# Lane 482 attempts

Initial checkpoint: read canonical U3 contract; dependency closure build running.
No completion claim is attached to this skeleton.

## P1: integral subtraction matching

```text
../formalization/NSFormalization/Section3/T23/PressureNormalization.lean:34:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∫ (a : Space) in Ω, p (t, a) - ?m.74
in the target expression
  ∫ (x : Space) in Ω, p (t, x) - domainPressureMean Ω p (t, x).1 = 0

Ω : Set Space
ho : IsOpen Ω
hb : Bornology.IsBounded Ω
hne : Ω.Nonempty
p : SpaceTimeScalar
t : ℝ
hp : IntegrableOn (fun x => p (t, x)) Ω volume
this : IsFiniteMeasure (volume.restrict Ω)
⊢ ∫ (x : Space) in Ω, p (t, x) - domainPressureMean Ω p (t, x).1 = 0
```
Resolution: reduce the pair projection before rewriting the integral.

## P2: real measure notation
```text
../formalization/NSFormalization/Section3/T23/PressureNormalization.lean:30:58: error: unsolved goals
Ω : Set Space
ho : IsOpen Ω
hb : Bornology.IsBounded Ω
hne : Ω.Nonempty
p : SpaceTimeScalar
t : ℝ
hp : IntegrableOn (fun x => p (t, x)) Ω volume
this : IsFiniteMeasure (volume.restrict Ω)
hv : (volume Ω).toReal ≠ 0
⊢ (∫ (a : Space) in Ω, p (t, a)) * ((volume Ω).toReal - (volume.restrict Ω).real univ) = (volume Ω).toReal * 0
../formalization/NSFormalization/Section3/T23/PressureNormalization.lean:33:38: warning: This simp argument is unused:
  Prod.fst

Hint: Omit it from the simp argument list.
  [apply] simp only [domainNormalizePressure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T23/PressureNormalization.lean:35:13: warning: This simp argument is unused:
  Measure.restrict_apply_univ

Hint: Omit it from the simp argument list.
  [apply] simp only [smul_eq_mul, domainPressureMean]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```
Resolution: unfold Measure.real before reducing restriction volume.

## P3: final ring normalization
```text
../formalization/NSFormalization/Section3/T23/PressureNormalization.lean:30:58: error: unsolved goals
Ω : Set Space
ho : IsOpen Ω
hb : Bornology.IsBounded Ω
hne : Ω.Nonempty
p : SpaceTimeScalar
t : ℝ
hp : IntegrableOn (fun x => p (t, x)) Ω volume
this : IsFiniteMeasure (volume.restrict Ω)
hv : (volume Ω).toReal ≠ 0
⊢ (∫ (a : Space) in Ω, p (t, a)) * (1 - 1) = 0
```
Resolution: ring after field_simp. Checkpoint e57eefb7 preceded this final fix.

## P4: finite-order zero cast
```text
../formalization/NSFormalization/Section3/T23/PressureNormalization.lean:64:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  @ContDiffOn ?m.42 ?m.43 ?m.44 ?m.45 ?m.46 ?m.47 ?m.48 ?m.49 0 ?m.51 ?m.50
in the target expression
  @ContDiffOn ℝ DenselyNormedField.toNontriviallyNormedField ℝ Real.normedAddCommGroup
    RCLike.toInnerProductSpaceReal.toNormedSpace ℝ Real.normedAddCommGroup RCLike.toInnerProductSpaceReal.toNormedSpace
    (↑0) (fun t => ∫ (x : Space) in Ω, p (t, x)) I

case zero
Ω : Set Space
hb : Bornology.IsBounded Ω
hm : MeasurableSet Ω
I : Set ℝ
hI : IsOpen I
p : SpaceTimeScalar
hp : SmoothOnClosedSlab I Ω p
⊢ ContDiffOn ℝ (↑0) (fun t => ∫ (x : Space) in Ω, p (t, x)) I
```
Resolution: change the order to literal zero.

## T1: opaque start time and slice inference
```text
../formalization/NSFormalization/Section3/T23/Triple.lean:203:27: error: linarith failed to find a contradiction
Ω K : Set Space
u f : VelocityField
p : PressureField
place : DomainPlacementData u p f K
hf : ContDiff ℝ ∞ f
hs : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f
ε : ℝ
hε : ε ∈ Ioc 0 place.ε₀
a✝ : T15.scaledStartTime place.T ε < 0
⊢ False
failed
../formalization/NSFormalization/Section3/T23/Triple.lean:239:13: error: don't know how to synthesize implicit argument `f`
  @ContDiff.differentiable ℝ DenselyNormedField.toNontriviallyNormedField Space (PiLp.normedAddCommGroup 2 fun x => ℝ)
    (PiLp.normedSpace 2 ℝ fun x => ℝ) Space (PiLp.normedAddCommGroup 2 fun x => ℝ) (PiLp.normedSpace 2 ℝ fun x => ℝ)
    (D.correction ε ∘ fun x => (?m.201, id x)) ∞
    (ContDiff.comp (C.correction_smooth ε hε) (ContDiff.prodMk contDiff_const contDiff_id))
    (of_eq_true
      (Eq.trans (congrArg Not (Eq.trans WithTop.coe_eq_zero._simp_1 ENat.top_ne_zero._simp_1)) not_false_eq_true))
    x
context:
ν δ r : ℝ
Ω K : Set Space
a : SpatialField
g : SpaceTimeField
u f : VelocityField
p : PressureField
place : DomainPlacementData u p f K
D : CutoffData
reference : ClassicalSolutionOmega ν Ω a g (place.T + δ)
hδ : 0 < δ
C : LocalCorrectionCore reference.velocity u K place.x₀ r place.T δ D
ε : ℝ
hε : ε ∈ Ioc 0 D.ε₀
hU : ContDiffOn ℝ ∞ (scaledVelocity u place.x₀ place.T ε) (Iio place.T ×ˢ univ)
hdiv : ∀ t < place.T, ∀ (x : Space), spatialDivergence (scaledVelocity u place.x₀ place.T ε) t x = 0
t : ℝ
ht : t ∈ Ico 0 place.T
x : Space
hx : x ∈ Ω
htr : t ∈ Ico 0 (place.T + δ)
hv : DifferentiableAt ℝ (fun y => reference.velocity (t, y)) x
⊢ Space → Space
../formalization/NSFormalization/Section3/T23/Triple.lean:239:14: error: don't know how to synthesize implicit argument `f`
  @ContDiff.comp ℝ Space SpaceTime Space DenselyNormedField.toNontriviallyNormedField
    (PiLp.normedAddCommGroup 2 fun x => ℝ) (PiLp.normedSpace 2 ℝ fun x => ℝ) Prod.normedAddCommGroup Prod.normedSpace
    (PiLp.normedAddCommGroup 2 fun x => ℝ) (PiLp.normedSpace 2 ℝ fun x => ℝ) ∞ (D.correction ε)
    (fun x => (?m.201, id x)) (C.correction_smooth ε hε) (ContDiff.prodMk contDiff_const contDiff_id)
context:
ν δ r : ℝ
Ω K : Set Space
a : SpatialField
g : SpaceTimeField
u f : VelocityField
p : PressureField
place : DomainPlacementData u p f K
D : CutoffData
reference : ClassicalSolutionOmega ν Ω a g (place.T + δ)
hδ : 0 < δ
C : LocalCorrectionCore reference.velocity u K place.x₀ r place.T δ D
ε : ℝ
hε : ε ∈ Ioc 0 D.ε₀
hU : ContDiffOn ℝ ∞ (scaledVelocity u place.x₀ place.T ε) (Iio place.T ×ˢ univ)
hdiv : ∀ t < place.T, ∀ (x : Space), spatialDivergence (scaledVelocity u place.x₀ place.T ε) t x = 0
t : ℝ
ht : t ∈ Ico 0 place.T
x : Space
hx : x ∈ Ω
htr : t ∈ Ico 0 (place.T + δ)
hv : DifferentiableAt ℝ (fun y => reference.velocity (t, y)) x
⊢ Space → SpaceTime
../formalization/NSFormalization/Section3/T23/Triple.lean:239:47: error: don't know how to synthesize implicit argument `f`
  @ContDiff.prodMk ℝ Space ℝ Space DenselyNormedField.toNontriviallyNormedField (PiLp.normedAddCommGroup 2 fun x => ℝ)
    (PiLp.normedSpace 2 ℝ fun x => ℝ) Real.normedAddCommGroup RCLike.toInnerProductSpaceReal.toNormedSpace
    (PiLp.normedAddCommGroup 2 fun x => ℝ) (PiLp.normedSpace 2 ℝ fun x => ℝ) ∞ (fun x => ?m.201) id contDiff_const
    contDiff_id
context:
ν δ r : ℝ
Ω K : Set Space
a : SpatialField
g : SpaceTimeField
u f : VelocityField
p : PressureField
place : DomainPlacementData u p f K
D : CutoffData
reference : ClassicalSolutionOmega ν Ω a g (place.T + δ)
hδ : 0 < δ
C : LocalCorrectionCore reference.velocity u K place.x₀ r place.T δ D
ε : ℝ
hε : ε ∈ Ioc 0 D.ε₀
hU : ContDiffOn ℝ ∞ (scaledVelocity u place.x₀ place.T ε) (Iio place.T ×ˢ univ)
hdiv : ∀ t < place.T, ∀ (x : Space), spatialDivergence (scaledVelocity u place.x₀ place.T ε) t x = 0
t : ℝ
ht : t ∈ Ico 0 place.T
x : Space
hx : x ∈ Ω
htr : t ∈ Ico 0 (place.T + δ)
hv : DifferentiableAt ℝ (fun y => reference.velocity (t, y)) x
⊢ Space → ℝ
../formalization/NSFormalization/Section3/T23/Triple.lean:239:62: error: don't know how to synthesize placeholder
context:
ν δ r : ℝ
Ω K : Set Space
a : SpatialField
g : SpaceTimeField
u f : VelocityField
p : PressureField
place : DomainPlacementData u p f K
D : CutoffData
reference : ClassicalSolutionOmega ν Ω a g (place.T + δ)
hδ : 0 < δ
C : LocalCorrectionCore reference.velocity u K place.x₀ r place.T δ D
ε : ℝ
hε : ε ∈ Ioc 0 D.ε₀
hU : ContDiffOn ℝ ∞ (scaledVelocity u place.x₀ place.T ε) (Iio place.T ×ˢ univ)
hdiv : ∀ t < place.T, ∀ (x : Space), spatialDivergence (scaledVelocity u place.x₀ place.T ε) t x = 0
t : ℝ
ht : t ∈ Ico 0 place.T
x : Space
hx : x ∈ Ω
htr : t ∈ Ico 0 (place.T + δ)
hv : DifferentiableAt ℝ (fun y => reference.velocity (t, y)) x
⊢ ℝ
../formalization/NSFormalization/Section3/T23/Triple.lean:239:7: error: failed to infer `have` declaration type
../formalization/NSFormalization/Section3/T23/Triple.lean:236:64: error: unsolved goals
ν δ r : ℝ
Ω K : Set Space
a : SpatialField
g : SpaceTimeField
u f : VelocityField
p : PressureField
place : DomainPlacementData u p f K
D : CutoffData
reference : ClassicalSolutionOmega ν Ω a g (place.T + δ)
hδ : 0 < δ
C : LocalCorrectionCore reference.velocity u K place.x₀ r place.T δ D
ε : ℝ
hε : ε ∈ Ioc 0 D.ε₀
hU : ContDiffOn ℝ ∞ (scaledVelocity u place.x₀ place.T ε) (Iio place.T ×ˢ univ)
hdiv : ∀ t < place.T, ∀ (x : Space), spatialDivergence (scaledVelocity u place.x₀ place.T ε) t x = 0
t : ℝ
ht : t ∈ Ico 0 place.T
x : Space
hx : x ∈ Ω
htr : t ∈ Ico 0 (place.T + δ)
hv : DifferentiableAt ℝ (fun y => reference.velocity (t, y)) x
⊢ spatialDivergence (velocity place D reference ε) t x = 0
```
Resolution: expose scaledStartTime and give the constant slice time explicitly.

## T2: velocity unfolding
```text
../formalization/NSFormalization/Section3/T23/Triple.lean:242:6: error: Failed to rewrite using equation theorems for `velocity`
```
Resolution: change to the explicit function before derivative rewrites.

## S1: integral slice inference and placement field name
```text
../formalization/NSFormalization/Section3/T23/Solution.lean:27:2: error: Tactic `apply` failed: could not unify the type of `SmoothOnClosedSlab.integrableOn_slice hb ?m.89 ht`
  IntegrableOn (fun x => ?m.88 (t, x)) Ω volume
with the goal
  IntegrableOn (fun x => reference.pressure (t, x) + scaledPressure p place.x₀ place.T ε (t, x)) Ω volume

ν δ : ℝ
Ω K : Set Space
a : SpatialField
g : SpaceTimeField
u f : VelocityField
p : PressureField
place : DomainPlacementData u p f K
reference : ClassicalSolutionOmega ν Ω a g (place.T + δ)
hδ : 0 < δ
ho : IsOpen Ω
hb : Bornology.IsBounded Ω
hne : Ω.Nonempty
ε : ℝ
hP : ContDiffOn ℝ ∞ (scaledPressure p place.x₀ place.T ε) (Iio place.T ×ˢ univ)
t : ℝ
ht : t ∈ Ico 0 place.T
⊢ IntegrableOn (fun x => reference.pressure (t, x) + scaledPressure p place.x₀ place.T ε (t, x)) Ω volume
../formalization/NSFormalization/Section3/T23/Solution.lean:52:23: error(lean.invalidField): Invalid field `T_pos`: The environment does not contain `NSFormalization.Section3.T23.DomainPlacementData.T_pos`, so it is not possible to project the field `T_pos` from an expression
  place
of type `DomainPlacementData u p f K`
```
Resolution: explicit joint scalar field; canonical horizon field is time_pos.

## Q1: original-Spec consumer elaboration
```text
../research/T23/probes/T23-U3-triple-solution_closes.lean:1215:18: error: Function expected at
  correctionForce
but this term has type
  ?m.169

Note: Expected a function because this term is being applied to the argument
  ν

Hint: The identifier `correctionForce` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T23/probes/T23-U3-triple-solution_closes.lean:1221:28: error(lean.unknownIdentifier): Unknown identifier `«dc».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1222:28: error(lean.unknownIdentifier): Unknown identifier `«pl».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1219:58: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
../research/T23/probes/T23-U3-triple-solution_closes.lean:1229:28: error(lean.unknownIdentifier): Unknown identifier `«dc».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1230:28: error(lean.unknownIdentifier): Unknown identifier `«pl».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1227:77: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
../research/T23/probes/T23-U3-triple-solution_closes.lean:1237:28: error(lean.unknownIdentifier): Unknown identifier `«dc».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1238:28: error(lean.unknownIdentifier): Unknown identifier `«pl».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1240:32: error: Application type mismatch: The argument
  hU ε hs
has type
  ContDiffOn ℝ ∞ (scaledPacket P.velocity place.x₀ place.T ε) (Iio place.T ×ˢ univ)
but is expected to have type
  ContDiffOn ℝ ∞
    (NSFormalization.Section3.T15.scaledVelocity ?m.298 (NSFormalization.Section3.T23.DomainPlacementData.x₀ ?m.301)
      (NSFormalization.Section3.T23.DomainPlacementData.T ?m.301) ?m.305)
    (Iio (NSFormalization.Section3.T23.DomainPlacementData.T ?m.301) ×ˢ univ)
in the application
  velocity_smooth hδ ?m.304 ?m.306 (hU ε hs)
../research/T23/probes/T23-U3-triple-solution_closes.lean:1245:28: error(lean.unknownIdentifier): Unknown identifier `«dc».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1246:28: error(lean.unknownIdentifier): Unknown identifier `«pl».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1248:47: error: Application type mismatch: The argument
  hP ε hs
has type
  ContDiffOn ℝ ∞ (scaledPressure P.pressure place.x₀ place.T ε) (Iio place.T ×ˢ univ)
but is expected to have type
  ContDiffOn ℝ ∞
    (NSFormalization.Section3.T15.scaledPressure ?m.299 (NSFormalization.Section3.T23.DomainPlacementData.x₀ ?m.300)
      (NSFormalization.Section3.T23.DomainPlacementData.T ?m.300) ?m.307)
    (Iio (NSFormalization.Section3.T23.DomainPlacementData.T ?m.300) ×ˢ univ)
in the application
  pressure_smooth hδ hb (IsOpen.measurableSet ho) (hP ε hs)
../research/T23/probes/T23-U3-triple-solution_closes.lean:1253:28: error(lean.unknownIdentifier): Unknown identifier `«dc».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1254:28: error(lean.unknownIdentifier): Unknown identifier `«pl».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1261:28: error(lean.unknownIdentifier): Unknown identifier `«dc».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1262:28: error(lean.unknownIdentifier): Unknown identifier `«pl».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1264:48: error: Application type mismatch: The argument
  hU ε hs
has type
  ContDiffOn ℝ ∞ (scaledPacket P.velocity place.x₀ place.T ε) (Iio place.T ×ˢ univ)
but is expected to have type
  ContDiffOn ℝ ∞
    (NSFormalization.Section3.T15.scaledVelocity ?m.310 (NSFormalization.Section3.T23.DomainPlacementData.x₀ ?m.313)
      (NSFormalization.Section3.T23.DomainPlacementData.T ?m.313) ?m.317)
    (Iio (NSFormalization.Section3.T23.DomainPlacementData.T ?m.313) ×ˢ univ)
in the application
  incompressible hδ ?m.316 ?m.318 (hU ε hs)
../research/T23/probes/T23-U3-triple-solution_closes.lean:1269:28: error(lean.unknownIdentifier): Unknown identifier `«dc».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1270:28: error(lean.unknownIdentifier): Unknown identifier `«pl».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1272:42: error: Application type mismatch: The argument
  hU ε hs
has type
  ContDiffOn ℝ ∞ (scaledPacket P.velocity place.x₀ place.T ε) (Iio place.T ×ˢ univ)
but is expected to have type
  ContDiffOn ℝ ∞
    (NSFormalization.Section3.T15.scaledVelocity ?m.342 (NSFormalization.Section3.T23.DomainPlacementData.x₀ ?m.345)
      (NSFormalization.Section3.T23.DomainPlacementData.T ?m.345) ?m.349)
    (Iio (NSFormalization.Section3.T23.DomainPlacementData.T ?m.345) ×ˢ univ)
in the application
  momentum hδ ?m.348 ?m.350 (hU ε hs)
../research/T23/probes/T23-U3-triple-solution_closes.lean:1277:28: error(lean.unknownIdentifier): Unknown identifier `«dc».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1278:28: error(lean.unknownIdentifier): Unknown identifier `«pl».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1290:52: error: Application type mismatch: The argument
  hU
has type
  ∀ ε ∈ Ioc 0 s, ContDiffOn ℝ ∞ (scaledPacket P.velocity place.x₀ place.T ε) (Iio place.T ×ˢ univ)
but is expected to have type
  ∀ ε ∈ Ioc 0 s,
    ContDiffOn ℝ ∞
      (NSFormalization.Section3.T15.scaledVelocity ?m.332 (NSFormalization.Section3.T23.DomainPlacementData.x₀ ?m.335)
        (NSFormalization.Section3.T23.DomainPlacementData.T ?m.335) ε)
      (Iio (NSFormalization.Section3.T23.DomainPlacementData.T ?m.335) ×ˢ univ)
in the application
  solution hδ ho hb hne ?m.338 s b hU
../research/T23/probes/T23-U3-triple-solution_closes.lean:1296:28: error(lean.unknownIdentifier): Unknown identifier `«dc».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1297:28: error(lean.unknownIdentifier): Unknown identifier `«pl».ε₀`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1299:50: error: Application type mismatch: The argument
  hU ε hs
has type
  ContDiffOn ℝ ∞ (scaledPacket P.velocity place.x₀ place.T ε) (Iio place.T ×ˢ univ)
but is expected to have type
  ContDiffOn ℝ ∞
    (NSFormalization.Section3.T15.scaledVelocity ?m.361 (NSFormalization.Section3.T23.DomainPlacementData.x₀ ?m.364)
      (NSFormalization.Section3.T23.DomainPlacementData.T ?m.364) ?m.368)
    (Iio (NSFormalization.Section3.T23.DomainPlacementData.T ?m.364) ×ˢ univ)
in the application
  classicalSolution hδ ho hb hne ?m.367 ?m.369 ?m.370 ⋯
```
Resolution: qualify the Spec correction force, parenthesize notation before projection, and explicitly instantiate placement/reference. No heartbeat increase.

## Q2: copied correction namespace
```text
../research/T23/probes/T23-U3-triple-solution_closes.lean:1215:18: error(lean.unknownIdentifier): Unknown identifier `BlowupDensity.T17.Draft.correctionForce`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1286:0: warning: declaration uses `sorry`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1294:0: warning: declaration uses `sorry`
```
Resolution: T17.Spec, as read in the original source. The admission warnings came from failed elaboration; no admission token was added.

## Q3: unexplained consumer admission warnings
```text
../research/T23/probes/T23-U3-triple-solution_closes.lean:1286:0: warning: declaration uses `sorry`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1294:0: warning: declaration uses `sorry`
```
Investigating elaboration of the no-slip-dependent examples; production axiom audit is clean.

## T3: inverse-power normalization changed the field syntax
```text
../formalization/NSFormalization/Section3/T23/Triple.lean:141:2: error: Type mismatch: After simplification, term
  h
 has type
  ContDiffOn ℝ ∞
    (Source.dilateField ε⁻¹ (ε ^ 2)⁻¹ ε⁻¹ (place.T - ε ^ 2) place.x₀ (Source.PacketScaling.zeroPastField u))
    (Iio place.T ×ˢ univ)
but is expected to have type
  ContDiffOn ℝ ∞ (scaledVelocity u place.x₀ place.T ε) (Iio place.T ×ˢ univ)
../formalization/NSFormalization/Section3/T23/Triple.lean:151:2: error: Type mismatch: After simplification, term
  h
 has type
  ContDiffOn ℝ ∞
    (Source.dilateField (ε ^ 2)⁻¹ (ε ^ 2)⁻¹ ε⁻¹ (place.T - ε ^ 2) place.x₀ (Source.PacketScaling.zeroPastField p))
    (Iio place.T ×ˢ univ)
but is expected to have type
  ContDiffOn ℝ ∞ (scaledPressure p place.x₀ place.T ε) (Iio place.T ×ˢ univ)
```
Resolution: rewrite only the horizon equality, preserving the definitionally equal field expression.

## Q4: named consumer missing section proof variables
```text
../research/T23/probes/T23-U3-triple-solution_closes.lean:1290:66: error(lean.unknownIdentifier): Unknown identifier `hδ`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1290:69: error(lean.unknownIdentifier): Unknown identifier `ho`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1290:72: error(lean.unknownIdentifier): Unknown identifier `hb`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1290:75: error(lean.unknownIdentifier): Unknown identifier `hne`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1290:79: error(lean.unknownIdentifier): Unknown identifier `C`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1290:85: error(lean.unknownIdentifier): Unknown identifier `hU`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1290:88: error(lean.unknownIdentifier): Unknown identifier `hP`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1290:91: error(lean.unknownIdentifier): Unknown identifier `hdiv`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1290:96: error(lean.unknownIdentifier): Unknown identifier `heq`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1290:100: error(lean.unknownIdentifier): Unknown identifier `hnoSlip`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1294:4: warning: declaration uses `sorry`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1294:4: warning: declaration uses `sorry`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1294:4: warning: declaration uses `sorry`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1294:4: warning: declaration uses `sorry`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1294:4: warning: declaration uses `sorry`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1294:4: warning: declaration uses `sorry`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1294:4: warning: declaration uses `sorry`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1294:4: warning: declaration uses `sorry`
../research/T23/probes/T23-U3-triple-solution_closes.lean:1294:4: warning: declaration uses `sorry`
theorem TripleSolutionProbe.solution_exact : ∀ {ν : ℝ} {P : BlowupDensity.Contracts.V1.PacketImportAPI ν}
  {Ω : Set BlowupDensity.Contracts.V1.Space} {a : BlowupDensity.Contracts.V1.Data.SpatialField}
  {g : BlowupDensity.Contracts.V1.Data.SpaceTimeField} {δ s b : ℝ}
  (place : BlowupDensity.T23.Spec.DomainPlacementData P.toPacketAPI) (D : BlowupDensity.T16.Draft.CutoffData)
  (reference : BlowupDensity.T23.Spec.ClassicalSolutionOmega ν Ω a g (place.T + δ)),
  ∀
    ε ∈
      Ioc 0
        (NSFormalization.Section3.T23.InsertedTriple.threshold (TripleSolutionProbe.placeTo place)
          (TripleSolutionProbe.cutoffTo D) s b),
    ∃ w,
      w.velocity =
          NSFormalization.Section3.T23.InsertedTriple.velocity (TripleSolutionProbe.placeTo place)
            (TripleSolutionProbe.cutoffTo D) (TripleSolutionProbe.solutionTo reference) ε ∧
        w.pressure =
          NSFormalization.Section3.T23.InsertedTriple.pressure (TripleSolutionProbe.placeTo place)
            (TripleSolutionProbe.solutionTo reference) ε :=
sorry
'TripleSolutionProbe.solution_exact' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
Resolution under test: explicitly include supplier/no-slip hypotheses in the named consumers.
