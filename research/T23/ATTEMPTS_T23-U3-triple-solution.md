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
