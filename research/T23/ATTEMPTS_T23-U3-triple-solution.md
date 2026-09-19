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
