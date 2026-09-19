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
