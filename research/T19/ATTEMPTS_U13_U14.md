# U13/U14 attempts

## Attempt 1 — energy helpers
Incorrect namespace for `spatialDerivative`; unrestricted `congr 1` expanded the
integral goal too far. Use its A02 namespace and explicit congruence instead.

```text
../formalization/NSFormalization/Section3/T19/Closure.lean:8:51: error(lean.unknownIdentifier): Unknown constant `NSFormalization.Section4.I02.spatialDerivative`
../formalization/NSFormalization/Section3/T19/Closure.lean:24:4: error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
../formalization/NSFormalization/Section3/T19/Closure.lean:48:32: error(lean.unknownIdentifier): Unknown identifier `spatialGradient`
../formalization/NSFormalization/Section3/T19/Closure.lean:49:19: error(lean.unknownIdentifier): Unknown identifier `spatialGradient`
../formalization/NSFormalization/Section3/T19/Closure.lean:48:4: error: stuck at solving universe constraint
  ?u.24 + 1 =?= imax ?u.22 ?u.23
while trying to unify
  (x : ?m.31 t) → ?m.32 t x : Sort (imax ?u.22 ?u.23)
with
  (x : ?m.31 t) → ?m.32 t x : Sort (imax ?u.22 ?u.23)
../formalization/NSFormalization/Section3/T19/Closure.lean:56:2: error: stuck at solving universe constraint
  ?u.24 + 1 =?= imax ?u.22 ?u.23
while trying to unify
  (x : ?m.31 t) → ?m.32 t x : Sort (imax ?u.22 ?u.23)
with
  (x : ?m.31 t) → ?m.32 t x : Sort (imax ?u.22 ?u.23)
../formalization/NSFormalization/Section3/T19/Closure.lean:46:42: error: stuck at solving universe constraint
  ?u.24 + 1 =?= imax ?u.22 ?u.23
while trying to unify
  (x : ?m.31 t) → ?m.32 t x : Sort (imax ?u.22 ?u.23)
with
  (x : ?m.31 t) → ?m.32 t x : Sort (imax ?u.22 ?u.23)

```

## Attempt 2 — namespace correction

`spatialDerivative` is in `NavierStokes.ProblemStatement`, already open.

```text
../formalization/NSFormalization/Section3/T19/Closure.lean:7:63: error(lean.unknownIdentifier): Unknown constant `NSFormalization.Section4.A02.spatialDerivative`
../formalization/NSFormalization/Section3/T19/Closure.lean:15:19: error: Application type mismatch: The argument
  u
has type
  SpaceTimeField
but is expected to have type
  Section4.A02.SpaceTimeField
in the application
  energyENormT T u
../formalization/NSFormalization/Section3/T19/Closure.lean:15:38: error: Application type mismatch: The argument
  v
has type
  SpaceTimeField
but is expected to have type
  Section4.A02.SpaceTimeField
in the application
  energyENormT T v
../formalization/NSFormalization/Section3/T19/Closure.lean:14:16: error: Application type mismatch: The argument
  v
has type
  SpaceTimeField
but is expected to have type
  ℝ × ?m.12 → ?m.3
in the application
  EqOn ?m.5 v
../formalization/NSFormalization/Section3/T19/Closure.lean:32:54: error: Application type mismatch: The argument
  u
has type
  SpaceTimeField
but is expected to have type
  Section4.A02.SpaceTimeField
in the application
  T15.EnergySlicesMemLpT T u
../formalization/NSFormalization/Section3/T19/Closure.lean:31:25: error: Application type mismatch: The argument
  u
has type
  SpaceTimeField
but is expected to have type
  ℝ × ?m.17 → ?m.6
in the application
  ContDiffOn ℝ ∞ u
../formalization/NSFormalization/Section3/T19/Closure.lean:45:29: error: Function expected at
  u
but this term has type
  SpaceTimeField

Note: Expected a function because this term is being applied to the argument
  z
../formalization/NSFormalization/Section3/T19/Closure.lean:45:35: error: Function expected at
  v
but this term has type
  SpaceTimeField

Note: Expected a function because this term is being applied to the argument
  z
../formalization/NSFormalization/Section3/T19/Closure.lean:46:31: error: Function expected at
  v
but this term has type
  SpaceTimeField

Note: Expected a function because this term is being applied to the argument
  z
../formalization/NSFormalization/Section3/T19/Closure.lean:46:37: error: Function expected at
  u
but this term has type
  SpaceTimeField

Note: Expected a function because this term is being applied to the argument
  z
../formalization/NSFormalization/Section3/T19/Closure.lean:47:59: error: Function expected at
  w
but this term has type
  SpaceTimeField

Note: Expected a function because this term is being applied to the argument
  z
../formalization/NSFormalization/Section3/T19/Closure.lean:47:81: error: Application type mismatch: The argument
  w
has type
  SpaceTimeField
of sort `Sort u_1` but is expected to have type
  Section4.A02.SpaceTimeField
of sort `Type` in the application
  energyENormT T w
../formalization/NSFormalization/Section3/T19/Closure.lean:48:59: error: Function expected at
  w
but this term has type
  SpaceTimeField

Note: Expected a function because this term is being applied to the argument
  z
../formalization/NSFormalization/Section3/T19/Closure.lean:49:35: error: Application type mismatch: The argument
  w
has type
  SpaceTimeField
of sort `Sort u_1` but is expected to have type
  VelocityField
of sort `Type` in the application
  spatialGradient w
../formalization/NSFormalization/Section3/T19/Closure.lean:49:45: error: unsolved goals
SpaceTimeField : Sort u_1
T : ℝ
u v w : SpaceTimeField
t : ℝ
x : Space
i : Fin 3
⊢ (fderiv ℝ (fun y => sorry () (t, y)) x) (coordinateVector i) = 0
../formalization/NSFormalization/Section3/T19/Closure.lean:47:86: error: unsolved goals
SpaceTimeField : Sort u_1
T : ℝ
u v w : SpaceTimeField
hg : ∀ (t : ℝ), (fun x => spatialGradient (fun z => -sorry) t x) = -fun x => spatialGradient sorry t x
⊢ essSup (fun t => eLpNorm (torusLift fun x => -sorry) 2 periodicTorusMeasure) (volume.restrict (Ioo 0 T)) +
      (∫⁻ (t : ℝ) in Ioo 0 T, eLpNorm (torusLift fun x => -spatialGradient sorry t x) 2 periodicTorusMeasure ^ 2) ^
        2⁻¹ =
    essSup (fun t => eLpNorm (torusLift fun x => sorry (t, x)) 2 periodicTorusMeasure) (volume.restrict (Ioo 0 T)) +
      (∫⁻ (t : ℝ) in Ioo 0 T, eLpNorm (torusLift fun x => spatialGradient sorry t x) 2 periodicTorusMeasure ^ 2) ^ 2⁻¹
../formalization/NSFormalization/Section3/T19/Closure.lean:56:23: error: Function expected at
  v
but this term has type
  SpaceTimeField

Note: Expected a function because this term is being applied to the argument
  z
../formalization/NSFormalization/Section3/T19/Closure.lean:56:29: error: Function expected at
  u
but this term has type
  SpaceTimeField

Note: Expected a function because this term is being applied to the argument
  z
../formalization/NSFormalization/Section3/T19/Closure.lean:53:48: warning: This simp argument is unused:
  fderiv_neg

Hint: Omit it from the simp argument list.
  [apply] simp [spatialGradient, spatialDerivative]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T19/Closure.lean:55:19: warning: This simp argument is unused:
  torusLift

Hint: Omit it from the simp argument list.
  [apply] simp only [hg, Pi.neg_apply, eLpNorm_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T19/Closure.lean:55:44: warning: This simp argument is unused:
  eLpNorm_neg

Hint: Omit it from the simp argument list.
  [apply] simp only [hg, torusLift, Pi.neg_apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`

```

## Attempt 3 — norm negation

Pointwise negation needs refolding as function negation before `eLpNorm_neg`.

```text
../formalization/NSFormalization/Section3/T19/Closure.lean:47:86: error: unsolved goals
T : ℝ
u v w : SpaceTimeField
hg : ∀ (t : ℝ), (fun x => spatialGradient (fun z => -w z) t x) = -fun x => spatialGradient w t x
⊢ essSup (fun t => eLpNorm (torusLift fun x => -w (t, x)) 2 periodicTorusMeasure) (volume.restrict (Ioo 0 T)) +
      (∫⁻ (t : ℝ) in Ioo 0 T, eLpNorm (torusLift fun x => -spatialGradient w t x) 2 periodicTorusMeasure ^ 2) ^ 2⁻¹ =
    essSup (fun t => eLpNorm (torusLift fun x => w (t, x)) 2 periodicTorusMeasure) (volume.restrict (Ioo 0 T)) +
      (∫⁻ (t : ℝ) in Ioo 0 T, eLpNorm (torusLift fun x => spatialGradient w t x) 2 periodicTorusMeasure ^ 2) ^ 2⁻¹
../formalization/NSFormalization/Section3/T19/Closure.lean:53:48: warning: This simp argument is unused:
  fderiv_neg

Hint: Omit it from the simp argument list.
  [apply] simp [spatialGradient, spatialDerivative]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T19/Closure.lean:55:19: warning: This simp argument is unused:
  torusLift

Hint: Omit it from the simp argument list.
  [apply] simp only [hg, Pi.neg_apply, eLpNorm_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T19/Closure.lean:55:44: warning: This simp argument is unused:
  eLpNorm_neg

Hint: Omit it from the simp argument list.
  [apply] simp only [hg, torusLift, Pi.neg_apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`

```

## Attempt 4 — elaboration of local negation and EqOn

Fix the local helper universe to `Type`; beta-reduce the EqOn goal explicitly.

```text
../formalization/NSFormalization/Section3/T19/Closure.lean:47:86: error: unsolved goals
T : ℝ
u v w : SpaceTimeField
hg : ∀ (t : ℝ), (fun x => spatialGradient (fun z => -w z) t x) = -fun x => spatialGradient w t x
hn' :
  ∀ {E : Type u_1} [inst : NormedAddCommGroup E] (f : Space → E),
    eLpNorm (torusLift fun x => -f x) 2 periodicTorusMeasure = eLpNorm (torusLift f) 2 periodicTorusMeasure
⊢ essSup (fun t => eLpNorm (torusLift fun x => -w (t, x)) 2 periodicTorusMeasure) (volume.restrict (Ioo 0 T)) +
      (∫⁻ (t : ℝ) in Ioo 0 T, eLpNorm (torusLift fun x => -spatialGradient w t x) 2 periodicTorusMeasure ^ 2) ^ 2⁻¹ =
    essSup (fun t => eLpNorm (torusLift fun x => w (t, x)) 2 periodicTorusMeasure) (volume.restrict (Ioo 0 T)) +
      (∫⁻ (t : ℝ) in Ioo 0 T, eLpNorm (torusLift fun x => spatialGradient w t x) 2 periodicTorusMeasure ^ 2) ^ 2⁻¹
../formalization/NSFormalization/Section3/T19/Closure.lean:60:33: warning: This simp argument is unused:
  hn'

Hint: Omit it from the simp argument list.
  [apply] simp only [hg, Pi.neg_apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T19/Closure.lean:96:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (extendByZero reference).velocity z
in the target expression
  (fun z => A.velocity ε z - reference.velocity z) z = (fun z => A.velocity ε z - (extendByZero reference).velocity z) z

a : SpatialField
ha : a ∈ initialClassT
ν : ℝ
hν : 0 < ν
T : ℝ
hT : 0 < T
g : SpaceTimeField
hg : g ∈ forceClassT
δ : ℝ
hδ : 0 < δ
reference : ClassicalSolutionT ν a g (T + δ)
A : T18.PeriodicInsertionAPI (insertionData hν ha hg hT hδ reference) := insertion hν ha hg hT hδ reference
href : ContDiffOn ℝ ∞ reference.velocity (Ico 0 T ×ˢ univ)
ε : ℝ
z : SpaceTime
hz : z ∈ Ico 0 T ×ˢ univ
⊢ (fun z => A.velocity ε z - reference.velocity z) z = (fun z => A.velocity ε z - (extendByZero reference).velocity z) z

```

## Final cleanup

Both fields closed. Replaced the unnecessary `<;>` flagged by the linter:

```text
../formalization/NSFormalization/Section3/T19/Closure.lean:61:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`

```

No residual proof obligations; no extra hypotheses or heartbeat overrides.
