# T15 U9 attempts — lane 450

## Successful route

A value-generic helper replaces the field by zero outside `Iio T`. Its support
is then uniformly bounded in the vendor sense; equality on the slab transfers
`ContDiffOn` to this replacement and transfers the smooth periodization back.
This does not assert smoothness across T. Velocity dilation and placement feed
the helper, and T11 supplies each integer-order datum and continuity of the
selected path. Pressure uses the same helper with scalar values, then subtracts
the spatially constant mean on each slice and applies the continuous-gradient
Haar MemLp theorem. No time regularity of that mean is needed.

## Failed attempts (exact Lean output)

### 1. Set membership did not simplify the conditional

`hz.1` has membership form; explicitly presenting it as `z.1 < T` fixes both
conditional simplifications. Full output:

```
../formalization/NSFormalization/Section3/T15/SobolevPath.lean:33:26: error: unsolved goals
V : Type u_1
inst✝¹ : NormedAddCommGroup V
inst✝ : NormedSpace ℝ V
v : SpaceTime → V
T : ℝ
hv : ContDiffOn ℝ ∞ v (Iio T ×ˢ univ)
hs : ∀ t < T, (tsupport fun x => v (t, x)) ⊆ interior fundamentalCube
w : SpaceTime → V := fun z => if z.1 < T then v z else 0
hw : NavierStokes.PeriodicLocalization.SupportedInCube 1 w
z : SpaceTime
hz : z ∈ Iio T ×ˢ univ
⊢ T ≤ z.1 → 0 = v z
../formalization/NSFormalization/Section3/T15/SobolevPath.lean:22:39: error: unsolved goals
V : Type u_1
inst✝¹ : NormedAddCommGroup V
inst✝ : NormedSpace ℝ V
v : SpaceTime → V
T : ℝ
hv : ContDiffOn ℝ ∞ v (Iio T ×ˢ univ)
hs : ∀ t < T, (tsupport fun x => v (t, x)) ⊆ interior fundamentalCube
w : SpaceTime → V := fun z => if z.1 < T then v z else 0
hw : NavierStokes.PeriodicLocalization.SupportedInCube 1 w
hsm : ContDiffOn ℝ ∞ w (Iio T ×ˢ univ)
z : SpaceTime
hz : z ∈ Iio T ×ˢ univ
n : NavierStokes.PeriodicLocalization.Lattice
⊢ T ≤ z.1 → v (z.1, z.2 - NavierStokes.PeriodicLocalization.lattice n) = 0
../formalization/NSFormalization/Section3/T15/SobolevPath.lean:33:38: warning: This simp argument is unused:
  hz.1

Hint: Omit it from the simp argument list.
  [apply] simp [w]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T15/SobolevPath.lean:38:56: warning: This simp argument is unused:
  hz.1

Hint: Omit it from the simp argument list.
  [apply] simp [NavierStokes.PeriodicLocalization.translate, w]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

### 2. Normalization's constant slice did not elaborate directly

Giving the constant function its explicit `Space → ℝ` type fixes this.

```
../formalization/NSFormalization/Section3/T15/SobolevPath.lean:112:41: error: Application type mismatch: The argument
  contDiff_const
has type
  ContDiff ?m.294 ?m.302 fun x => ?m.303
but is expected to have type
  ContDiff ℝ ∞ fun x => pressureMeanT (periodizedScaledPressure p place.x₀ place.T ε) (t, x).1
in the application
  ContDiff.sub
    (ContDiffOn.comp_contDiff hper (ContDiff.prodMk contDiff_const contDiff_id) fun x => ⟨ht.right, mem_univ x⟩)
    contDiff_const
```

### 3. Probe support refolding and bump normalization

Use a `change` to expose `tsupport` and the bump's `one_of_mem_closedBall`
lemma instead of unfolding the bump structure.

```
../research/T15/probes/sobolev_path_closes.lean:193:14: error: Invalid `←` modifier: `tsupport` is a declaration name to be unfolded

Hint: The simplifier cannot "refold" definitions by name. Use `rw` for this instead,
                      or use the `←` simp modifier with an equational lemma for `tsupport`.
../research/T15/probes/sobolev_path_closes.lean:193:2: error: Type mismatch: After simplification, term
  h
 has type
  closure (Function.support fun x => emPres (t, x)) ⊆ closure (Function.support ↑emSpaceBump)
but is expected to have type
  (tsupport fun x => emPres (t, x)) ⊆ emCarrier
../research/T15/probes/sobolev_path_closes.lean:213:32: error: unsolved goals
⊢ ¬↑{ rIn := 8⁻¹, rOut := 4⁻¹, rIn_pos := ⋯, rIn_lt_rOut := ⋯ } 2⁻¹ = 0 ∧
    ¬↑{ rIn := 8⁻¹, rOut := 4⁻¹, rIn_pos := ⋯, rIn_lt_rOut := ⋯ } 0 = 0
../research/T15/probes/sobolev_path_closes.lean:216:33: error: unsolved goals
⊢ ↑{ rIn := 8⁻¹, rOut := 4⁻¹, rIn_pos := ⋯, rIn_lt_rOut := ⋯ } 2⁻¹ *
      ↑{ rIn := 8⁻¹, rOut := 4⁻¹, rIn_pos := ⋯, rIn_lt_rOut := ⋯ } 0 =
    1
```

### Search command typo

A duplicated extension in a shell glob produced:
`zsh:1: no matches found: formalization/NSFormalization/Section4/I03/*.lean.lean`.
The corrected search used the I03 directory directly. No mathematical route was
abandoned and no residual hypothesis was introduced.

### 4. Probe `simp` normalized `1/2` before using its value

An explicit `change` and `rw [ht]` preserve the matching expression.

```
../research/T15/probes/sobolev_path_closes.lean:214:32: error: unsolved goals
hb : ↑emSpaceBump 0 = 1
ht : ↑emTimeBump (1 / 2) = 1
⊢ ¬↑emTimeBump 2⁻¹ = 0
../research/T15/probes/sobolev_path_closes.lean:219:28: warning: This simp argument is unused:
  ht

Hint: Omit it from the simp argument list.
  [apply] simp [emVel, emField, hb, coordinateVector]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../research/T15/probes/sobolev_path_closes.lean:221:33: error: unsolved goals
hb : ↑emSpaceBump 0 = 1
ht : ↑emTimeBump (1 / 2) = 1
⊢ ↑emTimeBump 2⁻¹ = 1
../research/T15/probes/sobolev_path_closes.lean:226:20: warning: This simp argument is unused:
  ht

Hint: Omit it from the simp argument list.
  [apply] simp [emPres, hb]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```
