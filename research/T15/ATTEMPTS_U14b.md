# U14b attempts (lane 462)

## Sharp lattice summability

Route: dominate `W^s` by the product of `(1+k_i²)^(s/3)`.
Each coordinate series is compared with the integer p-series away from zero,
with a separate singleton majorant at zero. This reaches every `s < -3/2`.

First elaboration diagnostics (ConvergenceTwo.lean):

```text
25:4: error: unsolved goals
⊢ 0 ≤ 0 ^ (2 * a)
27:17: warning: `if_neg` has been deprecated: Use `ite_eq_right` instead
33:35: error: unsolved goals
⊢ |↑n| ^ (↑2 * a) = |↑n| ^ (2 * a)
44:2: error: linarith failed to find a contradiction
k : PeriodicFrequency
i : Fin 3
hsum : ↑(k i) ^ 2 ≤ ∑ x, ↑(k x) ^ 2
hn : 0 ≤ ∑ j, ↑(k j) ^ 2
a✝ : 1 + 4 * Real.pi ^ 2 * ∑ i, ↑(k i) ^ 2 < 1 + ↑(k i) ^ 2
⊢ False
failed
```

Resolved with explicit nonnegativity at zero, `norm_num` for the cast,
`ite_eq_right`, and the nonnegative product `(4π²-1) * Σ k_i²`.

## Datum L1 bound

First elaboration diagnostics:

```text
150:10: error(lean.unknownIdentifier): Unknown identifier `abs_spaceCoord_le_norm`
153:19: error: Application type mismatch: The argument
  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?m.281 hi 2) hC
has type
  C * (∫ (y : Paper1.PeriodicTorus), ‖torusLift (fun x => ↑((z x).ofLp i)) y‖ ∂periodicTorusMeasure) ^ 2 ≤ C * L ^ 2
but is expected to have type
  (∑' (k : PeriodicFrequency), Paper1.periodicFrequencyWeight k ^ s) *
      (∫ (y : Paper1.PeriodicTorus), ‖torusLift (fun x => ↑((z x).ofLp i)) y‖ ∂periodicTorusMeasure) ^ 2 ≤
    C * L ^ 2
159:6: error: Type mismatch: After simplification, term
  Finset.sum_le_sum fun i x => hb i
 has type
  @LE.le ℝ Real.instPreorder.toLE (∑ x, Paper1.periodicSobolevSq s fun x_1 => ↑((z x_1).ofLp x))
    (↑Finset.univ.card * (C * L ^ 2))
but is expected to have type
  @LE.le ℝ Real.instLE (∑ x, Paper1.periodicSobolevSq s fun x_1 => ↑((z x_1).ofLp x)) (3 * (C * L ^ 2))
```

The coordinate bound is in `T13`; the two Fourier-weight definitions require
`periodicFrequencyWeight_eq_paper1`; the finite sum needs an explicit `Fin 3` index.

Further diagnostic, resolved by `change` before simplifying the scalar norm:

```text
149:8: error: Type mismatch: After simplification, term
  T13.abs_spaceCoord_le_norm (torusLift z y) i
 has type
  |(torusLift z y).ofLp i| ≤ ‖torusLift z y‖
but is expected to have type
  ‖torusLift (fun x => ↑((z x).ofLp i)) y‖ ≤ ‖torusLift z y‖
```

## Endpoint path plumbing

The first attempt lacked the explicit `T15.Mixed` import and used generic
continuous multiplication on `ENNReal`, which is not available at infinity:

```text
184:13: error(lean.unknownIdentifier): Unknown identifier `scaledForce_contDiff`
225:8: error(lean.unknownIdentifier): Unknown identifier `mixedLebesgueENorm_eq`
231:14: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  SeparatelyContinuousMul ℝ≥0∞
231:27: error: Application type mismatch: The argument
  hfinite
has type
  mixedLebesgueENorm 2 1 f ≠ ∞
of sort `Prop` but is expected to have type
  ℝ≥0∞
of sort `Type` in the application
  Tendsto.mul_const hfinite
```

After importing the existing closure, the next iteration required converting
the integral to a lintegral before rewriting the single-copy equality:

```text
195:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∫ (x : PeriodicTorus),
    ‖torusLift (fun x => periodizedScaledForce f place.x₀ place.T ε (t, x)) x‖ ∂periodicTorusMeasure
in the target expression
  ‖G t‖ ≤
    C *
      ∫ (y : Paper1.PeriodicTorus),
        ‖torusLift (fun x => scaledForce f place.x₀ place.T ε (t, x)) y‖ ∂periodicTorusMeasure
210:6: error: Type mismatch: After simplification, term
  hb t
 has type
  ‖G t‖ ≤ C * (eLpNorm (torusLift fun x => H (t, x)) 1 periodicTorusMeasure).toReal
but is expected to have type
  ‖G t‖ ≤ |C * (eLpNorm (torusLift fun x => H (t, x)) 1 periodicTorusMeasure).toReal|
213:10: error(lean.unknownIdentifier): Unknown identifier `eLpNorm_const_mul`
233:60: error: Application type mismatch: The argument
  ENNReal.ofReal_ne_top
has type
  ENNReal.ofReal ?m.192 ≠ ∞
but is expected to have type
  0 * mixedLebesgueENorm 2 1 f ≠ 0
in the application
  Or.inl ENNReal.ofReal_ne_top
```

Resolved with `le_abs_self`, `eLpNorm_const_smul`, and the right disjunct of
`ENNReal.Tendsto.const_mul`. No new path infrastructure was assumed.

## Interpolation and final scaling: exact saved diagnostics

The finite-index summability proof uses `(hasSum_fintype _).summable`.
`ENNReal` powers require `mul_rpow_of_nonneg` (there is no unconditional
`ENNReal.mul_rpow`). Normalization under powers and the composed slice lambda
must be made explicit before rewriting. The diagnostics below are from the
failed iterations; all are resolved in the delivered module.

### interpolation_diagnostics_462.log

```text
../formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:182:10: error(lean.unknownIdentifier): Unknown identifier `summable_fintype`
../formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:228:71: error: unsolved goals
case e_a
r θ : ℝ
hθ : 0 < θ
hθ1 : θ < 1
z : Space → Space
hz : ContDiff ℝ ∞ z
A : ↥(PeriodicSobolev ((1 - θ) * r))
B : ↥(PeriodicSobolev 0)
D : ↥(PeriodicSobolev r)
hA : IsPeriodicDatum ((1 - θ) * r) z A
hB : IsPeriodicDatum 0 z B
hD : IsPeriodicDatum r z D
e : ℝ → Fin 3 × PeriodicFrequency → ℝ :=
  fun a j => periodicFrequencyWeight j.2 ^ a * ‖periodicFourierCoeff (fun x => ↑((z x).ofLp j.1)) j.2‖ ^ 2
hn : ∀ (a : ℝ) (j : Fin 3 × PeriodicFrequency), 0 ≤ e a j
he : ∀ (j : Fin 3 × PeriodicFrequency), e ((1 - θ) * r) j = e 0 j ^ θ * e r j ^ (1 - θ)
hi :
  ∑' (i : Fin 3 × PeriodicFrequency), e 0 i ^ θ * e r i ^ (1 - θ) ≤
    (∑' (i : Fin 3 × PeriodicFrequency), e 0 i) ^ θ * (∑' (i : Fin 3 × PeriodicFrequency), e r i) ^ (1 - θ)
hsq : ‖A‖ ^ 2 ≤ (‖B‖ ^ 2) ^ θ * (‖D‖ ^ 2) ^ (1 - θ)
hh : ‖A‖ ≤ √((‖B‖ ^ 2) ^ θ) * √((‖D‖ ^ 2) ^ (1 - θ))
x a : ℝ
hx : 0 ≤ x
⊢ 2 * a * (1 / 2) = a
```

### interpolation_diagnostics_462b.log

```text
../formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:182:10: error(lean.unknownIdentifier): Unknown identifier `summable_of_finite`
```

### time_interpolation_diagnostics_462.log

```text
../formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:249:13: error(lean.unknownIdentifier): Unknown constant `ENNReal.mul_rpow`
../formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:256:4: error(lean.unknownIdentifier): Unknown constant `ENNReal.mul_rpow`
../formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:257:25: error: `simp` made no progress
../formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:257:25: error: `simp` made no progress
../formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:256:22: warning: This simp argument is unused:
  ← ENNReal.rpow_mul

Hint: Omit it from the simp argument list.
  [apply] simp only [Real.enorm_eq_ofReal (mul_nonneg (Real.rpow_nonneg (ha0 _) _) (Real.rpow_nonneg (hb0 _) _)),
    ENNReal.ofReal_mul (Real.rpow_nonneg (ha0 _) _), ← ENNReal.ofReal_rpow_of_nonneg (ha0 _) hθ,
    ← ENNReal.ofReal_rpow_of_nonneg (hb0 _) hns, Real.enorm_eq_ofReal (ha0 _), Real.enorm_eq_ofReal (hb0 _),
    ENNReal.mul_rpow]

Note: Simp arguments with `←` have the additional effect of removing the other direction from the simp set, even if the simp argument itself is unused. If the hint above does not work, try replacing `←` with `-` to only get that effect and silence this warning.

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

### time_interpolation_diagnostics_462b.log

```text
Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
```

### path_diagnostics_462.log

```text
../formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:305:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ENNReal.ofReal (ε ^ (-(1 / 2))) * mixedLebesgueENorm 2 2 f
in the target expression
  forceSobolevENormT 2 0 (periodizedScaledForce f place.x₀ place.T ε) =
    ENNReal.ofReal (ε ^ (-1 / 2)) * mixedLebesgueENorm 2 2 f

u f : VelocityField
p : PressureField
K : Set Space
hf : ContDiff ℝ ∞ f
hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f
place : PlacementData u p f K
ε : ℝ
hε : ε ∈ Ioc 0 place.ε₀
hF : MemForceT (periodizedScaledForce f place.x₀ place.T ε)
hH : ContDiff ℝ ∞ (scaledForce f place.x₀ place.T ε)
hHc : HasCompactSupport (scaledForce f place.x₀ place.T ε)
G : ℝ → ↥(PeriodicSobolev 0)
hG : ∀ (t : ℝ), IsPeriodicDatum 0 (fun x => periodizedScaledForce f place.x₀ place.T ε (t, x)) (G t)
left✝¹ : Continuous G
left✝ : HasCompactSupport G
hm : StronglyMeasurable G
hp : IsPeriodicSobolevPath 0 (periodizedScaledForce f place.x₀ place.T ε) G
right✝ : MemLp G 1 forceTimeMeasure
hmixed :
  mixedLebesgueENormT 2 2 (periodizedScaledForce f place.x₀ place.T ε) =
    ENNReal.ofReal (ε ^ (-(1 / 2))) * mixedLebesgueENorm 2 2 f
⊢ forceSobolevENormT 2 0 (periodizedScaledForce f place.x₀ place.T ε) =
    ENNReal.ofReal (ε ^ (-1 / 2)) * mixedLebesgueENorm 2 2 f
```

### scaling_diagnostics_462.log

```text
../formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:313:40: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  periodicSobolevENorm 0 (periodizedScaledForce f place.x₀ place.T ε ∘ fun x => (t, id x))
in the target expression
  (periodicSobolevENorm 0 fun x => periodizedScaledForce f place.x₀ place.T ε (t, x)) =
    eLpNorm (torusLift fun x => scaledForce f place.x₀ place.T ε (t, x)) 2 periodicTorusMeasure

u f : VelocityField
p : PressureField
K : Set Space
hf : ContDiff ℝ ∞ f
hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f
place : PlacementData u p f K
ε : ℝ
hε : ε ∈ Ioc 0 place.ε₀
hF : MemForceT (periodizedScaledForce f place.x₀ place.T ε)
hH : ContDiff ℝ ∞ (scaledForce f place.x₀ place.T ε)
hHc : HasCompactSupport (scaledForce f place.x₀ place.T ε)
G : ℝ → ↥(PeriodicSobolev 0)
hG : ∀ (t : ℝ), IsPeriodicDatum 0 (fun x => periodizedScaledForce f place.x₀ place.T ε (t, x)) (G t)
left✝¹ : Continuous G
left✝ : HasCompactSupport G
hm : StronglyMeasurable G
hp : IsPeriodicSobolevPath 0 (periodizedScaledForce f place.x₀ place.T ε) G
right✝ : MemLp G 1 forceTimeMeasure
hmixed :
  mixedLebesgueENormT 2 2 (periodizedScaledForce f place.x₀ place.T ε) =
    ENNReal.ofReal (ε ^ (-(1 / 2))) * mixedLebesgueENorm 2 2 f
t : ℝ
hmem : MemLp (torusLift fun x => scaledForce f place.x₀ place.T ε (t, x)) 2 periodicTorusMeasure
⊢ (periodicSobolevENorm 0 fun x => periodizedScaledForce f place.x₀ place.T ε (t, x)) =
    eLpNorm (torusLift fun x => scaledForce f place.x₀ place.T ε (t, x)) 2 periodicTorusMeasure
```

## Final status

No mathematical residual. `forceConvergence_two` closes every `s < -1/2`,
and `forceConvergence` closes the literal two-exponent canonical field.
The threshold is obtained with `r = (3*s - 3/2)/2` in the interpolated branch:
`3*s < r < -3/2`, `θ = 1-s/r`, and `1-3*θ/2 > 0`.
All 17 declarations print exactly `[propext, Classical.choice, Quot.sound]`.
