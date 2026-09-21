# Lane 456 attempts

## A1: endpoint component elaboration

The endpoint-product application unfolds `coordinateForce` in its result; `simp only [chartForce_fourierNorm]` cannot match the unfolded projection. Refold the endpoint integrands with `change` before rewriting. Exact diagnostic:

```text
../formalization/NSFormalization/Section3/T15/SobolevBound.lean:160:80: error: Application type mismatch: The argument
  hrate1
has type
  eLpNorm
      (fun t =>
        fourierSobolevNorm 1 fun x => coordinateForce (Source.parabolicForce ε⁻¹ (place.T - ε ^ 2) 0 f) i (t, x))
      1 volume ≤
    ENNReal.ofReal (ε ^ (-1 / 2)) * eLpNorm (fun t => fourierSobolevNorm 1 fun x => coordinateForce f i (t, x)) 1 volume
but is expected to have type
  eLpNorm (fun t => fourierSobolevNorm 1 fun x => ↑((chartForce f place.x₀ place.chartCenter place.T ε (t, x)).ofLp i))
      1 volume ≤
    ?m.324
in the application
  mul_le_mul' (le_refl (ENNReal.ofReal (2 * Real.pi))) hrate1
../formalization/NSFormalization/Section3/T15/SobolevBound.lean:153:13: warning: This simp argument is unused:
  chartForce_fourierNorm

Hint: Omit it from the simp argument list.
  [apply] simp only

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

## A2: endpoint finiteness rewrite inside the constant

Rewriting endpoint norms by `ofReal_toReal` also rewrites their occurrences inside the RHS constant. Normalize those new `toReal (ofReal c)` expressions with nonnegativity before ring arithmetic. Exact diagnostic:

```text
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
../formalization/NSFormalization/Section3/T15/SobolevBound.lean:131:77: error: unsolved goals
u f : VelocityField
p : PressureField
K : Set Space
hf : ContDiff ℝ ∞ f
hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f
place : PlacementData u p f K
ε : ℝ
hε : ε ∈ Ioc 0 place.ε₀
s : ℝ
hs0 : 0 ≤ s
hs1 : s ≤ 1
i : Fin 3
hε0 : 0 < ε
hε1 : ε ≤ 1
hS : SupportedInCube place.chartRadius (chartForce f place.x₀ place.chartCenter place.T ε)
hr : place.chartRadius < 1 / 2
hsm : ContDiff ℝ ∞ (chartForce f place.x₀ place.chartCenter place.T ε)
hcp : HasCompactSupport (chartForce f place.x₀ place.chartCenter place.T ε)
hcoord :
  (fun z =>
      ↑((NavierStokes.PeriodicLocalization.periodize (chartForce f place.x₀ place.chartCenter place.T ε) z).ofLp i)) =
    NavierStokes.PeriodicLocalization.periodize fun z => ↑((chartForce f place.x₀ place.chartCenter place.T ε z).ofLp i)
heq :
  (fun t =>
      Paper1.periodicSobolevNorm s fun x =>
        coordinateForce
          (NavierStokes.PeriodicLocalization.periodize (chartForce f place.x₀ place.chartCenter place.T ε)) i (t, x)) =
    fun t =>
    Paper1.periodicSobolevNorm s fun x =>
      NavierStokes.PeriodicLocalization.periodize
        (coordinateForce (chartForce f place.x₀ place.chartCenter place.T ε) i) (t, x)
hrate0 :
  eLpNorm
      (fun t =>
        fourierSobolevNorm 0 fun x => coordinateForce (Source.parabolicForce ε⁻¹ (place.T - ε ^ 2) 0 f) i (t, x))
      1 volume ≤
    ENNReal.ofReal (ε ^ (1 / 2)) * eLpNorm (fun t => fourierSobolevNorm 0 fun x => coordinateForce f i (t, x)) 1 volume
hrate1 :
  eLpNorm
      (fun t =>
        fourierSobolevNorm 1 fun x => coordinateForce (Source.parabolicForce ε⁻¹ (place.T - ε ^ 2) 0 f) i (t, x))
      1 volume ≤
    ENNReal.ofReal (ε ^ (-1 / 2)) * eLpNorm (fun t => fourierSobolevNorm 1 fun x => coordinateForce f i (t, x)) 1 volume
hC0top : packetEndpoint f 0 i < ∞
hC1top : packetEndpoint f 1 i < ∞
c0 : ℝ := (packetEndpoint f 0 i).toReal
hc0def : c0 = (packetEndpoint f 0 i).toReal
c1 : ℝ := (packetEndpoint f 1 i).toReal
hc1def : c1 = (packetEndpoint f 1 i).toReal
hc0 : 0 ≤ c0
hc1 : 0 ≤ c1
hstep1 : (ε ^ (1 / 2) * c0) ^ (1 - s) = ε ^ (1 / 2 * (1 - s)) * c0 ^ (1 - s)
hstep2 : (2 * Real.pi * (ε ^ (-1 / 2) * c1)) ^ s = ε ^ (-1 / 2 * s) * (2 * Real.pi * c1) ^ s
⊢ ε ^ (1 / 2 + s * (-1 / 2)) * c0 ^ (1 - s) * ε ^ (s * (-1 / 2)) * (Real.pi * c1 * 2) ^ s =
    ε ^ (1 / 2 + s * (-1 / 2)) * ε ^ (s * (-1 / 2)) * (ENNReal.ofReal c0).toReal ^ (1 - s) *
      (Real.pi * (ENNReal.ofReal c1).toReal * 2) ^ s
```

## Route selection and successful closure

Read the T13 assembled API, the Section 4 homogeneous scaling and cycles-to-datum transfer, the lane-438 report including its review correction, and the packet endpoint modules. Chose route B. No new analytic hypothesis or datum placeholder was introduced.

A sufficient adapter for route A would be the following (not asserted as a Lean theorem here): for `z : Space → Space`, `ContDiff ℝ ∞ z`, `HasCompactSupport z`, and `0 ≤ s ≤ 1`,

```lean
NSFormalization.Section4.D01.dotHomogeneousENorm s z ≤
  ENNReal.ofReal ((2 * Real.pi) ^ s *
    Real.sqrt (∑ i : Fin 3,
      NSFormalization.Source.fourierSobolevSq s (fun x => (z x i : ℂ))))
```

The already-proved `dotHomogeneousENorm_eq_homogeneousFourierENorm` identifies the datum infimum, and `Source/FourierConvention.lean` contains the actual angular/cycles convention bridge. Thus this is NOT a claim that the convention bridge is missing. A ready-made adapter with the displayed source and target was not located by `grep -rn --include='*.lean' 'dotHomogeneousENorm.*fourierSobolev\|homogeneousFourierENorm.*fourierSobolev' formalization/NSFormalization verification/Bindings`. No Lean proof of this adapter was attempted, and there is no compiler error for the route decision. It is unnecessary for the delivered result.

The eventual statement `eventually_packet_coordinate_periodized_endpoint_product` does not directly give all `ε ∈ Ioc 0 place.ε₀`. Instead apply `periodized_scalar_L1Hs_le_endpoint_product` at each admissible scale. Unlike the correction proof, raw `PlacementData` need not have its packet center equal to its chart center. `chartForce` translates the copy by `place.chartCenter`; `ball_coord_bounds` proves `chartRadius < 1/2`. The existing support transport supplies `SupportedInCube chartRadius`. Translation invariance gives the whole-space endpoint rates without imposing any additional condition on `place.x₀`.

The endpoint rates interpolate to `ε^(1/2-s)`. Component assembly and the added positive `1` in the constant imply the requested two-term bound. The real-order continuous, compactly supported Fourier datum path is supplied by `T17.force_coefficient_path_real` applied to `T15.force_mem`.

## Search-only failure

The brief's `Section4/I03/Sobolev*.lean` glob does not match this checkout. Exact shell diagnostic:

```text
zsh:1: no matches found: formalization/NSFormalization/Section4/I03/Sobolev*.lean
```

Resolved using `rg --files formalization/NSFormalization/Section4/I03` and `rg -n sobolev verification/Bindings/Scaling.lean`; the relevant modules are `HomogeneousScaling.lean`, `Angular.lean`, and the binding's `exists_packet_positive_const`. No source file was changed in response.
