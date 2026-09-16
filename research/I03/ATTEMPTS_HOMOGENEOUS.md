# Lane 250: homogeneous scaling attempts and status

## Exact draft fields (verbatim)

```lean
  packetNegativeHomogeneous : ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, -3 / 2 < s → s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      Data.forceHomogeneousENorm q s (scaledForce packet.force x₀ T ε) ≤
        ENNReal.ofReal (negativeConst q s * ε ^ thresholds.exponent q.toReal s)

  correctionNegativeHomogeneous : ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, -3 / 2 < s → s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      Data.forceHomogeneousENorm q s (forceCorrection ε) ≤
        ENNReal.ofReal (correctionNegativeConst q s *
          ε ^ (thresholds.exponent q.toReal s + 1))
```

## Proven route

The convention is `k = ε⁻¹`, physical force amplitude `k³`, source time
`k²(t-t₀)`, and spatial argument `k(x-x₀)`. Packet delay is `t₀=T-ε²`;
the correction profile uses `t₀=T` and an additional amplitude `ε`.

`HomogeneousScaling.lean` proves the exact cycles homogeneous integral identity,
spatial norm identity, scalar time identity including infinity, the exact angular
energy factor `(2π)^(2s)`, and the norm identity for genuine homogeneous vector
slice data. It also proves the exact vector-datum time identity. Positive-time
restriction preserves it when the original force is zero at nonpositive times
and the delay is nonnegative. No integrability claim is extracted from a
potentially totalized divergent real integral: compact smooth profile finiteness
is separately obtained in the range `-3/2 < s ≤ 0`.

The actual correction estimate reuses `scalarPhysicalForce_eq` and
`scalarProfile_uniform_homogeneous_time`; it does not apply an arbitrary-family
regularity premise as if that implied epsilon decay. Its component bounds are
summed. `Bindings.forceCorrection_eq_extension` transfers them back to exactly
the abstract correction's force on `scalingThreshold C`, the same threshold as
`Bindings.scaling C th`.

`Bindings/ScalingHomogeneous.lean` is required for registered Data and Scaling
vocabulary: NSFormalization cannot import its downstream Contracts library.
`homogeneousScaling hreal C th` inhabits the already stated but unregistered
`HomogeneousScalingAPI`, conditional on the one input below. Neither homogeneous
field was registered before this lane; neither is newly registered here.

Packet constant in this API is exactly
`(Data.forceHomogeneousENorm q s P.force).toReal` (proved finite in range).
The separate component-majorant theorem has the explicit constant
`(2π)^s * (Σ_i ‖profile_i‖_{L^q_t dot H^s,cycles}).toReal`.
Correction constant is `(2π)^s * K.toReal`, where `K=Σ_i K_i` and each finite
`K_i` is the uniform correction profile time bound from the existing compact
profile theorem. It is uniform in epsilon. The assembly uses the exact existing
API quantifier order; the standalone correction lemma first fixes `(q,s)` to
choose its constant, then `exists_correction_homogeneous_const` makes the total
constant family.

## Single remaining analytic hypothesis (exact statement)

```lean
def CompactHomogeneousRealization : Prop :=
  ∀ (s : ℝ) (hs : -3 / 2 < s), s < 0 → ∀ (F : VelocityField)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F),
    AEStronglyMeasurable (D01.Homogeneous.compactHomogeneousPath hs hF hc)
      Data.forceTimeMeasure
```

This is precisely the time measurability obligation for D01's existing concrete
path, independent of any scaling estimate. Slice validity, angular normalization,
pointwise norm bound, and scalar norm measurability are proved, not additional
inputs. Scalar norm measurability alone does not imply vector path measurability.
The infimum is bounded by exhibiting this actual path and its pairing proof;
there is no conversion from the negative-order Bessel datum.

Zero-force satisfiability is proved for this very constructor at every allowed
order (`compact_realization_zero`); the registered zero-force norm is zero at
all real orders without the hypothesis. The audit additionally instantiates the
slice path with the actual PacketAPI force at s=-1; its finite component profile
norm is also checked, including the concrete `Bindings.packet 1` constructor.
Nonzero packet time measurability is not claimed proved.
Thus the Prop. 4.6 / Thm 4.7 application remains conditional on this input.

## Attempts and pitfalls

* D01/HomogeneousWitness already produces negative-order slice data: the old
  COMPARISON/ATTEMPTS claims that no datum exists are historical. The unresolved
  part is the measurable path, not the Fourier scaling calculation.
* R43/CriticalDatumPath.ofSobolevVector requires `0 ≤ s`; negative orders cannot
  use its contractive Bessel-to-homogeneous conversion.
* Exact homogeneous scaling works by pulling back the weighted integrand with
  `ξ ↦ k⁻¹ ξ`; the weight contributes exactly `k^(2s)`. No comparison with a
  Bessel weight is used.
* `ENNReal.toReal_rpow` is oriented from the real power to `.toReal` of the
  extended power: simplifying the latter requires its reverse direction.
* Strongly measurable finite sums of functions require an extensional bridge
  between `Σ_i f_i` and `t ↦ Σ_i f_i t`.
* To recover norm equality from squares use `sq_eq_sq₀` with both nonnegativity
  facts. A raw nonlinear arithmetic call did not resolve the product square.
* All newly written declarations elaborate without increased heartbeat limits.
  Existing dependency linter warnings may be replayed by Lake; the two new
  modules themselves must have zero direct Lean output.

## Validation

See REPORT_250.md for the final commands and results. The audit enumerates every
named declaration in both new proof modules and checks the zero force plus the
actual packet's homogeneous slice path. Existing Lean modules, frozen contracts,
registry, and generated task files are unchanged.

The concrete packet example is in `packet_homogeneous_example.lean`: importing
both existing `Bindings.Packet` and `Bindings.Scaling` in one environment fails
because both declare `BlowupDensity.Bindings.navierStokesResidual_eq`. This
pre-existing collision is avoided with separate probes, without editing either
existing module. The main audit still checks the generic actual PacketAPI path.
