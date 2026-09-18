# REPORT 390 — T20 W1 units U3 `bIntegral` and U4 `constantTransportSkew`

Branch `erenup/390-T20-U3-U4-bintegral-transport`. Both reconciled
`CriticalRegularityTAPI` fields proved verbatim over the canonical
`formalization/NSFormalization/Section3/T20/CriticalRegularity.lean` (lane 381).

## 1. What was proved (exact statements)

`NSFormalization.Section3.T20.bIntegral` (`Section3/T20/BIntegral.lean`):
```
∀ (g : SpaceTimeField), g ∈ forceClassT →
  criticalBIntegral (meanFreeForce g) ≤ criticalRho g
```
(`eq:bintegral`, `03-torus.tex:442-444`): removing the spatial zero mode is
contractive on the inhomogeneous `H^{1/2}` datum path, so the full-time
`Ḣ^{1/2}` mean-free-force integral is `≤ ρ = ‖g‖_{L¹(0,∞;H^{1/2})}`.

`NSFormalization.Section3.T20.constantTransportSkew` (`Section3/T20/ConstantTransport.lean`):
```
∀ (m : Space) (v w : SpatialField),
  SmoothPeriodicT v → SmoothPeriodicT w →
    Integrable (fun y : PeriodicTorus ↦
      (inner ℝ (torusLift (constantTransportSpatialT m v) y) (torusLift w y) : ℝ)) periodicTorusMeasure →
    Integrable (fun y : PeriodicTorus ↦
      (inner ℝ (torusLift v y) (torusLift (constantTransportSpatialT m w) y) : ℝ)) periodicTorusMeasure →
      periodicPairing (constantTransportSpatialT m v) w =
        -periodicPairing v (constantTransportSpatialT m w)
```
(`03-torus.tex:411`): the constant-coefficient transport `(m·∇)` is skew-adjoint
on `L²(T³)`.

Both print exactly `[propext, Classical.choice, Quot.sound]`.

## 2. What exists in Lean now

- Files: `formalization/NSFormalization/Section3/T20/BIntegral.lean`,
  `formalization/NSFormalization/Section3/T20/ConstantTransport.lean`.
- Probe: `research/T20/probes/bintegral_transport_closes.lean` — both field types
  closed by `exact`; non-vacuity (nonzero smooth periodic mode; `forceClassT` inhabited).
- Axiom audit: `research/T20/axioms_u3_u4.lean`. Attempts: `research/T20/ATTEMPTS_U3_U4.md`.
- Reuse: U4 rides `NavierStokes.PeriodicUniqueness.cubeIntegral_inner_partial`
  (cube IBP) + `NSFormalization.Paper1.integral_torusLift`; U3 rides
  `T12.SpectralGap.reweightDatum`/`reweightDatum_real`/`reweightDatum_norm_le` and
  `T10.DatumBasics.{periodicFourierCoeff_sub,periodicFourierCoeff_const}` +
  `T11.MeanIdentity.meanT_sub_const`. `meanFreeForce g (t,·) = meanZeroPartT (g(t,·))`
  is definitional.

## 3. Gaps / residuals

None for these two units — both fields are closed, verbatim, with the standard
three axioms. Out of scope (unchanged): the remaining T20 fields, including the
T12-blocked analytic core (U7/U8/U10). One `set_option maxHeartbeats 400000 in`
guards the `IsPeriodicHomogeneousDatum` reconstruction in `bIntegral_slice`
(within the ≤ 400000 limit, per-declaration, commented). No `sorry`/`axiom`/
`native_decide`, no named inputs, no placeholder `Prop`, no goal repackaging.

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.BIntegral NSFormalization.Section3.T20.ConstantTransport` → `Build completed successfully (10593 jobs).`
- `lake env lean` on both modules → no errors.
- `lake env lean ../research/T20/axioms_u3_u4.lean` →
  `bIntegral … [propext, Classical.choice, Quot.sound]`,
  `constantTransportSkew … [propext, Classical.choice, Quot.sound]`.
- `lake env lean ../research/T20/probes/bintegral_transport_closes.lean` → no errors/warnings.
- `make check` → contract policy 13 tests OK; work queue 45 items consistent; architecture checks pass.
