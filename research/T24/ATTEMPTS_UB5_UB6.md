# Lane 469 — Ub5 / Ub6 attempts

All four fields are closed. No additional analytic input, admission, new axiom,
or heartbeat override is used. Existing Lean modules were not edited.

## Statement checks and route corrections

- T15 `unboundedSpeed` gives `SpeedUnboundedAt T`, without a ball constraint.
  Its proof constructs Euclidean scaled witnesses before periodizing. We reuse
  that construction and retain `affineImage_subset_ball` membership. The
  placement chart is definitionally the prescribed region (same centre/radius).
- `packetEnergyIdentity` is an essential-supremum identity, not equality of
  every slice norm. The proof uses `ENNReal.ae_le_essSup` for all finitely many
  components, squares, adds, then bounds the assembled essential supremum.
- Gradient support is proved on `interior fundamentalCube` using local
  single-copy equality and `fderiv_of_notMem_tsupport` for the scaled field.
  The cube boundary is null (`volume_frontier_fundamentalCube`). No assertion
  that disjoint open balls have disjoint closures is used.
- Time measurability for summing dissipation integrals comes from
  `I03.scaled_dissipation_integrableOn` and the squared-gradient-rate identity.
  The final constant uses `packetDissipationIdentity`; the parameter named `E`
  in `RegionsData` is precisely the parameter named `D` in `MultipleRegionsAPI`.

## A1 — finite sum hidden behind definitions (resolved)

Initial `apply Finset.sum_eq_single j` failed:

```text
Tactic `apply` failed: could not unify the conclusion of `Finset.sum_eq_single j`
  ∑ x ∈ ?m.75, ?m.76 x = ?m.76 j
with the goal
  d.assembledVelocity (t, x) = (d.component j).velocity (t, x)
```

Fix: explicitly `change (∑ i, (d.component i).velocity (t, x)) = _`.

## A2 — definitionally equal placement horizon in rewrite (resolved)

```text
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  periodizedScaledVelocity u (d.placement j).x₀ (d.placement j).T (d.ε j) (t, x)
in the target expression
  A < ‖periodizedScaledVelocity u (d.placement j).x₀ d.T (d.ε j) (t, x)‖
```

Fix: rewrite `d.placement_time j` in the single-copy equality first.

## A3 — NNReal notation and the same horizon in MemLp (resolved)

```text
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  LE Type
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  OfNat Type 0
```

The `ℝ≥0` annotation required opening the `NNReal` scope; recovery then
produced an unsolved synthetic goal (not a source admission).

```text
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  periodizedScaledVelocity u (d.placement j).x₀ d.T (d.ε j)
in the target expression
  MemLp (torusLift fun x => periodizedScaledVelocity u (d.placement j).x₀ (d.placement j).T (d.ε j) (t, x)) 2
    periodicTorusMeasure
```

Fix: `rw [d.placement_time j, ← (d.component_pin j).1] at hm`.

## A4 — apply leaves an autoParam goal (resolved)

```text
error: unsolved goals
case hfbdd
⊢ autoParam
    (Filter.IsCoboundedUnder (fun x1 x2 => x1 ≤ x2) (ae (volume.restrict (Ioo 0 d.T))) fun t =>
      eLpNorm (torusLift fun x => d.assembledVelocity (t, x)) 2 periodicTorusMeasure)
    essSup_le_of_ae_le._auto_1
```

Fix: supply `(by apply Filter.isCobounded_le_of_bot)` explicitly to
`essSup_le_of_ae_le`.

## A5 — gradient finite sum simp names (resolved)

```text
../formalization/NSFormalization/Section3/T24/MultipleRegions.lean:191:8: warning: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`).
../formalization/NSFormalization/Section3/T24/MultipleRegions.lean:191:39: error(lean.unknownIdentifier): Unknown constant `WithLp.sum_apply`
../formalization/NSFormalization/Section3/T24/MultipleRegions.lean:191:57: error(lean.unknownIdentifier): Unknown constant `WithLp.toLp_apply`
../formalization/NSFormalization/Section3/T24/MultipleRegions.lean:186:59: error: unsolved goals
ν : ℝ
u f : VelocityField
p : PressureField
K : Set Space
M E : ℝ
d : RegionsData ν u p f K M E
t : ℝ
ht : t < d.T
x : Space
hd :
  fderiv ℝ (fun y => ∑ i, (d.component i).velocity (t, y)) x =
    ∑ i, fderiv ℝ (fun x => (d.component i).velocity (t, x)) x
i k : Fin 3
⊢ (∑ i_1, (fderiv ℝ (fun x => (d.component i_1).velocity (t, x)) x) (coordinateVector i)).ofLp k =
    ((∑ j, WithLp.toLp 2 fun i => (fderiv ℝ (fun y => (d.component j).velocity (t, y)) x) (coordinateVector i)).ofLp
          i).ofLp
      k
../formalization/NSFormalization/Section3/T24/MultipleRegions.lean:191:76: warning: This simp argument is unused:
  Finset.sum_apply

Hint: Omit it from the simp argument list.
  [apply] simp only [spatialGradient, spatialDerivative, assembledVelocity, finiteVelocitySum, hd,
    ContinuousLinearMap.sum_apply, WithLp.sum_apply, WithLp.toLp_apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

Fix: Use `sum_apply`, `WithLp.ofLp_sum`, `WithLp.ofLp_toLp`, and `Finset.sum_apply`.

## A6 — unconstrained implicit centre (resolved)

```text
../formalization/NSFormalization/Section3/T24/MultipleRegions.lean:251:13: error: don't know how to synthesize implicit argument `x₀`
  @scaledVelocity_slice_contDiff u ?m.97 d.T (d.ε j) d.packet.extension_smooth (eps_admissible d j).left t ht
context:
ν : ℝ
u f : VelocityField
p : PressureField
K : Set Space
M E : ℝ
d : RegionsData ν u p f K M E
j : Fin d.N
t : ℝ
ht : t < d.T
⊢ Space
../formalization/NSFormalization/Section3/T24/MultipleRegions.lean:251:7: error: failed to infer `have` declaration type
../formalization/NSFormalization/Section3/T24/MultipleRegions.lean:250:54: error: unsolved goals
ν : ℝ
u f : VelocityField
p : PressureField
K : Set Space
M E : ℝ
d : RegionsData ν u p f K M E
j : Fin d.N
t : ℝ
ht : t < d.T
⊢ eLpNorm (torusLift fun x => spatialGradient (d.component j).velocity t x) 2 periodicTorusMeasure ^ 2 =
    ENNReal.ofReal
      (NavierStokesR3.CompactEnergy.dissipation
        (Source.parabolicVelocity (d.ε j)⁻¹ (d.T - d.ε j ^ 2) (d.placement j).x₀ (zeroPastField u)) t)
```

Fix: Supply `(x₀ := (d.placement j).x₀)` to the standalone smoothness fact.

## A7 — scaled/parabolic field bridge (resolved)

```text
../formalization/NSFormalization/Section3/T24/MultipleRegions.lean:264:12: error: Type mismatch: After simplification, term
  Section4.I03.eLpNorm_spatialGradient_sq_slice hs hc
 has type
  @Eq ℝ≥0∞ (eLpNorm (fun x => spatialGradient (scaledVelocity u (d.placement j).x₀ d.T (d.ε j)) t x) 2 volume ^ 2)
    (ENNReal.ofReal (NavierStokesR3.CompactEnergy.dissipation (scaledVelocity u (d.placement j).x₀ d.T (d.ε j)) t))
but is expected to have type
  @Eq ℝ≥0∞
    (eLpNorm
        (fun x =>
          WithLp.toLp 2 fun i =>
            (fderiv ℝ (fun x => scaledVelocity u (d.placement j).x₀ d.T (d.ε j) (t, x)) x) (coordinateVector i))
        2 volume ^
      2)
    (ENNReal.ofReal
      (NavierStokesR3.CompactEnergy.dissipation
        (Source.parabolicVelocity (d.ε j)⁻¹ (d.T - d.ε j ^ 2) (d.placement j).x₀ (zeroPastField u)) t))
```

Fix: Rewrite `scaledVelocity_eq_parabolicVelocity` in the identity and target.

## A8 — gradient wrapper transparency after rewriting (resolved)

```text
../formalization/NSFormalization/Section3/T24/MultipleRegions.lean:266:2: error: Type mismatch: After simplification, term
  he
 has type
  @Eq ℝ≥0∞
    (eLpNorm
        (fun x =>
          spatialGradient (Source.parabolicVelocity (d.ε j)⁻¹ (d.T - d.ε j ^ 2) (d.placement j).x₀ (zeroPastField u)) t
            x)
        2 volume ^
      2)
    (ENNReal.ofReal
      (NavierStokesR3.CompactEnergy.dissipation
        (Source.parabolicVelocity (d.ε j)⁻¹ (d.T - d.ε j ^ 2) (d.placement j).x₀ (zeroPastField u)) t))
but is expected to have type
  @Eq ℝ≥0∞
    (eLpNorm
        (fun x =>
          WithLp.toLp 2 fun i =>
            (fderiv ℝ
                (fun x =>
                  Source.parabolicVelocity (d.ε j)⁻¹ (d.T - d.ε j ^ 2) (d.placement j).x₀ (zeroPastField u) (t, x))
                x)
              (coordinateVector i))
        2 volume ^
      2)
    (ENNReal.ofReal
      (NavierStokesR3.CompactEnergy.dissipation
        (Source.parabolicVelocity (d.ε j)⁻¹ (d.T - d.ε j ^ 2) (d.placement j).x₀ (zeroPastField u)) t))
```

Fix: Also unfold `spatialGradient` and `spatialDerivative` in the final `simpa only`.

## Final status

All four goals closed. No residual statement or error remains.
All 15 module declarations are audited by `axioms_ub5_ub6.lean`.
The four field probes use `exact` without any new hypotheses.
