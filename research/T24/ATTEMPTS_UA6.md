# T24a Ua6 — `energy_finite` — attempts log (lane 407)

Target verbatim (`research/T24/Spec.lean:1076-1077`, with the packet field
`P.velocity` replaced by the raw `U`):

```lean
theorem energy_finite {U : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (henergy : energyENorm 1 U < ⊤) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      energyENorm 1 (affineVelocity U b) < ⊤
```

Module: `formalization/NSFormalization/Section3/T24/AffineEnergy.lean`.
Probe: `research/T24/probes/affine_energy_closes.lean`.
Axiom audit: `research/T24/axioms_ua6.lean`.

Raw packet clause consumed: **only** `energyENorm 1 U < ⊤`. No smoothness,
measurability, support or divergence clause of `U` is used.

## Where the norm came from

`energyENorm` is registered in `verification/Contracts/V1/Data.lean:444-476` and
canonical modules may not import `Contracts.*`. Searching first (`grep -rn
"def energyEssSup\|def energyGradient\|def energyENorm"` over
`formalization/NSFormalization`) shows **no** local whole-space restatement:
`Section3/T10/PeriodicData.lean:330-341` defines only the *torus* variants
`energyEssSupT/energyGradientT/energyENormT` (over `periodicTorusMeasure`), and
`Section4/I02/Energy.lean` / `Section4/I03/Energy.lean` state their bounds with
the `essSup …` / `∫⁻ …` expressions written out rather than through a name.
So §1 of the new module restates the three definitions verbatim, reusing the
already-canonical `Section4.I02.spatialGradient`; the probe checks all four
`rfl` bridges.

Also searched, per the brief, before proving subadditivity:
`energyENorm_add`, `energyEssSup_add`, `energyGradient_add` in `Section4/` and
`Source/` — **absent there**. They exist only in
`verification/Bindings/ScalingEnergy.lean:57,105,167`, which is downstream of
`formalization/` (`verification` depends on `formalization`, not conversely), so
they cannot be imported by a canonical module.

## What did not work

1. **Minkowski (`eLpNorm_add_le`) — the route named in the brief.**
   `MeasureTheory.eLpNorm_add_le (hf : AEStronglyMeasurable f μ)
   (hg : AEStronglyMeasurable g μ) (hp1 : 1 ≤ p)` needs *both* summands
   measurable. `Bindings.ScalingEnergy.energyEssSup_add_le` therefore carries
   four measurability/differentiability hypotheses on each field. Ua6's raw
   clause `energyENorm 1 U < ⊤` carries none of them, and adding
   `velocity_smooth` to the statement would be a second packet clause, wider
   than the ledger entry (`T24_SPLIT.md:192`, "raw `energyENorm 1 U < ⊤`").
   Abandoned in favour of route 2.

2. **`fderiv_add` unconditionally.** `spatialGradient (U+b) t x` is built from
   `fderiv ℝ (fun y ↦ U (t,y) + b (t,y)) x`, and `fderiv_add` needs *both*
   summands differentiable at `x`. Without a smoothness clause for `U` there is
   no such hypothesis. Fixed by a case split
   (`enorm_spatialGradient_affineVelocity_le`): if the `U` slice is not
   differentiable at `x`, neither is the sum (subtracting the smooth `b` would
   make it so), hence `fderiv = 0` and `spatialGradient (U+b) t x = 0`, so the
   bound `‖∇(U+b)‖ₑ ≤ ‖∇U‖ₑ + ‖∇b‖ₑ` holds in both branches.

3. **`(x+y)² ≤ 2x² + 2y²` in `ℝ≥0∞`.** `add_sq` expands to `x² + 2xy + y²`, and
   `2xy ≤ x² + y²` (`two_mul_le_add_sq`) needs a `LinearOrderedRing`; `ℝ≥0∞` has
   no subtraction. Replaced by the crude `(x+y)² ≤ 4x² + 4y²`, proved by
   `rcases le_total x y` and `x + y ≤ 2·max x y`. Only finiteness is claimed
   downstream, so the constant is irrelevant.

4. **`∫⁻ (f + g) = ∫⁻ f + ∫⁻ g` without measurability.** False in general
   (the lower integral is superadditive). Used `lintegral_add_right (f)
   (hg : Measurable g)`, which needs only the *right* summand measurable; the
   right summand is always the `b` term (smooth → continuous → measurable) or a
   constant. This is what makes the whole proof work with no hypothesis on `U`.

5. **Restricting a slice integral to the carrier via `Set.indicator`.**
   `Set.indicator_of_notMem` / `Set.indicator_of_mem` did not resolve under this
   Mathlib pin (`Mathlib/Algebra/Group/Indicator.lean` no longer carries them at
   these names). Replaced by `setLIntegral_eq_of_support_subset`
   (`Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:532`), which needs only
   a support inclusion — no `MeasurableSet` argument at all.

6. **Name drift costing two compile rounds** (all "unknown identifier" or type
   mismatch, no mathematical content):
   - `pow_le_pow_left` → `pow_le_pow_left₀`;
   - `mul_le_mul_left'` → does not exist; used `mul_le_mul' (le_refl 4) h`;
   - `eLpNorm_eq_lintegral_rpow_enorm` → deprecated, use
     `eLpNorm_eq_lintegral_rpow_enorm_toReal`;
   - `fderiv_const` (a `Function.const` statement) → `fderiv_const_apply`;
   - **`add_le_add_left` adds on the *right* under this pin**
     (`add_le_add_left (h : b ≤ c) (a) : b + a ≤ c + a`), which silently
     produced a metavariable goal and burned 200000 heartbeats in `whnf`
     before failing. Diagnosed by re-running the one declaration with
     `set_option maxHeartbeats 2000000`, which turned the "timeout" into an
     ordinary type mismatch in 31 s. Use `add_le_add h₁ h₂` instead; the final
     module needs **no** `set_option maxHeartbeats`.

## What worked (final route)

Both halves of `E_1` are handled by the same measurability-free scheme.

- `add_rpow_two_le : (x+y)^(2:ℝ) ≤ 4x^(2:ℝ) + 4y^(2:ℝ)` in `ℝ≥0∞`.
- `rpow_two_eLpNorm_two : (eLpNorm f 2 volume)^(2:ℝ) = ∫⁻ x, ‖f x‖ₑ^(2:ℝ)` —
  pure unfolding of `eLpNorm`, no measurability.
- `rpow_two_eLpNorm_add_le` — from a pointwise `‖H‖ₑ ≤ ‖F‖ₑ + ‖G‖ₑ` and
  `Measurable (fun x ↦ ‖G x‖ₑ^(2:ℝ))` only:
  `(eLpNorm H 2)² ≤ 4(eLpNorm F 2)² + 4(eLpNorm G 2)²`.
- `rpow_two_eLpNorm_le_of_bound` — a field bounded by `√A` and vanishing off a
  set `K` has `(eLpNorm f 2)² ≤ ofReal A · |K|`
  (`setLIntegral_eq_of_support_subset` + `setLIntegral_const`).
- Uniform bounds for `b`: `Continuous.bounded_above_of_compact_support` applied
  to `b` itself and to `fun z : SpaceTime ↦ spatialDerivative b z.1 z.2`. The
  latter is continuous by `ContDiff.fderiv` (base point `(t,x)`, fibre variable
  `y`, `Function.uncurry` of the slice family is `b ∘ (fun p ↦ (p.1.1, p.2))`)
  and compactly supported because a slice of `b` is locally zero off
  `tsupport b`, so its `fderiv` vanishes there
  (`Filter.EventuallyEq.fderiv_eq` on the open complement). The Frobenius
  gradient is then bounded by `3 Cg²` through
  `I02.norm_spatialGradient_sq` and `‖coordinateVector i‖ = 1`.
- `L^∞_t L²_x` half: `essSup_le_of_ae_le` against the constant
  `(4 S² + 4 Db)^{1/2}`, with `S := energyEssSup 1 U` supplied a.e. by
  `ENNReal.ae_le_essSup`; finiteness by `ENNReal.rpow_lt_top_of_nonneg`.
- `L²_t Ḣ¹_x` half: `lintegral_mono` to `4·(‖∇U(t)‖₂)² + 4·Dg`, then
  `lintegral_add_right _ measurable_const` + `lintegral_const_mul'` +
  `setLIntegral_const`, giving
  `4·(∫⁻ (‖∇U(t)‖₂)²) + 4·Dg·|Ioo 0 1| < ⊤`; the inner `∫⁻` is finite because
  `energyGradient 1 U = (∫⁻ …)^{1/2} < ⊤` and `⊤^{1/2} = ⊤`.

## Open gap (not Ua6)

`Contracts.V1.PacketAPI` has **no** `energyENorm 1 velocity < ⊤` field. It
carries `square_integrable` (`Packet.lean:247`), `energy_isLUB` (`:255`),
`dissipation_integrable` (`:260`) and `dissipation_eq` (`:266`). So the probe
threads `energyENorm 1 (Bindings.packet ν hν).velocity < ⊤` as a hypothesis
rather than deriving it. Assembling it is a separate unit (for Ua9):

- `L^∞_t L²_x`: `I02.eLpNorm_two_eq_ofReal_sqrt` turns each slice `eLpNorm` into
  `ofReal (√(l2Sq U t))` under `square_integrable`; `energy_isLUB` bounds that
  by `ofReal energyBound`.
- `L²_t Ḣ¹_x`: `I03.eLpNorm_spatialGradient_sq_slice` identifies the squared
  gradient `eLpNorm` with `ofReal (dissipation U t)` (slice smoothness from
  `velocity_smooth` on the open `Ioo 0 1 ×ˢ univ ⊆ preSingularDomain`, slice
  compact support from `velocity_support` + `carrier_compact`), and then
  `dissipation_integrable` + `ofReal_integral_eq_lintegral_ofReal`.
