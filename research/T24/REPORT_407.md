# REPORT_407 — T24 Ua6 `energy_finite` (Opus; transcribed by lead from the agent message, report-file guard)

Lane 407 is done and committed on `erenup/407-T24-Ua6-energy-finite` (commit `323648ba`). No `sorry`/`admit`/`axiom`/`native_decide`, no `set_option maxHeartbeats`, no edits to existing Lean modules, nothing pushed.

## 1. What was proved

T24a unit **Ua6**, `energy_finite` — the `03-torus.tex:686-687` clause "finite energy and dissipation, `‖Ũ‖_{E_1} < ∞`", over the raw packet velocity. Exact statement as it stands in the file:

```lean
theorem energy_finite {U : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (henergy : energyENorm 1 U < ⊤) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      energyENorm 1 (affineVelocity U b) < ⊤
```

The conclusion is token-identical to `research/T24/Spec.lean:1076-1077` with `P.velocity` replaced by the raw `U`. **The only packet clause used is `energyENorm 1 U < ⊤`** — no smoothness, measurability, support or divergence clause of `U` appears. `AffineAdmissible` and `affineVelocity` are imported from lane 392's `AffineBasics`, not restated.

Route actually landed (it differs from the brief's route 2, and the difference is the mathematical content of the lane):

- **Minkowski is unusable here.** `eLpNorm_add_le` requires `AEStronglyMeasurable` slices of *both* summands, which `energyENorm 1 U < ⊤` does not give. The existing subadditivity lemmas (`energyEssSup_add_le`, `energyGradient_add_le`, `energyENorm_add_le`) exist only in `/data_8T/ping/blowup_density/.claude/worktrees/407-T24-Ua6-energy-finite/verification/Bindings/ScalingEnergy.lean:57,105,167` — downstream of `formalization/`, so a canonical module cannot import them, and each carries four measurability/differentiability hypotheses anyway. Instead both halves go through `(x+y)² ≤ 4x²+4y²` in `ℝ≥0∞` plus `lintegral_add_right`, which needs only the **right** summand measurable; the right summand is always `b` (smooth) or a constant.
- **`fderiv_add` is unusable too** (needs both slices differentiable). A case split gives `‖∇(U+b)‖ₑ ≤ ‖∇U‖ₑ + ‖∇b‖ₑ` unconditionally: if the `U` slice is not differentiable at `x`, neither is the sum (subtract the smooth `b`), so `spatialGradient (U+b) t x` is the `fderiv` junk value `0`.
- `b`'s two uniform bounds: `Continuous.bounded_above_of_compact_support` on `b`, and on `fun z : SpaceTime ↦ spatialDerivative b z.1 z.2` — continuous via `ContDiff.fderiv` (its `Function.uncurry` is `b ∘ (fun p ↦ (p.1.1, p.2))`), compactly supported because a slice's `fderiv` vanishes off `tsupport b`. Slice integrals are confined to the compact `Prod.snd '' tsupport b` by `setLIntegral_eq_of_support_subset` (no `MeasurableSet` needed).

## 2. What exists in Lean now

- `/data_8T/ping/blowup_density/.claude/worktrees/407-T24-Ua6-energy-finite/formalization/NSFormalization/Section3/T24/AffineEnergy.lean` (423 lines, 17 declarations, namespace `NSFormalization.Section3.T24`): §1 verbatim restatement of `energyEssSup`/`energyGradient`/`energyENorm`; §2 `add_rpow_two_le`, `rpow_two_eLpNorm_two`, `rpow_two_eLpNorm_add_le`, `rpow_two_eLpNorm_le_of_bound`; §3 `enorm_spatialGradient_affineVelocity_le`; §4 `continuous_spatialDerivative_uncurry`, `spatialDerivative_eq_zero_of_notMem_tsupport`, `exists_bound_spatialDerivative`, `enorm_spatialGradient_rpow_two_le`, `rpow_two_eLpNorm_slice_le`, `rpow_two_eLpNorm_gradient_slice_le`; §5 the two halves `energyEssSup_affineVelocity_lt_top`, `energyGradient_affineVelocity_lt_top`; §6 `energy_finite`.
- `/data_8T/ping/blowup_density/.claude/worktrees/407-T24-Ua6-energy-finite/research/T24/probes/affine_energy_closes.lean` — four `rfl` bridges to `Contracts.V1.Data.{energyEssSup, energyGradient, energyENorm, spatialGradient}`; the `Spec.lean:1076-1077` field discharged on `Bindings.packet ν hν`; the same for an arbitrary raw `U`; non-vacuity (`b = 0` is admissible, and at `b = 0` the conclusion reduces to the hypothesis).
- `/data_8T/ping/blowup_density/.claude/worktrees/407-T24-Ua6-energy-finite/research/T24/axioms_ua6.lean`, `.../research/T24/ATTEMPTS_UA6.md`, Ua6 "DONE (lane 407)" block in `.../research/T24/T24_SPLIT.md`, one entry at the top of `.../logs/LESSONS.md`.

**Why a new local restatement of `E_T`:** I grepped `formalization/NSFormalization` for `def energyEssSup|energyGradient|energyENorm` — there is none for whole space (`Section3/T10/PeriodicData.lean:330-341` defines only the *torus* `energyEssSupT/energyGradientT/energyENormT`; `Section4/I02,I03/Energy.lean` write the `essSup …`/`∫⁻ …` expressions out). So §1 restates `verification/Contracts/V1/Data.lean:444-476` verbatim on the already-canonical `Section4.I02.spatialGradient`, and the probe checks the `rfl` bridges. A reviewer may prefer this block to move to a shared canonical module later; it is currently the only copy.

## 3. Gap

One, and it is outside Ua6: **`Contracts.V1.PacketAPI` has no `energyENorm 1 velocity < ⊤` field.** It carries `square_integrable` (`Packet.lean:247`), `energy_isLUB` (`:255`), `dissipation_integrable` (`:260`), `dissipation_eq` (`:266`). So the probe's packet example threads `energyENorm 1 (Bindings.packet ν hν).velocity < ⊤` as a hypothesis rather than deriving it. This matches the design: `T24_SPLIT.md:34` lists `energyENorm 1 velocity < ⊤` among the raw clauses the canonical T24a module takes as explicit hypotheses, and the §2 ledger row for Ua6 (`:192`) names exactly "raw `energyENorm 1 U < ⊤`" as the consumed input. Assembling it from the three packet fields is a separate unit (for Ua9); the route is recorded in `ATTEMPTS_UA6.md`: `I02.eLpNorm_two_eq_ofReal_sqrt` + `energy_isLUB` for the `L^∞_tL²_x` half, `I03.eLpNorm_spatialGradient_sq_slice` + `dissipation_integrable` + `ofReal_integral_eq_lintegral_ofReal` for the other. I did not do it — it would have widened the lane.

Failed approaches, with why (all also in `ATTEMPTS_UA6.md`):
1. Minkowski / the `Bindings.ScalingEnergy` lemmas — needs measurability of `U`'s slices; and the import direction forbids reuse.
2. `fderiv_add` unconditionally — needs both slices differentiable.
3. `(x+y)² ≤ 2x²+2y²` — `two_mul_le_add_sq` needs a `LinearOrderedRing`; `ℝ≥0∞` has no subtraction. Used constant `4` instead (only finiteness is claimed).
4. `∫⁻(f+g) = ∫⁻f + ∫⁻g` without measurability — false; used `lintegral_add_right`.
5. `Set.indicator_of_mem`/`indicator_of_notMem` to restrict a slice integral — those names do not resolve under this Mathlib pin; used `setLIntegral_eq_of_support_subset`.
6. Name drift, two compile rounds: `pow_le_pow_left` → `pow_le_pow_left₀`; `mul_le_mul_left'` does not exist (used `mul_le_mul' (le_refl 4) h`); `eLpNorm_eq_lintegral_rpow_enorm` deprecated → `..._toReal`; `fderiv_const` → `fderiv_const_apply`. The expensive one: **under this pin `add_le_add_left` adds on the right** (`b ≤ c → b + a ≤ c + a`), so writing it produced a metavariable goal that burned the full 200000 heartbeats in `whnf` and reported as a "timeout". Re-running the single declaration with a temporary `set_option maxHeartbeats 2000000` turned it into an ordinary type mismatch in 31 s. Replaced by `add_le_add h₁ h₂`; the committed module needs no heartbeat option.

## 4. Commands run and results

All from the worktree, after `. scripts/lean-env.sh`, `lake` run from `verification/` with `LEAN_NUM_THREADS=6`.

| command | result |
|---|---|
| `lake build NSFormalization.Section3.T24.AffineEnergy` | `Build completed successfully (9326 jobs).` — 0 errors; module built in 2.9 s (only pre-existing upstream `Source/*` deprecation warnings replayed) |
| `lake env lean ../formalization/NSFormalization/Section3/T24/AffineEnergy.lean` | 0 lines of output |
| `lake env lean ../research/T24/probes/affine_energy_closes.lean` | 0 lines of output |
| `lake env lean ../research/T24/axioms_ua6.lean` | 14 declarations, each `depends on axioms: [propext, Classical.choice, Quot.sound]` (14/14 matches) |
| `make check` | `Ran 13 tests ... OK`; `45 work items: ownership, contract registration and task cards consistent.` |
| `git commit` | `323648ba [407-T24] Ua6 energy_finite: ...` on `erenup/407-T24-Ua6-energy-finite`; working tree clean |

Intermediate failures observed before the fixes above: round 1 reported 9 errors (`add_le_add_right` orientation, deprecated `eLpNorm_eq_lintegral_rpow_enorm`, `Function.uncurry` `simpa`, `fderiv_const`, `pow_le_pow_left`, `mul_le_mul_left'`); round 2 reported 2 real errors plus four `(deterministic) timeout at 'whnf'/'tactic execution', maximum number of heartbeats (200000) has been reached` at the `add_le_add_left` site, which the 2000000-heartbeat isolation run re-reported as `Type mismatch: add_le_add_left (mul_le_mul' (le_refl 4) (rpow_two_eLpNorm_gradient_slice_le hCg t)) ?m.498 has type 4 * eLpNorm (fun x => spatialGradient b t x) 2 volume ^ 2 + ?m.498 ≤ ...`.


> Lead note after review 407: the hypothesis-count wording at line 20 should read "the only packet clause used is `energyENorm 1 U < ⊤`; the geometric parameters `c r τ₀ τ₁` enter only through `AffineAdmissible`" (the reviewer flagged the count as imprecise). The three local norm definitions are now audited in `axioms_ua6.lean`.
