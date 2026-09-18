# Lane 375 — T17 U4: the fixed-cylinder force profile (Opus prover; transcribed by the lead — report-file guard)

`erenup/375-T17-U4-force-profile`, now **merged with `origin/erenup/integration-section3`** (`def02c7c`, clean merge, no code conflicts) so lane 373's `Section3/T17/Transport.lean` and the registered `Contracts/V1/LocalPotential.lean` are on the base. Bare `(x₀, T)` (G3) and the global `hv : ContDiff ℝ ∞ v` premise (G1) as in lane 370. New commit hash recorded in the lane branch / merge log.

## 1. What was proved (`Section3/T17/ForceProfile.lean`, 13 declarations: 10 audited in `axioms_u4.lean` + 3 vocabulary defs, all `[propext, Classical.choice, Quot.sound]`, reviewer-verified)
Five `CorrectionAPI` force-profile field conclusions (`Spec.lean:805-823`), after extracting the T16 cutoff and placement-scale premises, with the authorized global `hv` premise: `force_profile_smooth`, `force_profile_support`, `forceProfileConst` (`def : ℕ → ℝ`), `forceProfileConst_nonneg`, `force_profile_uniform` (with `hε₀ : D.ε₀ ≤ 1`).

Sixth field **now closed in Spec form** (over the abstract-correction force `correctionForce ν v D ε`, lane 373's `Transport.correctionForce`):
`force_profile_identity {v U K} (ν) (hv) {x₀ r T δ D} (hpot : LocalPotentialAPI v U K x₀ r T δ D) : ∀ ε ∈ Ioc 0 D.ε₀, ∀ z ∈ fixedProfileCylinder D, correctionForce ν v D ε (correctionChartPoint x₀ T ε z) = (ε ^ 2)⁻¹ • rescaledForceProfile ν v x₀ T ε D z`.
The chart-force variant is kept: `physicalForce_eq_rescaledForceProfile : … Source.correctionForce ν v (physicalCorrection v x₀ T D.θ D.η ε) (correctionChartPoint x₀ T ε z) = (ε ^ 2)⁻¹ • rescaledForceProfile ν v x₀ T ε D z` (needs only `hv, hθ, hη`).

Supporting: the def bridge `rescaledForceProfile_eq_forceProfile` — a **proved pointwise identity to Paper1's `forceProfile`, not a `rfl` bridge**: the Spec writes the `(w·∇)v`-type term as `ε² • spatialDerivative v (physical point) (W z)` while Paper1 uses `ε • spatialDerivative V_ε t x (W(t,x))`, reconciled by the chain rule `spatialDerivative_rescaledReference` (`∂ₓV_ε = ε • ∂ₓv(physical)`) + `smul_add`/`abel` over `forceProfile_eq_operators`; also `rescaledReference_spatialDerivative_smul`, `inverseScale_correctionChartPoint`, and the new lift `force_eq_chart` (from Transport's `correctionForce_eq_source` + `source_correctionForce_congr` + lane 370's `correction_eq_physicalCorrection`). Vocabulary defs `rescaledReference`, `rescaledForceProfile` restated verbatim (place→bare); the abstract-force `correctionForce` is **reused** from Transport (not re-declared — the two would clash).

## 2. Files
`formalization/NSFormalization/Section3/T17/ForceProfile.lean` (now imports `Section3.T17.Transport`); `research/T17/probes/force_profile_closes.lean` (six Spec fields restated token-for-token, the identity in **Spec form** from a `LocalPotentialAPI` witness plus the chart-force variant, each closed by `exact`; non-vacuity: nonzero constant reference + T16 cutoffs discharge the five cutoff-only fields and the chart-force identity); `research/T17/axioms_u4.lean` (12 decls); `research/T17/ATTEMPTS_U4.md`; U4 status in `research/T17/T17_SPLIT.md`; reviewer probes `research/T17/probes/rev375_{vocabulary_axioms,wrong_power}.lean`.

## 3. Gap
The Spec-form `force_profile_identity` is now closed (G0 resolved by the merge that brought lane 373's `Transport.lean`). Its non-vacuity still needs a concrete `LocalPotentialAPI` inhabitant (T16 `localPotential` assembly), staged like every abstract-correction field for U12; the probe's non-vacuity therefore discharges the five cutoff-only fields and the chart-force identity, not the `LocalPotentialAPI`-dependent Spec-form identity. G1 (global `hv` premise — no `reference_smooth` field on the `CorrectionAPI`) and G3 (bare `x₀,T`) are authorized limitations carried over from lane 370.

## 4. Commands and results
- `lake build NSFormalization.Section3.T17.ForceProfile` → `Build completed successfully (9363 jobs)`; the only warning replayed in the closure is `Section3/T16/Assembly.lean:362 if_pos deprecated` (a dependency via Transport, **not** from `ForceProfile.lean`).
- `lake env lean` on `ForceProfile.lean`, `force_profile_closes.lean`, `rev375_vocabulary_axioms.lean` → each exit 0, no output / axiom lines only; `rev375_wrong_power.lean` → exit 1 (`error: Type mismatch`, ε⁻³ mutation rejected).
- `lake env lean ../research/T17/axioms_u4.lean` → all 12 declarations `[propext, Classical.choice, Quot.sound]`.
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` → exit 0, `"base_compatibility_checked": true` (the earlier `Removed stable specification: Contracts/V1/LocalPotential.lean` is resolved by the merge).
- `make check` → exit 0 (`test_contract_policy` 13 passed; `check_work_queue` consistent).
- forbidden-token grep (`sorry|admit|native_decide|axiom`) on the added `.lean` files → none.
