# Lane 375 — T17 U4: the fixed-cylinder force profile (Opus prover; transcribed by the lead from the agent's final message — report-file guard)

Commit `5fb0be0c6e432ef9957a87e8156ef42aa12f5c7a` on `erenup/375-T17-U4-force-profile` (stacked on lane 370). Bare `(x₀, T)` (G3) and the global `hv : ContDiff ℝ ∞ v` premise (G1) as in lane 370.

## 1. What was proved (`Section3/T17/ForceProfile.lean`, 10 declarations, all `[propext, Classical.choice, Quot.sound]`)
Five `CorrectionAPI` force-profile fields verbatim (`Spec.lean:805-823`): `force_profile_smooth`, `force_profile_support`, `forceProfileConst` (`def : ℕ → ℝ`), `forceProfileConst_nonneg`, `force_profile_uniform` (with `hε₀ : D.ε₀ ≤ 1`). Sixth field in chart-force form: `physicalForce_eq_rescaledForceProfile : ∀ ε ∈ Ioc 0 D.ε₀, ∀ z ∈ fixedProfileCylinder D, Source.correctionForce ν v (physicalCorrection v x₀ T D.θ D.η ε) (correctionChartPoint x₀ T ε z) = (ε ^ 2)⁻¹ • rescaledForceProfile ν v x₀ T ε D z`.
Supporting: `rescaledForceProfile_eq_forceProfile` (def bridge to Paper1's `forceProfile` — **not `rfl`**: the Spec writes the `(w·∇)v`-type term as `ε² • spatialDerivative v (physical point) (W z)` while Paper1 uses `ε • spatialDerivative V_ε t x (W(t,x))`; reconciled by the chain rule `spatialDerivative_rescaledReference` (`∂ₓV_ε = ε • ∂ₓv(physical)`) + `smul_add`/`abel`), `rescaledReference_spatialDerivative_smul`, `inverseScale_correctionChartPoint`; verbatim restatements `rescaledReference`, `rescaledForceProfile`, `correctionForce`.

## 2. Files
`formalization/NSFormalization/Section3/T17/ForceProfile.lean`; `research/T17/probes/force_profile_closes.lean` (six Spec fields restated token-for-token, identity in chart-force form, each closed by `exact`; non-vacuity: nonzero constant reference + T16 cutoffs); `research/T17/axioms_u4.lean`; `research/T17/ATTEMPTS_U4.md`; U4 status in `research/T17/T17_SPLIT.md`.

## 3. Gap (exact residual for U12)
`force_profile_identity` over the Spec's `correctionForce ν v D ε` (abstract `D.correction ε`) needs, given a `LocalPotentialAPI v U K x₀ r T δ D` witness:
```
force_eq_chart : ∀ ε ∈ Ioc 0 D.ε₀, ∀ z ∈ fixedProfileCylinder D,
  correctionForce ν v D ε (correctionChartPoint x₀ T ε z)
    = Source.correctionForce ν v (physicalCorrection v x₀ T D.θ D.η ε) (correctionChartPoint x₀ T ε z)
```
then `force_profile_identity = force_eq_chart ▸ physicalForce_eq_rescaledForceProfile`. `force_eq_chart` = operator reorder (`add_comm` of the two middle summands) + field agreement on `univ ×ˢ ball x₀ r` (lane 370's `correction_eq_physicalCorrection` + operator locality) — exactly lane 373's `force_eq` (`Section3/T17/Transport.lean`, not on this base) restricted to the chart. G1/G3 carried over.

## 4. Commands and results
`lake build NSFormalization.Section3.T17.ForceProfile` → success (9359 jobs), 0 errors/0 warnings; `lake env lean` on module → clean; axioms → 10 × standard; probe → exit 0; `make check` → OK; forbidden-token grep → none.
