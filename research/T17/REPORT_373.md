# Lane 373 — T17 U2: concrete correction data + force-operator transport (Opus prover; transcribed by the lead from the agent's final message — report-file guard)

Commit `0ccdc187925bb3c34fb616ea66494c77af4a8827` on `erenup/373-T17-U2-transport`. No `sorry`/`admit`/`axiom`/`native_decide`, no named `Prop` inputs; every declaration `[propext, Classical.choice, Quot.sound]`.

## 1. What was proved (`Section3/T17/Transport.lean`)
- `def correctionData (v x₀ T θ η O θR ε₀) : CutoffData := localPotentialData v x₀ T θ η O θR ε₀` (T16's witness; plain `x₀ T` — the `place` form is a projection corollary once a canonical `PlacementData` exists).
- `theorem correctionData_correction … (ε) : (correctionData …).correction ε = latticeLift (physicalCorrection v x₀ T θ η ε)` — by `rfl` (the structural fact U5–U11 rewrite through).
- `def correctionForce (ν v D ε) : SpaceTimeField` — the T17 `eq:H` spelling copied verbatim from `research/T17/Spec.lean:726-733` (`∂ₜw − ν•Δw + Dw(v) + Dv(w) + advection w`).
- `theorem force_eq` (U2 goal) under the honest T16 hypotheses (`hv : IsPeriodicOn univ v`, `hvsm : ContDiffOn ℝ ∞ v (Ioo 0 (T+δ) ×ˢ ball x₀ r)`, θ/η smooth + compact support with `tsupport θ ⊆ ball 0 θR`, `tsupport η ⊆ Ioo (−2) 2`, `r < 1/2`, `0 < ε`, `ε·θR < r`, `2ε² < min T δ`): `correctionForce ν v (correctionData …) ε = latticeLift (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε))`.
- `theorem correctionForce_periodic : IsPeriodicOn univ (correctionForce ν v (correctionData …) ε)` (same hypotheses).
- Supporting: `correctionForce_eq_source` (T17 spelling = `Source.correctionForce`, `abel`), translation-equivariance `temporalDerivative_translate` / `spatialDerivative_translate` / `spatialLaplacian_translate` / `advection_translate`, germ-locality `source_correctionForce_congr`, `source_force_translate`, `source_correctionForce_eq_zero` / `_support`, `contDiff_spatialDerivative_apply`.
Route: pointwise, by cases on `x ∈ periodicSet (ball x₀ r)`: inside a periodic copy the lift is a single translate near `x` (no mixing of copies in the nonlinear term), each operator is translation-equivariant, and `v` (and its derivative, on the cylinder) is periodic; outside the periodic support both sides vanish (`physical_support`).

## 2. Files
`formalization/NSFormalization/Section3/T17/Transport.lean`; `research/T17/probes/transport_closes.lean` (nonzero constant divergence-free periodic reference; `correctionData_correction` by `rfl`); `research/T17/axioms_u2.lean`; `research/T17/ATTEMPTS_U2.md`; U2 status in `research/T17/T17_SPLIT.md`.

## 3. Gap
None for U2. Assembly notes (U12): `correctionData` uses plain `x₀ T`; `force_eq`/`correctionForce_periodic` are over the concrete `correctionData` — the abstract-`D` fields bind through `correctionData_correction` (they are false for an arbitrary `LocalPotentialAPI` witness, `T17_SPLIT.md` risk 5).

## 4. Commands and results
`lake build NSFormalization.Section3.T17.Transport` → success (9361 jobs); `lake env lean` on module / axioms (8 declarations standard) / probe → clean; forbidden-token grep → none; `make check` → OK. Failed approaches in ATTEMPTS_U2.md (finite-sum route mixes copies in the advection term; `v` only `ContDiffOn` the cylinder — case split on the time window; `translate` name clash → fully qualify; typed `have`s for `clm_apply`; `rw [show … from rfl]` for the `∘` form).
