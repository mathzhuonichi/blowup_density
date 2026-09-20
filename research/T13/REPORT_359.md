# Lane 359 — T13 `localization` assembly + `LocalizationAPI` (Opus prover; transcribed by the lead from the agent's final message — report-file guard)

Commit `06f696482a04763b75d4fcf0a99752975afd5c66` on `erenup/359-T13-localization-assembly` (stacked on lane 354). No `sorry`/`admit`/`axiom`/`native_decide`, no named input, no `maxHeartbeats` override; 11 declarations, all `[propext, Classical.choice, Quot.sound]`.

## 1. What was proved (`Section3/T13/Assembly.lean`)
- `localization` — verbatim the field of `research/T13/probes/api_on_canonical.lean`: `∀ s, 0 < s → s < 1 → ∀ c r, 0 < r → closure (ball c r) ⊆ interior fundamentalCube → ∃ C, 0 < C ∧ ∀ f, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) → periodicSobolevENorm s (periodize f) ≤ ofReal C * (eLpNorm f 2 volume + dotHomogeneousENorm s f)`, with the explicit constant `C := (1 + (4 · tailGeomConst s c r / cFrac s) ^ (1/2)).toReal` (finite: `tailGeomConst < ⊤`, `0 < cFrac`).
- `localizationAPI : LocalizationAPI` — the six-field record (restated token-for-token in the module): `⟨constant_pos_finite, wholeSpace_identity, torus_identity, localization, endpoint_zero, endpoint_one⟩`.
- Supporting: `torus_cube_L2` (COMPARISON item 8: `eLpNorm (torusLift v) 2 periodicTorusMeasure = eLpNorm v 2 (volume.restrict fundamentalCube)` for continuous `v`), `contDiff_periodize_supported`, `isPeriodicSpatial_periodize`, `lintegral_torusLift_normSq`, `eLpNorm_two_sq`, `enn_le_of_sq_le`, `latticeVector_eq_lattice`, `periodize_eq_vendor`, `homogeneous_bound`.
Route (all in `ℝ≥0∞`): 353's `periodicSobolevENorm_le_l2_add_homogeneous` splits the norm; `L²` term: 363's Parseval-at-0 → `torus_cube_L2` → 344's `endpoint_zero_eq` gives `= eLpNorm f 2 volume`; homogeneous term: 345's `torus_identity` + 354's `iTorus_periodize_le` + 348's `wholeSpace_identity` give `cFrac·x² ≤ cFrac·a² + 4·tailGeomConst·b²`, cancel `cFrac`, monotone `ℝ≥0∞` square root (`enn_le_of_sq_le`, no `toReal`).

## 2. Files
`formalization/NSFormalization/Section3/T13/Assembly.lean`; `research/T13/probes/assembly_closes.lean` (`example : LocalizationAPI := localizationAPI`; `localization` instantiated at `s = 1/2` on the nonzero lane-344 `ContDiffBump` field); `research/T13/axioms_assembly.lean` (11); `research/T13/ATTEMPTS_ASSEMBLY.md`; `research/T13/COMPARISON.md` ("all six fields closed").

## 3. Gap
None: all six `LocalizationAPI` fields are proved, the record is inhabited and non-vacuous; `torus_cube_L2` closes COMPARISON item 8 / open question 4 for the order-zero physical norm.

## 4. Commands and results
`lake build NSFormalization.Section3.T13.Assembly` → success (9997 jobs), 0 errors, 0 warnings on the module; `lake env lean` on module / probe / axioms → exit 0, 11 × standard axioms; `make check` → OK. Fixed snags recorded in ATTEMPTS: explicit `∂μ` in `rpow_natCast` targets; trailing `rfl` after `rw [← Paper1.integral_torusLift …]`; qualified `ENNReal.one_ne_top` / `T15.periodicSobolevENorm_zero_eq`; unused binders renamed.
