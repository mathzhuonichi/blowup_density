# REPORT_438 — T17 U11 force Sobolev bound (Opus; transcribed by lead from the agent message, report-file guard)

Lane 438 is complete and committed. Four-part report:

---

## 1. What was proved

All four canonical `CorrectionAPI` fields of unit U11 (`eq:HHs`, `paper/sections/03-torus.tex:238-240`), at the concrete `correctionData` of unit U2, on the **whole** range `0 ≤ s ≤ 1` — no case left open.

Common premise block (identical to lanes 385/425, plus lane 385's `hε₀`):

```
(ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
(hvper : IsPeriodicOn univ v) {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) (θR ε₀ : ℝ)
(hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
(hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
(hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
(hr2 : r < 1 / 2) (hε₀ : ε₀ ≤ 1)
(hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
(hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r)
```

**The constant** (`sobolevConst`, `Sobolev.lean:283`) — a `def`, explicit in Paper1's two endpoint profile constants, fixed before `ε`:

```
def sobolevConst (ν) (hv) (x₀) (T) (hθ) (hη) (hθc) (hηc) : ℝ → ℝ :=
  fun s ↦ 1 + ∑ i : Fin 3,
    (sobolevC0 ν hv x₀ T hθ hη hθc hηc i).toReal ^ (1 - s) *
      (2 * Real.pi * (sobolevC1 ν hv x₀ T hθ hη hθc hηc i).toReal) ^ s
```

where `sobolevC0/sobolevC1 … i` are the `Classical.choose` of Paper1's `correction_scalar_whole_endpoint_rates` (house style of lane 385's `forceDerivConst`).

**`sobolevConst_pos`** (`:299`): `∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < sobolevConst ν hv x₀ T hθ hη hθc hηc s`.

**`forceSobolev_memLp`** (`:547`):
```
∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
  MemForceSobolevT 1 s (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε)
```

**`force_sobolev_bound`** (`:570`):
```
∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
  forceSobolevENormT 1 s (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) ≤
    ENNReal.ofReal (sobolevConst ν hv x₀ T hθ hη hθc hηc s *
      (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s)))
```

Types are literally the canonical fields: the probe's three `example`s project `A.sobolevConst_pos`, `A.forceSobolev_memLp`, `A.force_sobolev_bound` out of a hypothetical `CorrectionAPI` into exactly these shapes (two-sided conformance).

**Route actually used — not the one in the brief.** T13's `localization` *is* proved and its ball hypothesis is derivable from `ball_in_chart` + `chartBall_in_cube`, but its RHS is `eLpNorm f 2 volume + dotHomogeneousENorm s f`, and `dotHomogeneousENorm` evaluates (via `D01.isHomogeneousSliceDatum_compact`) to an integral against `Source.angularFourier` (`e^{-i x·ξ}`), while Paper1's ε-rates are stated with Mathlib's `𝓕` (`e^{-2πi x·ξ}`). The `(2π)^{3+2s}` whole-space dilation bridge does not exist in the tree. The lane instead goes through Paper1's periodic Fourier series: `periodized_scalar_L1Hs_le_endpoint_product` fed by `correction_scalar_whole_endpoint_rates`, after recentring the single Euclidean copy at the origin. The proof actually yields `≤ C ε^{3/2-s}`, majorized into the manuscript's `C_s(ε^{3/2}+ε^{3/2-s})`.

## 2. What exists in Lean now

- `/data_8T/ping/blowup_density/.claude/worktrees/438-T17-U11-sobolev/formalization/NSFormalization/Section3/T17/Sobolev.lean` — 592 lines, new module, namespace `NSFormalization.Section3.T17`, 21 declarations. **No existing module edited.** Reusable pieces beyond the four fields:
  - `norm_scalar_datum_real` / `norm_datum_eq_sqrt` / `norm_datum_eq_vector` / `periodicSobolevENorm_slice_eq` — T10's order-`s` datum norm **is** Paper1's `periodicVectorSobolevNorm` at every *real* order (`T10.norm_scalar_datum_nat` is natural-order only because it rewrites one step further, into `periodicSobolevSq_nat`).
  - `periodicSobolevENorm_translate` — spatial translation invariance, via T11's `isPeriodicDatum_translate` + `translatePeriodicDatum_norm`.
  - `norm_datum_mono`, `force_coefficient_path_real` — the real-order analogue of `T10.force_coefficient_path` for `s ≤ 1`; continuity at fractional `s` by squeezing against the order-1 path (`Paper1.periodicSobolevSq_mono_smooth`).
  - `shiftedForce` + `shiftedForce_supportedInCube` + `periodize_shiftedForce` — reconciles the repo's two fundamental-domain normalizations (`[0,1]³` vs origin-centred `SupportedInCube r`, `r < 1/2`) without adding any hypothesis on `‖x₀‖`.
  - `component_L1Hs_bound`, `forceSobolevENormT_le_of_translate`, `forceSobolev_memLp_and_bound`.
- `/data_8T/ping/blowup_density/.claude/worktrees/438-T17-U11-sobolev/research/T17/probes/sobolev_closes.lean` — 213 lines; three `field_*` theorems closed by `exact`, three record-projection conformance `example`s, `fields_at_placement` at `place.x₀`/`place.T`, and `nonvacuous_sobolev` instantiating both quantitative fields on T16's `exists_originCutoff`/`exists_timeCutoff`/`exists_threshold` at a nonzero, divergence-free, periodic constant reference **centred in the cube** (`x₀ = 0`, `T = 1`, `r = 1/4`).
- `/data_8T/ping/blowup_density/.claude/worktrees/438-T17-U11-sobolev/research/T17/axioms_u11.lean` — 21 `#print axioms`.
- `/data_8T/ping/blowup_density/.claude/worktrees/438-T17-U11-sobolev/research/T17/ATTEMPTS_U11.md` — positive and negative record.
- U11 status paragraph inserted in `/data_8T/ping/blowup_density/.claude/worktrees/438-T17-U11-sobolev/research/T17/T17_SPLIT.md:240-260`; one line prepended to `/data_8T/ping/blowup_density/.claude/worktrees/438-T17-U11-sobolev/logs/LESSONS.md`.
- Commit `0cc741f7` on `erenup/438-T17-U11-sobolev`; working tree clean; nothing pushed, merged or rebased.

Per my harness instructions I could not create `research/T17/REPORT_438.md`; this message is the report, per the brief's fallback.

## 3. Gaps

**No residual on the deliverable — all four fields are closed for every `s ∈ [0,1]`.** Three things the lead should know:

1. **`eq:HHs` is not yet proved *through* `lem:localization`.** The brief's route needs a whole-space bridge between `Source.angularFourier` (`e^{-i x·ξ}`, used by `D01.homogeneousFourierENorm`, hence by `dotHomogeneousENorm`) and Mathlib's `𝓕` (`e^{-2πi x·ξ}`, used by `Source.fourierSobolevSq` and by all Paper1 ε-rates) — a `(2π)^{3+2s}` change of variables inside an `ℝ≥0∞` lintegral over `Space`. `grep -rn "angularFourier" formalization/` finds no such bridge; only the two integer-endpoint scalar facts `Paper1.PeriodicScalarForceEndpoints.angularSobolevSq_{zero,one}_eq_physical`. If the owner wants the manuscript's proof path mirrored exactly, that bridge is a lane of its own. The theorem statements delivered here are unaffected.
2. **Two extra premises relative to the raw Spec field**, both already precedented: `hv : ContDiff ℝ ∞ v` is the open G1 of `research/T17/SPEC_ISSUES.md` (same as U3–U7); `hε₀ : ε₀ ≤ 1` is already carried by lane 385's `force_derivative_bound` and at assembly comes from `eps_le_placement` + `PlacementData.eps_le_one`. No named input (`def … : Prop`), no placeholder field.
3. **Mutation coverage is type-level only.** The two negative probes below are `Type mismatch` failures of the `exact`-conformance probes; they do not test whether the *proof* would have supported a stronger RHS. In fact it would: the proof gives `≤ C ε^{3/2-s}`, strictly stronger than the manuscript's `C_s(ε^{3/2}+ε^{3/2-s})` for `ε<1`. I kept the Spec's spelling verbatim rather than strengthening it.

**Failed approaches** (all in `ATTEMPTS_U11.md`):
- T13 `localization` + `dotHomogeneousENorm` — the Fourier-convention gap above.
- `‖·‖_{H^s} ≤ ‖·‖_{H^1}` for `s ≤ 1` (provable, it is `norm_datum_mono`) — gives rate `ε^{1/2}`, which is **weaker** than `ε^{3/2-s}` for `ε<1`, `s<1`. Kept only as the continuity tool.
- `Paper1.PeriodicCorrectionEndpointInstantiation.eventually_correction_coordinate_periodized_endpoint_product:30`, the only pre-existing *periodized* endpoint statement for this force — rejected: it is `∀ᶠ ε in 𝓝[>] 0` and assumes `hcenter : ‖x₀‖ < 1/4`, which a chart ball inside `(0,1)³` does not satisfy. Recentring the copy removes the need for any such hypothesis.
- `abel` on `z.2 - lattice n + x₀ = z.2 + x₀ - lattice n` over `PiLp`: leaves `z.2 + -1 • lattice n + x₀ = -1 • lattice n + (z.2 + x₀)` unsolved; `sub_add_eq_add_sub` closes it.
- `mul_le_mul_left'`: `Unknown identifier` at this pin; used `mul_le_mul' le_rfl h`.
- `rw [fourierSobolevNorm_translate]` after a `funext`-produced beta-redex `fun x => (fun y => …) (x - -x₀)`: "Did not find an occurrence of the pattern"; `simp only [sub_neg_eq_add]` then `exact` works.

## 4. Commands and results

All from `…/438-T17-U11-sobolev/verification` after `. ../scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`.

| Command | Result |
|---|---|
| `lake build NSFormalization.Section3.T17.Sobolev` | `Build completed successfully (10014 jobs).` — 0 errors (warnings are pre-existing, from replayed upstream modules only) |
| `lake env lean ../formalization/NSFormalization/Section3/T17/Sobolev.lean` | no output, exit 0 |
| `lake env lean ../research/T17/probes/sobolev_closes.lean` | 5 lines, each `depends on axioms: [propext, Classical.choice, Quot.sound]` (`field_sobolevConst_pos`, `field_forceSobolev_memLp`, `field_force_sobolev_bound`, `fields_at_placement`, `nonvacuous_sobolev`); no errors, so the three `A.*` record-projection conformance `example`s typechecked |
| `lake env lean ../research/T17/axioms_u11.lean` | 21 declarations, all `[propext, Classical.choice, Quot.sound]` |
| `make check` (repo root) | passes: architecture checks JSON; `test_contract_policy.py` `Ran 13 tests … OK`; `check_work_queue.py` `45 work items: ownership, contract registration and task cards consistent.` |
| `grep -nE "sorry\|admit\|native_decide\|^axiom \|maxHeartbeats"` on the three new Lean files | no matches (exit 1) |
| `git show --stat HEAD` | 6 files, 962 insertions, 0 deletions — 1 new Lean module, 2 new research Lean files, 1 new md, 2 md appends; no existing module touched |

Negative probes (run from `/tmp/u11mut`, deliberately not committed), both **failed as required**:
- exponent `ε ^ ((3:ℝ)/2 - s)` → `ε ^ ((3:ℝ)/2 + s)`: `error: Type mismatch … ENNReal.ofReal (sobolevConst … s * (ε ^ (3 / 2) + ε ^ (3 / 2 - s))) but is expected to have type … ε ^ (3 / 2 + s)`
- range `s ≤ 1` → `s ≤ 2` on all three fields: three `Type mismatch` errors, each printing the delivered `s ≤ 1` range.
