# REPORT_434 — T17 U9 energy bound + honest slices (Opus; transcribed by lead from the agent message, report-file guard)

Lane 434 (T17 U9) is done. Four-part report.

---

## 1. What was proved

All five U9 targets of the canonical `CorrectionAPI` (`Section3/T17/Correction.lean:223-241`, Spec form `research/T17/Spec.lean:900-920`), stated at the concrete `correctionData` of unit U2, closed with no incomplete proof.

**Common premise block** (identical on the three field theorems; `r` only on the bound):

```
{v : SpaceTimeField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T : ℝ)
{θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) {θR r ε₀ : ℝ}
(hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
(hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
(hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
(hcube : closure (ball x₀ r) ⊆ interior fundamentalCube)
(hε₀ : ε₀ ≤ 1) (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r)
```

`hv` is the **documented G1 premise** (`research/T17/SPEC_ISSUES.md`), needed because Paper1's two Euclidean energy bounds and `physical_smooth` are stated for a globally smooth reference. `hcube` is the only placement clause beyond lane 385/425's block, and it is **not a new assumption**: the probe's `hcube_of_placement` derives it as `(closure_mono A.ball_in_chart).trans place.chartBall_in_cube`.

**`correction_slice_memLp`** (`Energy.lean:224`) and **`correction_gradient_memLp`** (`:240`):
```
∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀, ∀ t : ℝ,
  MemLp (torusLift (fun x : Space =>
      (correctionData v x₀ T θ η O θR ε₀).correction ε (t, x))) 2 periodicTorusMeasure

∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀, ∀ t : ℝ,
  MemLp (torusLift (fun x : Space =>
      spatialGradient ((correctionData v x₀ T θ η O θR ε₀).correction ε) t x)) 2
    periodicTorusMeasure
```

**`energyConst`** (`:261`) — the constant, explicit, and **the same one the Section 4 binding registers** (`verification/Bindings/Correction.lean:349`):
```
def energyConst … : ℝ :=
  Real.sqrt (Classical.choose
      (Paper1.CorrectionEnergy.physicalCorrection_uniform_energy hv x₀ T hθ hη hθc hηc)) +
  Real.sqrt (Classical.choose
      (Paper1.InsertionEnergy.correction_gradientSquare_bound hv x₀ T hθ hη hθc hηc))
```
i.e. `C = √A + √D` with `A` the uniform `L²`-energy `ε³` constant and `D` the time-integrated dissipation `ε³` constant. **`energyConst_nonneg`** (`:273`): `0 ≤ energyConst hv x₀ T hθ hη hθc hηc`.

**`correction_energy_bound`** (`:285`), `eq:wE`:
```
∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
  energyENormT T ((correctionData v x₀ T θ η O θR ε₀).correction ε) ≤
    ENNReal.ofReal (energyConst hv x₀ T hθ hη hθc hηc * ε ^ ((3 : ℝ) / 2))
```

Route (as planned in the SPLIT, with one deviation, see §3): every torus slice of `D.correction ε` is **definitionally** T13's `periodize` of the single-copy slice (`correction_slice_eq`, `rfl`), so T15 U-TB1's `eLpNorm_torusLift_periodize` / `eLpNorm_torusLift_spatialGradient_periodize` give the two slicewise Haar↔Lebesgue norm identities (`eLpNorm_torusLift_correction_slice :158`, `eLpNorm_torusLift_correction_gradient :177`); `energyEssSupT`/`energyGradientT` then become syntactically the two quantities bounded by `I02.energyEssSup_le` / `I02.energyGradient_le`, and `I02.sqrt_mul_cube` turns `√(A ε³) + √(D ε³)` into `(√A + √D)·ε^{3/2}`.

Four supporting declarations, all new, none a placeholder: `measurable_torusChart`, `memLp_torusLift_of_continuous`, `physicalCorrection_slice_ball`, `physicalCorrection_slice_tsupport_cube`, `correction_contDiff`.

## 2. What exists in Lean now

- `/data_8T/ping/blowup_density/.claude/worktrees/434-T17-U9-energy-bound/formalization/NSFormalization/Section3/T17/Energy.lean` — 354 lines, **new** module, namespace `NSFormalization.Section3.T17`. No existing module edited.
- `/data_8T/ping/blowup_density/.claude/worktrees/434-T17-U9-energy-bound/research/T17/probes/energy_closes.lean` — 240 lines: three `field_*` theorems restating the Spec fields at the concrete data and closed by `exact`; four `example`s projecting `A.correction_slice_memLp` / `A.correction_gradient_memLp` / `A.correction_energy_bound` / `A.energyConst_nonneg` out of a hypothetical `CorrectionAPI` into exactly the delivered statements (two-sided conformance); `hcube_of_placement`; `fields_at_placement`; `cubeCentre` + `closure_ball_cubeCentre`; `nonvacuous_energy`.
- `/data_8T/ping/blowup_density/.claude/worktrees/434-T17-U9-energy-bound/research/T17/axioms_u9.lean` — 13 `#print axioms`.
- `/data_8T/ping/blowup_density/.claude/worktrees/434-T17-U9-energy-bound/research/T17/ATTEMPTS_U9.md`
- U9 status paragraph appended at `/data_8T/ping/blowup_density/.claude/worktrees/434-T17-U9-energy-bound/research/T17/T17_SPLIT.md:219-238`
- One new top line in `/data_8T/ping/blowup_density/.claude/worktrees/434-T17-U9-energy-bound/logs/LESSONS.md`
- Commit `ed5976b6` on `erenup/434-T17-U9-energy-bound`; working tree clean; nothing pushed, merged or rebased. No `REPORT_434.md` was written (my harness forbids report `.md` files; per the brief the full report is this message).

## 3. Gaps

**No residual statement — all five targets are closed.** Five things the lead should know:

1. **G1 remains open at the spec level, not at this lane's level.** The theorems carry `hv : ContDiff ℝ ∞ v` explicitly, exactly as U3–U7 do. The canonical `CorrectionAPI` has only `reference_periodic`, so assembly unit U12 must still add `reference_smooth` or truncate the reference.
2. **The brief's `MemLp` route does not exist.** `grep -n "memLp" formalization/NSFormalization/Section3/T15/HaarBridge.lean` returns nothing — there is no `memLp_torusLift_*` there. `Paper1.memLp_torusLift` (`Paper1/TorusCube.lean:58`) is `ℂ`-only and its proof goes through `Measurable.comp`, which would demand `BorelSpace`/`SecondCountableTopology` on the value type. §1 of the new module reproves it for an arbitrary normed value type by composing with `Continuous.comp_aestronglyMeasurable` instead; this is a candidate for promotion into `Paper1/TorusCube.lean` or `Section3/T10` by a maintenance lane (lane 413's LESSONS line reports the same gap for the gradient tensor), not moved here because the brief forbids editing existing modules.
3. **Non-vacuity witnesses for anything Haar-normed must sit inside the cube.** `T13.fundamentalCube = {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}`, so lane 425's `x₀ = 0` does **not** satisfy `hcube` (half the ball has negative coordinates). This lane's witness is placed at `cubeCentre = WithLp.toLp 2 (fun _ => 1/2)` with radius `1/4`. Later units (U8, U10, U11) inherit this.
4. **`T16.exists_threshold` hides `ε₀ ≤ 1`.** Its witness *is* `min 1 (…)` but the existential does not expose it, while Paper1's two `ε³` bounds need `∀ ε ∈ Ioc 0 1`. The non-vacuity theorem takes `min 1 ε₁` and re-derives both clauses.
5. **Line-number corrections** (verified with `sed -n`/`grep -n`): in `verification/Contracts/V1/Correction.lean` the registered field `correction_energy_bound` is at `:493-494` (the SPLIT's `:486` is a doc-comment line), `energyConst :478`, `correction_slice_memLp :482`, `correction_gradient_memLp :487`. In `Section3/T10/PeriodicData.lean` the energy definitions are at `:328` / `:334` / `:340`, not `:330-341`.

**Failed / rejected approaches** (full record in `research/T17/ATTEMPTS_U9.md`):
- `Paper1.memLp_torusLift` directly — `ℂ`-only, see (2).
- Routing the `MemLp` fields through the Haar bridge — the bridge gives an `eLpNorm` equality only, which supplies finiteness but not a.e.-strong-measurability, so it would still need the new measurability lemma; continuity + the probability measure closes it in four lines with no support hypothesis at all.
- Going through `Contracts.V1.Data.energyENorm` — impossible from `formalization/` (contract-import policy), and unnecessary: `I02.energyEssSup_le` / `energyGradient_le` are already stated in the unfolded form.
- Two elaboration slips, both fixed in the same pass: `have hsupp := physicalCorrection_slice_tsupport_cube …` → `don't know how to synthesize implicit argument v` / `T` (the two implicits occur only in the conclusion; fixed with `(v := v) (T := T)`); `obtain ⟨A, hA, hAb⟩ := ⟨Classical.choose …, …⟩` → `Invalid ⟨…⟩ notation: The expected type of this term could not be determined` (replaced by `have … := Classical.choose_spec …` + `set … with …` + `obtain`).

## 4. Commands and results

All from `.../434-T17-U9-energy-bound/verification` after `. ../scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`.

| Command | Result |
|---|---|
| `lake build NSFormalization.Section3.T17.Energy` | `✔ [9924/9924] Built NSFormalization.Section3.T17.Energy (4.6s)` / `Build completed successfully (9924 jobs).` — 0 errors |
| `lake env lean ../formalization/NSFormalization/Section3/T17/Energy.lean` | no output, exit 0 |
| `lake env lean ../research/T17/probes/energy_closes.lean` | 7 lines, each `depends on axioms: [propext, Classical.choice, Quot.sound]`; no errors, so the four `A.*` conformance `example`s typechecked |
| `lake env lean ../research/T17/axioms_u9.lean` | 13 lines, each `[propext, Classical.choice, Quot.sound]` |
| `make check` (repo root) | passes: architecture checks JSON, `test_contract_policy.py` `Ran 13 tests … OK`, `check_work_queue.py` `45 work items: ownership, contract registration and task cards consistent.` |
| `grep -nE "sorry\|admit\|native_decide\|^axiom \|maxHeartbeats"` on the three new Lean files | no matches (exit 1) |

Negative probes (in `/tmp/u9mut`, deliberately not committed), both **failed as required**, printing the delivered statement:
- `ε ^ ((5:ℝ)/2)` instead of `ε ^ ((3:ℝ)/2)`: `error: Type mismatch … has type … ENNReal.ofReal (energyConst hv x₀ T hθ hη hθc hηc * ε ^ (3 / 2)) but is expected to have type … * ε ^ (5 / 2)`
- Lebesgue slice instead of the Haar torus lift: `error: Type mismatch … has type … MemLp (torusLift fun x => (correctionData v x₀ T θ η O θR ε₀).correction ε (t, x)) 2 periodicTorusMeasure but is expected to have type … MemLp (fun x => …) 2 volume`
