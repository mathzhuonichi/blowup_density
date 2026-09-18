# REPORT_412 — ForceProfile.lean merge repair (Opus; transcribed by lead from the agent message, report-file guard)

Committed `45f6113f` on `erenup/412-MAINT-t17-forceprofile-merge-repair`. No push, no merge, no rebase.

---

# Lane 412-MAINT — four-part report

## 1. What was proved / what the verification found

**The lead's restore was itself a regression, and I repaired it.**

The brief assumed the task was pure verification of `a1417ef7` (reset of `ForceProfile.lean` to the reviewed lane-394 blob `c4be85b0`). That reset does fix the parse damage from #366, but it **silently deletes two theorems that were already on integration**: `force_eq_chart` and `force_profile_identity` (the Spec-form force identity), added by lane-375 rev1 (`2730dbc1`, "close Spec-form force_profile_identity").

Why the union merge went wrong, precisely:

| version | blob | lines | has the two theorems |
|---|---|---|---|
| lane-375 rev0 `5fb0be0c` (the file's real common ancestor) | `48b47a94` | 314 | no |
| integration side `cc5813d7` (via lane-375 rev1 `2730dbc1`) | `cb414de6` | 325 | **yes** |
| lane-394 side `c4be85b0` | `c71a68b6` | 264 | no |
| union merge `aa9ab1d8` → `139f6431` | `b3d65059` | 349 | yes, but unparseable |
| lead's reset `a1417ef7` | `c71a68b6` | 264 | **no — content loss** |

Lane 394 branched from integration at `a3f63026`, i.e. *before* `2730dbc1` landed. Both sides then independently made the same structural change (import `Transport`, drop the local `correctionForce` def, rewrite two doc paragraphs) — but only integration added the two theorems. `git merge-base c4be85b0 cc5813d7` is `2fe4fb75`, which **predates the file entirely** (`fatal: path … exists on disk, but not in 2fe4fb75`), so git had no usable base and the union resolver just concatenated the two texts.

Measured proof that the reset broke integration (run before my repair):

```
research/T17/probes/force_profile_closes.lean:93:2: error(lean.unknownIdentifier):
  Unknown identifier `force_profile_identity`
research/T17/axioms_u4.lean:18:14: error(lean.unknownIdentifier): Unknown constant `force_eq_chart`
research/T17/axioms_u4.lean:19:14: error(lean.unknownIdentifier): Unknown constant `force_profile_identity`
```

Both files are lane-375 artefacts already on integration (reviewed at `research/T17/REVIEW_375-T17-U4-force-profile.md:353`/:357).

**The repair — the only change made.** Set the file to the integration blob `cc5813d7` (which keeps both theorems verbatim, and keeps lane-375 rev1's corrected paragraph "It **equals** the Euclidean `CorrectionForceProfile.forceProfile` … not a `rfl` bridge"), then apply lane 394's two documentation updates on top:

1. module docstring section "`force_profile_identity`: chart force and Spec form" — appended lane 394's sentence about the canonical periodized composition with `Transport.force_eq`, its germ in `ATTEMPTS_UCAN.md`, and the check in `probes/force_profile_canonical.lean`;
2. docstring of `physicalForce_eq_rescaledForceProfile` — replaced the stale rev0 sentence ("the lift … is U2's `force_eq` (lane 373), whose exact residual is recorded in `ATTEMPTS_U4.md`") with one pointing at `force_eq_chart` below plus the same two lane-394 records.

`git diff cc5813d7 -- …/ForceProfile.lean` is **comment text only**: zero Lean statements, proofs, imports or declaration names differ from what is on the integration parent. No `sorry`/`admit`/`axiom`/`native_decide`; no statement changed.

## 2. What exists in Lean now

`/data_8T/ping/blowup_density/.claude/worktrees/412-MAINT-t17-forceprofile-merge-repair/formalization/NSFormalization/Section3/T17/ForceProfile.lean` — 330 lines, 4 imports (no duplicates), balanced doc comments, 14 declarations:

- defs `rescaledReference`, `rescaledForceProfile`
- `spatialDerivative_rescaledReference`, `rescaledReference_spatialDerivative_smul`, `rescaledForceProfile_eq_forceProfile`, `force_profile_smooth`, `force_profile_support`, `forceProfileConst`, `forceProfileConst_nonneg`, `force_profile_uniform`, `inverseScale_correctionChartPoint`, `physicalForce_eq_rescaledForceProfile`
- **restored**: `force_eq_chart`, `force_profile_identity`

All twelve theorems/defs audited by `research/T17/axioms_u4.lean` at exactly `[propext, Classical.choice, Quot.sound]`, including the two restored ones.

Importers (source files only, `formalization/NSFormalization` + `verification` + `research`): `formalization/NSFormalization/Section3/T17/Correction.lean` (built), and probes `research/T17/axioms_u4.lean`, `research/T17/probes/force_profile_closes.lean`, `rev375_vocabulary_axioms.lean`, `rev375_wrong_power.lean` (all run). **No `verification/` module imports it.**

## 3. Gap

Nothing blocking. Two things for you:

1. **`origin/erenup/integration-section3` still carries the broken union blob `b3d65059`** — duplicate imports at lines 3–4 and a module docstring split by a stray `-/`. This lane's branch is the fix; per the brief I did not push or merge it. Note that merging the lane-394 blob instead would re-break `force_profile_closes.lean` and `axioms_u4.lean`.
2. **Two T17 probes fail by design** and are not regressions:
   - `research/T17/probes/rev394_mutation.lean` — reviewer's mutation probe (chart time coefficient 1→2, temporal-volume bound 4→2). Expected exit 1; the two type mismatches printed are byte-identical to those recorded at `REVIEW_394-T17-UCAN-canonical-correction.md:385`/:391.
   - `research/T17/probes/rev394_field_conformance.lean` — declared **obsolete** by `REVIEW_394-T17-UCAN-canonical-correction.md:19` ("tries to use the chart theorem directly and is obsolete as a completion test; the new proof supplies the missing bridge"), and absent from the reviewer's pass list at :294–296. It fails identically against the lane-394 blob, the integration blob and the repaired file, because `physicalForce_eq_rescaledForceProfile` is the chart-force statement in all three. Superseded by `probes/force_profile_canonical.lean`, which passes.

   The lane-375-era negatives (`rev369_negative_widened_ball`, `rev369r1_negative_lt`, `rev370_support_mutation`, `rev373_mutation`, `rev375_wrong_power`, `rev385_mutated`, `rev385_negative`) also fail by design.

No failed approach to report on the fix itself: the diagnosis came straight from the git three-way analysis, and the resolution compiled first try. The one dead end was `git merge-file --diff3` against `git merge-base c4be85b0 cc5813d7` (= `2fe4fb75`), which aborted with `fatal: path … exists on disk, but not in 2fe4fb75` — that merge base predates the file, which is exactly why the original merge produced garbage; I used `5fb0be0c` (lane-375 rev0) as the true content base instead and resolved hunk by hunk.

## 4. Commands run and results

All Lake calls after `. scripts/lean-env.sh`, from `verification/`, `LEAN_NUM_THREADS=6`.

**Build (after repair)** — `lake build NSFormalization.Section3.T17.{ForceProfile,Correction,Transport,CorrectionDeriv,ForceDeriv,LatticeDeriv,CorrectionProfile}` → **exit 0, 0 `error:` lines**, `Build completed successfully (10015 jobs).`, `✔ [10015/10015] Built NSFormalization.Section3.T17.Correction (2.8s)`.

**`lake env lean ../formalization/NSFormalization/Section3/T17/ForceProfile.lean`** → **exit 0, 0 bytes of output**.

**All 22 probes + 6 axiom files:**

| file | exit | note |
|---|---|---|
| `probes/correction_canonical.lean` | 0 silent | |
| `probes/correction_profile_closes.lean` | 0 silent | |
| `probes/derivative_bounds_closes.lean` | 0 | 3 axiom lines, all standard |
| `probes/force_profile_canonical.lean` | 0 silent | |
| `probes/force_profile_closes.lean` | **0 silent** | **was exit 1 before the repair** |
| `probes/lattice_deriv_closes.lean` | 0 silent | |
| `probes/rev369_api_name.lean` | 0 silent | |
| `probes/rev369_negative_widened_ball.lean` | 1 | negative, expected |
| `probes/rev369_nonvacuity.lean` | 0 silent | |
| `probes/rev369r1_negative_lt.lean` | 1 | negative, expected |
| `probes/rev370_support_mutation.lean` | 1 | mutation, expected |
| `probes/rev373_axioms_all.lean` | 0 | all standard |
| `probes/rev373_mutation.lean` | 1 | mutation, expected |
| `probes/rev373_nonvacuity.lean` | 0 silent | |
| `probes/rev375_vocabulary_axioms.lean` | 0 | 3 axiom lines, all standard |
| `probes/rev375_wrong_power.lean` | 1 | negative (`ε^3` vs `ε^2`), expected |
| `probes/rev385_mutated.lean` | 1 | mutation, expected |
| `probes/rev385_negative.lean` | 1 | negative, expected |
| `probes/rev394_field_conformance.lean` | 1 | obsolete per REVIEW_394:19 |
| `probes/rev394_mutation.lean` | 1 | mutation, expected per REVIEW_394:383 |
| `probes/rev394_nonvacuity.lean` | 0 silent | |
| `probes/transport_closes.lean` | 0 silent | |
| `axioms_u1.lean` | 0 | all standard |
| `axioms_u2.lean` | 0 | all standard |
| `axioms_u3.lean` | 0 | all standard |
| `axioms_u4.lean` | **0** | **was exit 1**; 12 declarations, all standard |
| `axioms_u5u6.lean` | 0 | all standard |
| `axioms_ucan.lean` | 0 | all standard |

`axioms_u4.lean` now ends with:
```
'NSFormalization.Section3.T17.force_eq_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.force_profile_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Gates:**
- `make check` → **exit 0** (`check_contracts.py` clean; `test_contract_policy.py` 13 tests OK; `check_work_queue.py`: "45 work items: ownership, contract registration and task cards consistent.")
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` → **exit 0**, `"registered_contracts": 42`, `"base_compatibility_checked": true`
- `make test` → **exit 0**, 0 `error` lines, every `Tests.*` contract "checked; standard logical axioms only"
- hygiene grep `sorry|admit|^axiom |native_decide|maxHeartbeats` on the repaired file → no hits

`research/MAINT/REPORT_412.md` was **not** written — the report-file guard rejected it, so this message is the report.
