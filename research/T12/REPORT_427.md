# REPORT_427 — T12 dedupe + `T01.mean_zero_calculus` registration (Opus; transcribed by lead from the agent message, report-file guard)

Lane complete and committed. Full four-part report below (I did not create `research/T12/REPORT_427.md` — my harness forbids writing report/summary `.md` files, and the brief allowed the final message instead; the durable repo record lives in `ATTEMPTS_UREG.md` and the `T12_SPLIT.md` status section, which are not report files).

## 1. What was proved / changed

**The dedupe (the exact move).** Lanes 400 and 405 each declared, inside the one namespace `NSFormalization.Section3.T12`, a `contDiff_dirDeriv` with the *identical* proof term `(hw.fderiv_right (by simp)).clm_apply contDiff_const`. Lane 400's is the general one (`{w : Space → F}` under `variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]`); lane 405's is exactly its `F := Space` instance (`{v : SpatialField}`, and `SpatialField` is the reducible `abbrev Space → Space`). I moved the **general** one verbatim into a new leaf module `Section3/T12/DirDeriv.lean` (sole import `NSFormalization.Section4.A05.SmoothJets`), deleted both copies, and added `import NSFormalization.Section3.T12.DirDeriv` to `GradientLSix.lean` and `GradientLambdaL3.lean`. No exported statement changed; all call sites (7 in GradientLSix, 4 in GradientLambdaL3, 1 in `Section3/T20/CriticalTrilinear.lean`) elaborate unchanged because the lane-405 uses instantiate `F := Space` by reducible unfolding.

I scanned for further collisions: every `theorem|lemma|def|abbrev|instance|structure` head across all eleven `Section3/T12/*.lean` modules, `sort | uniq -d` → **exactly one** duplicate, `contDiff_dirDeriv`. Nothing else.

**The registration.** `T01.mean_zero_calculus` is now the 43rd registered contract: the reconciled T12 `MeanZeroSobolevCalculusAPI` — nine proved fields (tame product on `H^m(T³)` for `2 ≤ m`, `H²→L^∞`, critical `Ḣ^{1/2}→L³`, existence of a periodic `Λ` representative, `‖∇v‖₃+‖Λv‖₃ ≤ C‖v‖_{Ḣ^{3/2}}`, `‖∇v‖₆ ≤ C‖Δv‖₂`, `‖v‖_{H²} ≤ C‖Δv‖₂`, and both directions of the spectral-gap comparison at `0 ≤ s`) with seven constants as structure data. No `sorry`/`axiom`/`native_decide`/placeholder; every declaration prints `[propext, Classical.choice, Quot.sound]`.

## 2. What exists in Lean now

All paths under `/data_8T/ping/blowup_density/.claude/worktrees/427-T12-UREG-dedupe-register/`:

- `formalization/NSFormalization/Section3/T12/DirDeriv.lean` — **new**, 33 lines, the single shared `contDiff_dirDeriv`.
- `formalization/NSFormalization/Section3/T12/GradientLSix.lean`, `.../GradientLambdaL3.lean` — one import added, the duplicate declaration replaced by a two-line pointer comment. Nothing else touched.
- `verification/Contracts/V1/MeanZeroCalculus.lean` — now **token-for-token** the `BlowupDensity.T12.Draft` body of `research/T12/Spec.lean` (verified by a comment-stripped token diff; the only residual difference is the added `def meanZeroCalculusStatement`). Lane 419 had dropped the Spec's three defeq checks (`lift v = BlowupDensity.Contracts.V1.lift v` and the gradient/Laplacian analogues, `Spec.lean:534-546`); they are restored, which needed `import Contracts.V1.GradientL6`, and the three derivative docstrings were restored to the Spec's manuscript-citing ones. A file header was added.
- `verification/Bindings/MeanZeroCalculus.lean` — rewritten. Eleven `rfl` drift guards (`IsPeriodicScalarDatum`, `periodicScalarSobolevENorm`, `MemPeriodicHmScalar`, `MemPeriodicHmVector`, `MemPeriodicHomogeneous`, `SmoothPeriodicT`, `periodicLpENorm` pointwise, `lift`, `gradientTensor`, `laplacian`, `IsPeriodicLambda`) — **no fieldwise conversion was needed anywhere** — plus `def meanZeroCalculus` assembling the 9 fields and 7 constants from `tameProductConst`, `linftyConst`, `CcriticalHalf`, `CcriticalThreeHalves`, `Csix`, `hTwoConst`, `gapConst`, and `theorem meanZeroCalculusStatement_holds`.
- `verification/Tests/MeanZeroCalculus.lean` — `def checkedMeanZeroCalculus` (a `def`, not `theorem`: the API is Type-valued), `run_cmd TestSupport.checkAxioms ``checkedMeanZeroCalculus`, independent conformance restatements of **all 7 constants and all 9 fields**, and non-vacuity: the witness `meanZeroProbe = meanZeroPartT (x ↦ cos(2π x₀)·e₀)` rebuilt from lane 396's probe with `≠ 0`, smoothness, periodicity, mean-zero and `MemPeriodicHomogeneous s` for every `0 < s`, then five fields instantiated on it.
- `verification/contracts.json` — 43 contracts; the entry is now a proper list element with `specification`/`binding_module`/`test_module`/`declaration`/`enabled` and an honest scope naming what is *not* asserted (whole-space halves, `s < 0`, non-mean-zero homogeneous norms, uniqueness of `Lv`, sharpness of constants) and spelling out every constant as a closed term.
- `collaboration/work_items.json`, `collaboration/TASKS.md`, `collaboration/tasks/T12.md` — T12 claimed by `erenup`, `contracts: ["T01.mean_zero_calculus"]`, re-rendered.
- `research/T12/ATTEMPTS_UREG.md` (rewritten truthfully, 419's text kept under a "superseded" heading), `research/T12/axioms_ureg.lean` (24 `#print axioms`), `research/T12/T12_SPLIT.md` (registration status section), `logs/LESSONS.md` (one new top line).

Commit `f7e398e2` on `erenup/427-T12-UREG-dedupe-register`. No push, no merge, no rebase.

## 3. Gaps

- **No Lean gap.** Nothing was left unproved, no statement was weakened, no placeholder field exists.
- **`parent_task` judgement call, please confirm.** Lane 419 wrote `"parent_task": "T12"`. I changed it to `"T01"` because (a) the `work_items.json` T12 deliverable says "register the accepted versioned contract **under parent task T01**", (b) T01's blueprint contract is the node whose text reads "prove the uniform mean-zero critical embedding", and (c) both precedents take the parent named by the id prefix — `T01.torus_local_theory` is T11's content under parent T01, `T02.localization` is T13's content under parent T02. Either value passes `check_contracts.py`; say the word and it is a one-line change.
- **`research/T12/REPORT_427.md` not written** (harness rule against report `.md` files). Everything that belongs in the repo record is in `ATTEMPTS_UREG.md` and the `T12_SPLIT.md` status section, and the `T12_SPLIT.md` pointer was adjusted so there is no dangling reference.
- **Two probes fail by design** — do not read these as regressions. `research/T12/probes/rev400_negative_constant.lean` and `rev405_negative.lean` are mutation probes; they still fail with exactly the intended mismatch, e.g.
  `error: Type mismatch: gradientLSix has type … ENNReal.ofReal Csix * … but is expected to have type … ENNReal.ofReal 0 * …`.
- **Lane 419's Bindings never compiled at all** (419 reported only that the *contract* file compiles). Three independent faults, all recorded in `ATTEMPTS_UREG.md` §2: opening both the contract namespace and `NSFormalization.Section3.T12` made every bridge LHS `overloaded, errors`; `NavierStokes.ProblemStatement` was never opened so `Space` resolved elsewhere (`Application type mismatch: z has type Space → ℝ but is expected to have type NavierStokes.ProblemStatement.Space → ℝ`); `scoped ENNReal` was never opened so `(p : ℝ≥0∞)` was a parse error (`expected token`). Also `MeanZeroCalculus.lift` does not resolve from inside `namespace BlowupDensity.Bindings` — the bridges must spell `Contracts.V1.MeanZeroCalculus.lift`.
- **One approach rejected:** putting the shared helper in `Section4/A05/SmoothJets.lean` next to `dirDeriv`. That module sits in the registered `A05.gradient_l6` closure and the brief's edit exception covers only the two T12 modules, so a new T12 leaf module is the smaller change.

## 4. Commands run and results

All from the worktree root, after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, `lake` from `verification/`.

| command | result |
|---|---|
| `lake build NSFormalization.Section3.T12.{GradientLSix,GradientLambdaL3,CriticalL3Density} NSFormalization.Section3.T20.CriticalTrilinear` | `Build completed successfully (10648 jobs).` — 0 errors |
| `lake env lean ../research/T12/probes/gradient_l6_closes.lean` | empty output, exit 0 |
| `lake env lean ../research/T12/probes/gradient_lambda_l3_closes.lean` | empty output, exit 0 |
| `lake env lean ../research/T12/probes/{api_on_canonical,critical_l3_density_closes,rev400_finiteness}.lean` | empty output each |
| `lake env lean ../research/T12/{axioms_u5,axioms_u6}.lean` | all 52 + 24 declarations `[propext, Classical.choice, Quot.sound]` |
| `lake build Bindings.MeanZeroCalculus` | `Build completed successfully (10063 jobs).` |
| `lake build Tests.MeanZeroCalculus` | `Build completed successfully (10065 jobs).`; `info: Contract BlowupDensity.Tests.checkedMeanZeroCalculus: checked; standard logical axioms only` — no warnings under `warningAsError = true` |
| `lake env lean ../research/T12/axioms_ureg.lean` | all 24 declarations (11 bridges, record, statement, acceptance def, 9 witness declarations, moved helper) `[propext, Classical.choice, Quot.sound]` |
| `BASE_REF=origin/erenup/integration-section3 scripts/gates.sh` | `== make check` ok; `== make test` all Tests report "standard logical axioms only", including `Tests/MeanZeroCalculus.lean:31:0`; `== make test-mutations` → `extra_axiom: rejected as required`, `weakened_hypothesis: rejected as required`, `Mutation suite passed.`; `== gates OK` |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` | exit 0, `"registered_contracts": 43`, `"base_compatibility_checked": true` |
| `make check` (work queue) | `13 tests ... OK`; `45 work items: ownership, contract registration and task cards consistent.` |
| `git diff --stat verification/contracts.json` | `verification/contracts.json | 18 ++++++++++++------` (12 insertions, 6 deletions: the new list element in, lane 419's malformed top-level key out) |
| forbidden-token scan over every changed `.lean` | only prose hits (a pre-existing lane-400 docstring sentence and my audit file's title); no `sorry`/`admit`/`axiom`/`native_decide` in code |


> Lead note after review 427: (1) this file was transcribed by the lead from the agent message (report-file guard), so "REPORT_427.md not written" describes the agent's own step; (2) `parent_task: T01` is **resolved** by the lead (precedent `T01.torus_local_theory`, `T02.localization`; the T12 work item names T01).
