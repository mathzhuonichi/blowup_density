# Lane 029 review — `I02.correction_v2` (contract version 2)

Run on `erenup/029-I02-v2-thetaradius` @ `ef6db06`, base `erenup/integration` @ `8f70cfa`, in
`.claude/worktrees/029-I02-v2-thetaradius`; `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`. Lean timings
below are replays off the closure already built here; no cold-build timing was taken.

## Verdict

**ACCEPT.** The project's first V2 contract is correctly shaped: `Contracts/V2/CorrectionAPI` is version one plus
exactly one field (Lean-confirmed, not prose-confirmed), the compatibility binding is the definitional parent
projection, the registered V2 statement is strictly stronger than V1, V1 is byte-identical and still green, and the
`K → K_*` premise lanes 021/027 recorded as undischargeable is discharged by bare term application. Six issues, all
cosmetic or documentary; none blocks the merge.

## 1. Gates

| command | time | result |
|---|---|---|
| `make check` | 8.3 s | exit 0; `registered_contracts: 7`, policy `Ran 13 tests … OK`, `30 work items … consistent.` |
| `lake test` (from `verification/`) | 2.1 s | exit 0; **7** `checked; standard logical axioms only`, incl. `Tests/Correction.lean:19` (`checkedCorrection`, V1) and `Tests/CorrectionV2.lean:28` (`checkedCorrectionV2`). No `error`/`sorry`/`declaration uses`. |
| `make test-mutations` | 8.7 s | exit 0; `implementation_refactor: accepted`, `admitted_proof`/`extra_axiom`/`weakened_hypothesis` `rejected as required`. |
| `check_contracts.py --base-ref erenup/integration` | 3.9 s | exit 0; `base_compatibility_checked: true`; closures 5/534/597/**600**/60/59/621 — V2's = V1's 597 + exactly the 3 new modules. |
| `build_changed_lean.py --base-ref … --dry-run` | 0.02 s | `Bindings.CorrectionV2, Contracts.V2.Correction, NSFormalization.Section4.I02.Prescribed, Tests.CorrectionV2` — **4 modules**. |
| same without `--dry-run` | 2.1 s | `Build completed successfully (9364 jobs)`. |

## 2. V1 frozen

`git diff erenup/integration..HEAD --stat -- verification/Contracts/V1 verification/Bindings/Correction.lean verification/Tests/Correction.lean` → **empty**. Independently enforced: `check_compatibility` byte-compares every
file under `verification/Contracts` present at the base ref plus every registered test module, and passed
(`Bindings/` is *not* in that byte-compare — §6).

## 3. V2 = V1 + one field

Checked in Lean, not by reading:

```
@Contracts.V2.CorrectionAPI.mk : … (toCorrectionAPI : Contracts.V1.CorrectionAPI ν P) →
                                    K ⊆ toCorrectionAPI.plateau → Contracts.V2.CorrectionAPI ν P K
getStructureFields V1.CorrectionAPI = 73
getStructureFields V2.CorrectionAPI = 2 = [toCorrectionAPI, prescribed_subset_plateau]
```

No V1 field is dropped, renamed or weakened — structural, not a claim about copied text. `correctionStatement`
differs from V1's in exactly three edits: the binder gains `(K : Set Space)`, the hypothesis chain gains a leading
`IsCompact K →`, the existential reads `∃ A : CorrectionAPI ν P K`. Import rule: the file imports **only**
`Contracts.V1.Correction`, accepted by `contract_import_allowed` via the `Contracts.` prefix. Assertion-free —
one `structure`, one `def … : Prop`, no `theorem`/`example`/`instance`/`axiom`/`sorry`.

## 4. Compatibility binding and the discharged premise

All five declarations present and exercised in a scratch: `correctionV1_of_v2 A = A.toCorrectionAPI` proved by
`rfl`, i.e. **definitional**; `correctionStatement_of_v2 : V2.correctionStatement → V1.correctionStatement`
instantiating `K := P.carrier` via `P.carrier_compact`, with `example : Contracts.V1.correctionStatement :=
Bindings.correctionStatement_of_v2 Tests.checkedCorrectionV2` typechecking, so V2 ⇒ V1 holds
registered-to-registered; plus `prescribed_subset_ball`, `isCompact_carrierStar`, `force_carrier_subset_ball`.
The premise, by bare term application, no tactic:

```lean
example {ν : ℝ} {P : Contracts.V1.PacketAPI ν}
    (A : Contracts.V2.CorrectionAPI ν P (P.carrier ∪ Prod.snd '' tsupport P.force)) :
    ∀ z ∈ tsupport P.force, z.2 ∈ Metric.ball (0 : Contracts.V1.Space) A.θRadius :=
  fun _z hz => Bindings.force_carrier_subset_ball A hz     -- compiles
```

and end-to-end from the *registered* statement with no hypothesis beyond `isCompact_carrierStar`: `obtain ⟨A, …⟩ :=
Tests.checkedCorrectionV2 ν P (P.carrier ∪ Prod.snd '' tsupport P.force) T δ r v π g x₀
(Bindings.isCompact_carrierStar P) hT hδ hr hv hπ hdiv heq`, then the term above — exactly the
`force_carrier_subset` field `research/I03/REVIEW_CONTRACT.md` §5.1 deleted from `ScalingAPI`. Scratches deleted.

## 5. Axioms and hygiene

`#print axioms` in one scratch importing `Tests.CorrectionV2` — each exactly `[propext,
Classical.choice, Quot.sound]`: `Tests.checkedCorrectionV2`, `Bindings.correctionV2`,
`Bindings.correctionV1_of_v2`, `Bindings.correctionStatement_of_v2`, `Bindings.prescribed_subset_ball`,
`Bindings.isCompact_carrierStar`, `Bindings.force_carrier_subset_ball`, `Section4.I02.exists_prescribed_cutoff`.
Hygiene over the four new files: zero hits for `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`/`#exit` (comments
included), zero `TODO`/`FIXME`, no trailing whitespace, tabs, CRLF/BOM or double blank lines; final newline in all
four. One `set_option` (issue 1); seven over-100-char lines, all inherited verbatim (issue 6).

## 6. Duplication assessment

`Bindings/CorrectionV2.lean` (553 lines) shares **416** lines with `Bindings/Correction.lean` (537), ~394 of them
proof body. `diff -u` is 7 hunks: imports, module docstring, deletion of the 14-declaration `Correspondence` section
(genuinely imported rather than recopied — a namespace-renamed probe failed on unqualified `energyENorm_eq`/
`mixedLebesgueENorm_le` until `open BlowupDensity.Bindings` was added), signature/target type, the cutoff block, the
record literal gaining one field, and the five new trailing declarations. The mathematical delta is one `choose`
against `exists_prescribed_cutoff`.

**Acceptable as delivered.** Half the lane's reason is a real obstruction: a V1 *record* cannot yield a V2 one —
`θ`, `plateau`, `θRadius` are fields, so nothing outside can widen the plateau, and `V1.correctionStatement` binds
`θRadius` existentially with the witness fixing it from `P.carrier` alone. The other half is lane scope, not policy:
`Bindings/` is **not** byte-frozen by `check_contracts.py` (only `verification/Contracts/**` and registered test
modules are), and `test_contract_mutations.py`'s `implementation_refactor: accepted` case exists to bless re-cutting
a binding under an unchanged contract.
So a shared helper *was* reachable — e.g. `Section4/I02/Assemble.lean` exposing `correctionOfCutoff … (R θ O)
(hR hθ hθc hθR hO hKO hθone) … : V1.CorrectionAPI ν P` built as a structure literal so `.plateau` reduces to `O`
by `rfl`, with V2 then `⟨correctionOfCutoff …, hKplateau⟩` and both bindings calling it. Cleaner on a two-version
horizon, and the right move the moment a V3 or an I03 V2 forces `Bindings/Correction.lean` open anyway (the
`.plateau = O` reduction is the delicate part). Against it: leaving the V1 witness literally untouched is the
strongest evidence that V1 still holds for the same reason it held yesterday. **Report only: extract the helper
when the next version lands.**

## 7. Registry, policy scripts, ATTEMPTS

`contracts.json` adds one entry: `id: I02.correction_v2`, `version: 2`, `specification:
verification/Contracts/V2/Correction.lean` (satisfying `assert f'/V{contract["version"]}/' in contract['specification']`),
`binding_module: Bindings.CorrectionV2`, `test_module: Tests.CorrectionV2`, `declaration:
BlowupDensity.Tests.checkedCorrectionV2`, `enabled: true`, `parent_task: I02`, non-empty
`scope`. A distinct id was required: reusing `I02.correction` trips `Duplicate contract IDs`, and
`check_compatibility` would report `Changed stable contract I02.correction: version`. `work_items.json`
I02 lists both ids. `tasks.py render` regenerates `collaboration/TASKS.md` and `collaboration/tasks/*.md`
**byte-identically** (diffed against a snapshot; `git status` clean after). `git diff
erenup/integration..HEAD -- experiments/` is **empty** — no policy script modified, and
`test_contract_policy.py:138 test_new_version_does_not_replace_old_version` already covered this case.

`ATTEMPTS_V2.md` is accurate on every load-bearing point checked: the 73 V1 fields, the `extends`-vs-copy rationale,
the five rejected alternatives of §3, the §4 walk through each policy script. §5's note that *"an `I03` V2 carrying a
`Contracts.V2.CorrectionAPI` is the natural follow-up"* is present and correctly qualified (R42 v1 not held for this;
`ScalingAPI.correction` reachable via `A.toCorrectionAPI`). Three small inaccuracies, issues 2–4.

## 8. Issues, ranked

1. **Dead `set_option maxHeartbeats 2000000 in` on `correctionV2`** (`Bindings/CorrectionV2.lean:61`).
   Probe: the 412-line body, option stripped and the `def` renamed into a fresh namespace, elaborated clean in
   6.3 s under the *default* 200000 heartbeats. Inherited from the frozen V1 binding (`Bindings/Correction.lean:130`)
   where it cannot be removed, but V2 is new code and can drop it. Same class as lane 026's "6 of 8 dead".
2. **`ATTEMPTS_V2.md` §7 `build_changed_lean.py` row is stale**: it records `Changed Lean modules: none —
   the lane has no commits`. With `ef6db06` committed it reports the four modules. Update the row.
3. **`ATTEMPTS_V2.md` §2 miscounts the reused `Correspondence` lemmas**: "the thirteen `rfl` …bridges and
   `energyENorm_eq`, `alpha_add_one`, `mixedLebesgueENorm_le`" (= 16). Actual: 14 declarations, **12** of them
   `:= rfl` (`energyENorm_eq` among those), plus `alpha_add_one` and `mixedLebesgueENorm_le`.
4. **"four hunks" is true of the proof body only** — `diff -u` of the two binding files is 7 hunks; the
   other three are imports, module docstring and the `Correspondence` deletion. Say "four hunks *of the
   proof body*" in both `ATTEMPTS_V2.md` §2 and `CorrectionV2.lean`'s module docstring.
5. **Branch is 7 commits behind `erenup/integration`** (merge-base `72a5dc3`), so the two-dot diff *appears* to
   revert `PLAN.md`, `logs/AGENT_RUNS.csv` and `.github/workflows/contracts.yml`. The three-dot delta is the 9 lane
   files only and the two file sets do not overlap, so the merge is conflict-free — merge or rebase, never
   force-push the two-dot state. Informational, not a lane defect.
6. **Seven lines over 100 chars** in `Bindings/CorrectionV2.lean`, all inherited verbatim from the frozen V1 binding; the repo already carries 39 such lines under `verification/`. No action.
