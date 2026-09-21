# Lane 475-T21-A-assembly-registration — T21 unit A: assemble `NonDensityAPI` / `MainTheoremAPI`, close the arrow statements and the two paper statements, register `T03.non_density` and `T03.main`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof/registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/475-T21-A-assembly-registration` (git branch `erenup/475-T21-A-assembly-registration`, = `origin/erenup/integration-section3` after lanes 472 (N0–N10, N12: `nonDensityAPI`) and 474 (N11, N13–N15: `mainTheoremAPI` over threaded
`NonDensityAPI`) merged; T19 (`T03.density`), T20 (`T03.critical_regularity`) registered).
Read `CLAUDE.md` (contract import rules; bindings by `rfl`/fieldwise conversions; `Tests` = `warningAsError`; `Prop` records assembled by `def` need `set_option linter.defProp false` as in `Section3/T19/Assembly.lean`), **`research/T21/T21_SPLIT.md`** (unit A verbatim: the three
arrow-type `Prop` definitions `nonDensityOfCritical`, `mainOfDensityAndNonDensity`, `mainOfInputs` at `Spec.lean:595,602,613`; `nonDensityStatement` `:436-438`; the two unconditional paper statements; the T19 → T20 → T21 gate), `research/T21/RECONCILIATION.md`
(lead-approved decisions: `Prop` records, T20 consumed through `maximalLifespanT_eq`), `research/T21/Spec.lean`, `research/T21/REPORT_{472,474}.md` + `Section3/T21/*.lean` (exact names of the inhabitants and which hypotheses 474 threaded), the registration pattern of
`research/T19/REPORT_470.md` + `verification/{Contracts/V1,Bindings,Tests}/Density.lean` and `research/T20/REPORT_451.md` + `CriticalRegularityT.lean`, `verification/contracts.json`, `collaboration/work_items.json` (T21 item), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first (`lake build NSFormalization.Section3.T21.Main` and the 472 modules).
- No `sorry`/`admit`/`axiom`/`native_decide`; no placeholder fields; existing `Contracts/V1/*` and `Tests/*` untouched; contract statements token-for-token the canonical/Spec ones (docstrings cite `03-torus.tex` lines).
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
1. `Section3/T21/MainAssembly.lean` (**new file** — lane 472 already owns `Section3/T21/Assembly.lean` with `nonDensityAPI K : NonDensityAPI K.c` and `nonDensityOfCritical_holds`; import it): with `K := ` the canonical T20 inhabitant (`Section3/T20/Assembly.lean`) and `D := periodicDensityAPI` (T19): theorems inhabiting the three arrow statements under fresh names (`nonDensityOfCritical_holds`, `mainOfDensityAndNonDensity_holds`,
   `mainOfInputs_holds`), the closed records `Nonempty (NonDensityAPI K.c)` and `Nonempty MainTheoremAPI`, the witness-independent `∃ c, Nonempty (NonDensityAPI c)`, and the two unconditional paper statements (`nonDensityStatement` and the `thm:main` statement as the Spec spells
   them). Non-vacuity: the records' fields are `∀`-statements over registered classes with an explicit `c = criticalSmallnessH1`; add `research/T21/probes/assembly_closes.lean` reading off `zeroInitialNonDensity 1 1 1` and `fixedInitialDensity` at the zero datum.
2. Contract trios `verification/Contracts/V1/TorusNonDensity.lean` and `verification/Contracts/V1/TorusMain.lean` (records + statements token-for-token; `TorusMain` may import `TorusNonDensity` and the registered `Density`/`CriticalRegularityT` contracts), `Bindings/TorusNonDensity.lean`,
   `Bindings/TorusMain.lean`, `Tests/TorusNonDensity.lean`, `Tests/TorusMain.lean`; registry entries `T03.non_density` and `T03.main` (`version: 1`, `parent_task: "T03"`, honest `scope`: what `thm:main` asserts here (T19 density + T20 critical regularity → the zero-datum
   density iff `s < 1/2`, non-density for `s ≥ 1/2`), what is excluded per `RECONCILIATION.md`), `work_items.json` T21 `contracts`, `python3 experiments/tasks.py render`.
Deliverables: modules, probe, `research/T21/axioms_a.lean`, `research/T21/ATTEMPTS_A.md`, A status line in `T21_SPLIT.md`.

## Gates
`lake build NSFormalization.Section3.T21.Assembly`, `make check`, `make test` (new `checked…` lines: standard axioms only), `make test-mutations`, `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` (registered count +2, `base_compatibility_checked: true`),
the probe, the axioms file.

## Report
Commit on your branch; end with four parts (what was registered with exact statements / files / gaps / commands and results). Also write it to `research/T21/REPORT_475.md`.

## Lead note (2026-09-19 16:03Z) — module ownership and duplicates
Your worktree = lane 472's branch (nine modules `Section3/T21/{Definitions,CriticalBridge,OrderLowering,ForceMonotonicity,Zero,Ball,Disjointness,NonDensity,Assembly}.lean`) + lane 474's branch (`Section3/T21/Main.lean`: `thresholdValue`, `zeroInitialClass`, `fixedInitialDensity D`, `zeroInitialDensityIff D nonDensity`, `zeroInitialNonDensity nonDensity`, `mainTheoremAPI D nonDensity`, `mainOfDensityAndNonDensity_holds D nonDensity`) + integration. The two lanes ran in parallel: **check for duplicate declarations** (`zeroInitialClass` appears in both; 474 unfolded `breakdownSetTZero` locally). You may edit `Main.lean` for exactly this dedupe (delete its duplicate, import 472's module, keep statements unchanged) — record it in `ATTEMPTS_A.md`. The adapter 474 asks for: `fun _c D (N : NonDensityAPI _c) => mainOfDensityAndNonDensity_holds D N.nonDensity`. No other edits to existing modules.
