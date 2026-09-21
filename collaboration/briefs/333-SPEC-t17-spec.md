# Lane 333-SPEC-t17-spec — produce the reconciled specification of T17 (bounds for the background correction (`lem:correction`)) from the lead's reconciliation of the two blind drafts

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/333-SPEC-t17-spec` (git branch `erenup/333-SPEC-t17-spec`, based on `origin/erenup/integration-section3`). Read `CLAUDE.md` (contract import rules; no placeholder
`Prop`s; docstrings cite paper lines), then **the lead's decisions** `research/T17/RECONCILIATION.md` (binding), and the two blind drafts (not on your base; read them with
`git show erenup/294-SPEC-t17-draft-a:research/T17/DraftA.lean`, `git show erenup/294-SPEC-t17-draft-a:research/T17/COMPARISON_A.md`,
`git show erenup/295-SPEC-t17-draft-b:research/T17/DraftB.lean`, `git show erenup/295-SPEC-t17-draft-b:research/T17/COMPARISON_B.md`), the paper lines they cite, and the registered
vocabulary `verification/Contracts/V1/Data.lean` (`criticalOrder` `:259`, `breakdownSetIn`/`RelativelyDense` `:672-712`, `CompletedDenseVia`/`CompletedDense`/`CompletedDenseHomogeneous`
`:732-750`, `energyENorm` §5, `IsSobolevPath` `:174`, `IsHomogeneousPath` `:375`), `Contracts/V1/InsertionFamily.lean` (the R42 record), `Contracts/V2/InsertionLifespan.lean`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. No proofs, no edits to existing modules; new files only.
- **Follow the reconciliation's decisions exactly** (field names, parametric shapes, `q : ℝ≥0∞` with `(q = 1 ∨ q = 2)`, threshold `criticalOrder q.toReal`, which conjuncts to keep/drop).
  Where the reconciliation says "check `rfl`" (registered abbreviations vs `CompletedDenseVia`), verify it with an `example … := rfl` in the spec file and report.

## Deliverables
1. `research/T17/DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md`, `REPORT_294.md`, `REPORT_295.md` copied verbatim from the two branches (provenance).
2. `research/T17/Spec.lean`: the reconciled statement — one `structure` in a `Draft`-style namespace, every field with a docstring citing the cited paper file and line (`03-torus.tex:<line>`) and the exact
   quantifier order; **elaborates** (`cd verification && lake env lean ../research/T17/Spec.lean`, 0 errors); plus the `rfl` checks above and a "non-vacuity" comment per field.
3. `research/T17/COMPARISON.md`: merged paper-clause → Lean field table with A/B provenance and the reconciliation's rulings; §"Proof dependencies" copied from the reconciliation;
   §"Open questions for the owner".
4. Report in four parts; write it to `research/T17/REPORT_333.md`; commit on your branch.

## T17-specific instructions (binding)
- **Vocabulary**: `import Contracts.V1.TorusData` (+ `Contracts.V1.Correction`, `Contracts.V2.Correction`, `Contracts.V1.Scaling` for `alpha` and spelling checks) and use the registered names; copy verbatim
  (T13 copy policy, delimited blocks with source-line markers, own namespaces `BlowupDensity.T10.Draft` / `BlowupDensity.T16.Draft` / `BlowupDensity.T13.Spec` / `BlowupDensity.T15.Spec`) only the still-unregistered
  T10 solution-class declarations, T16's `CutoffData`/`LocalPotentialAPI`, T13's `LocalizationAPI` (+ its defs), and T15's `PlacementData` and rescaled fields you use.
- **Structures and fields exactly as `research/T17/RECONCILIATION.md` §3** (base B with the five A imports; `CorrectionAPI` Type-valued with the profile constants as real data fields and bounds as
  `ENNReal.ofReal (C · ε^…)`; parameter `place : PlacementData P`; the manuscript cylinder `Icc (−2) 2 ×ˢ closedBall 0 θRadius`; `𝒜_ε` bound to T16's potential through the chart; B's two profile
  identities; T16/T13 witnesses as fields; `eq:derivativebounds`, `eq:wE`, `eq:Hmixed` with the registered `Contracts.V1.alpha` and `[Fact (1 ≤ p)], 1 ≤ q` quantifiers, `eq:HHs` with the
  `MemForceSobolevT 1 s` guard; support measured on the torus lift with the open-ball force support; `ball_in_chart`, `eps_le_placement`); A's `force_exponent_identity` as a drift `example`, not a field.
- **No junk-value traps**: every norm identity/bound guarded as the reconciliation prescribes; say in each docstring which guard makes the Bochner integrals honest.
- Report the elaboration of `research/T17/Spec.lean` and the `rfl` checks; do not prove anything.
