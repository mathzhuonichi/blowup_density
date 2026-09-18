# Lane 350-SPEC-t24-spec — produce the reconciled specification of T24 (further constructions (`prop:affine` whole-space, `prop:multiple`, `prop:conservative`)) from the lead's reconciliation of the two blind drafts

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/350-SPEC-t24-spec` (git branch `erenup/350-SPEC-t24-spec`, based on `origin/erenup/integration-section3` **after** commit 84490fdc, so `research/T24/RECONCILIATION.md` is on your base — verify with `ls research/T24/`). Read `CLAUDE.md` (contract import rules; no placeholder
`Prop`s; docstrings cite paper lines), then **the lead's decisions** `research/T24/RECONCILIATION.md` (binding), and the two blind drafts (not on your base; read them with
`git show erenup/306-SPEC-t24-draft-a:research/T24/DraftA.lean`, `git show erenup/306-SPEC-t24-draft-a:research/T24/COMPARISON_A.md`,
`git show erenup/307-SPEC-t24-draft-b:research/T24/DraftB.lean`, `git show erenup/307-SPEC-t24-draft-b:research/T24/COMPARISON_B.md`), the paper lines they cite, and the registered
vocabulary `verification/Contracts/V1/Data.lean` (`criticalOrder` `:259`, `breakdownSetIn`/`RelativelyDense` `:672-712`, `CompletedDenseVia`/`CompletedDense`/`CompletedDenseHomogeneous`
`:732-750`, `energyENorm` §5, `IsSobolevPath` `:174`, `IsHomogeneousPath` `:375`), `Contracts/V1/InsertionFamily.lean` (the R42 record), `Contracts/V2/InsertionLifespan.lean`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. No proofs, no edits to existing modules; new files only.
- **Follow the reconciliation's decisions exactly** (field names, parametric shapes, `q : ℝ≥0∞` with `(q = 1 ∨ q = 2)`, threshold `criticalOrder q.toReal`, which conjuncts to keep/drop).
  Where the reconciliation says "check `rfl`" (registered abbreviations vs `CompletedDenseVia`), verify it with an `example … := rfl` in the spec file and report.

## Deliverables
1. `research/T24/DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md`, `REPORT_306.md`, `REPORT_307.md` copied verbatim from the two branches (provenance).
2. `research/T24/Spec.lean`: the reconciled statement — one `structure` in a `Draft`-style namespace, every field with a docstring citing the cited paper file and line (`03-torus.tex:<line>`, `01-introduction.tex:<line>`) and the exact
   quantifier order; **elaborates** (`cd verification && lake env lean ../research/T24/Spec.lean`, 0 errors); plus the `rfl` checks above and a "non-vacuity" comment per field.
3. `research/T24/COMPARISON.md`: merged paper-clause → Lean field table with A/B provenance and the reconciliation's rulings; §"Proof dependencies" copied from the reconciliation;
   §"Open questions for the owner".
4. Report in four parts; write it to `research/T24/REPORT_350.md`; commit on your branch.

## T24-specific instructions (binding)
- **Three structures, two domains** (`research/T24/RECONCILIATION.md` §3): `AffineVariationAPI` is the **whole-space** statement — import `Contracts.V1.Packet` (`PacketAPI`, `navierStokesResidual`,
  `SpeedUnboundedAtOne`, `energyENorm`) and copy T14's `PacketImportAPI` only; do not copy T10/T13/T15 for it. `MultipleRegionsAPI` (Type-valued) and `ConservativeForcingAPI` (`Prop`) are on the
  torus: `import Contracts.V1.TorusData`, copy verbatim (T13 copy policy, delimited blocks, own namespaces) the unregistered T10 solution-class declarations, T14, T15's `PlacementData`/rescaled
  fields/`ScalingAPI` fields you use; cylinder / ball family / `ν, T, N` as **parameters**, with the `placement_chart` field pinning T15's chart ball to `B_j`.
- **The fixes from §2 are mandatory**: `zero_from_rest` concludes `∀ t ∈ Ico 0 T, …` (not full-function equality); supports measured inside `fundamentalCube` (T15's `*_singleCopy` shape), never
  `tsupport ⊆` a single ball for a periodic field; `affineCkSeminorm` as an `ℝ≥0∞` `⨆` (never a real `sSup`); no `−∇φ ∈ forceClassT` hypothesis; dissipation `:719` as an equality, energy `:718` as `≤`;
  `M, D` from the packet's `energyBound`/`dissipationBound`; no new constants; bounded-domain/no-slip clauses omitted with a docstring note (out of V1 scope).
- Every field: docstring with the paper line, exact quantifier order, non-vacuity note, and the integrability/class guards that make the Bochner integrals honest.
- Report the elaboration of `research/T24/Spec.lean` and the `rfl` checks against registered spellings; do not prove anything.

## Anti-stub clause (added after lane 343 was discarded)
Lane 343 (gpt-6-astra, low effort) delivered an 84-line `Spec.lean` whose fields were `True`, whose seminorm was `def ck … := 0`, and whose
"distinct" clause was `b₁ ≠ b₂ → b₁ ≠ b₂`. That is exactly what CLAUDE.md hard rule 3 forbids (no placeholder `Prop` fields) and it was thrown
away unread by any reviewer. Your `Spec.lean` must carry **every clause of the three propositions as a concrete statement** in the registered
vocabulary: every field mentions the objects it constrains (no field may be `True`, `∃ x, True`, a tautology, or a definition that ignores its
arguments); every definition is the paper's formula (`affineCkSeminorm` is the `ℝ≥0∞` supremum over the cited derivatives, etc.). Expect a
file comparable in size to the union of the two drafts' relevant parts (Draft A 980 lines, Draft B 1256 lines; the reconciliation keeps
B as the base). Before reporting, print `grep -nE ': *True|:= *0$|→ *True' research/T24/Spec.lean` and confirm it is empty.
