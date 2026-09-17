# Lane 295-SPEC-t17-draft-b — Section 3 node T17 "bounds for the background correction" (`lem:correction`): double-blind draft B of the Lean statements

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/295-SPEC-t17-draft-b` (git branch `erenup/295-SPEC-t17-draft-b`, based on `origin/erenup/integration-section3`). One of two **independent, mutually
invisible** drafts (rule 2 of `CLAUDE.md`): **do NOT read** `research/T17/` or `collaboration/briefs/` entries for other T17 lanes. T17 is the torus
counterpart of the second half of Section 4's I02 (registered contracts `I02.correction`, `I02.correction_v2`); T18 (`thm:insertion`) consumes it.

Read: `CLAUDE.md` (contract rules; no placeholder `Prop`s; docstrings cite paper lines), `collaboration/SECTION3_PLAN.md` §1–§3 (representation decision
(b) and the T17 row), the paper `paper/sections/03-torus.tex:176-286` in full — `lem:potential` `:176-217` (context: the divergence-free cutoff
`w_ε = -∇×(η_ε θ_ε A)`, `eq:potential`, `eq:cutoff`, `eq:bgzero`) and **Lemma `lem:correction` `:218-286`** with its proof: the rescaled profile
uniformly smooth on a fixed cylinder ⇒ `eq:derivativebounds` (`:226-233`: the derivative bounds on `w_ε` with the exact powers of `ε`), `eq:wE`
(`‖w_ε‖_{E_T} ≤ C ε^{3/2}`), `eq:Hmixed` (`:235-238`: the mixed-norm bound on the correction force `H_ε` of `eq:H` `:219-223`, `= C_{p,q} ε^{α(p,q)+1}`),
`eq:HHs` (`:239-241`: `L¹_t H^s_x` bound for `0 ≤ s ≤ 1`, via `lem:localization`). Read the exact displays, constants, quantifier order, and which
quantities depend on `ε`, `T`, `p`, `q`, `s`. Then the reconciled Section 3 vocabulary these statements must be written in: `research/T10/Spec.lean`
(`IsPeriodicSpatial`/`IsPeriodicOn`, `torusLift`, `periodicSobolevENorm` — with lead amendment 1's integrability conjunct, `research/T10/RECONCILIATION.md` §5 —
`forceSobolevENormT`, `energyEssSupT`/`energyGradientT`/`energyENormT`), `research/T16/Spec.lean` (`CutoffData`, `LocalPotentialAPI`: the correction
`w_ε` = `D.correction ε` and its properties — **reuse these, do not restate the cutoff**), `research/T13/Spec.lean` (`LocalizationAPI`, for `eq:HHs`),
and `research/T15/` is **not** available to you (T15 is being drafted in parallel); where `eq:Hmixed` needs the rescaled packet fields, state them as
parameters with the exact hypotheses the lemma uses (uniform smoothness of the profile on the fixed cylinder) — say so. Registered Section 4 shapes to mirror:
`verification/Contracts/V1/Correction.lean` and `Contracts/V2/Correction.lean` (find through `verification/contracts.json` entries `I02.correction`,
`I02.correction_v2`; read every field: how the ℝ³ version packages the constants, the `ε` range, the derivative bounds, the mixed norms, `α(p,q)`).
Also skim `formalization/NSFormalization/Paper1/Correction*.lean` and `PeriodicCorrectionEndpointRates.lean` heads (`grep -nE "^(def|structure|theorem) "`) for
implementation candidates to cite (not to import).

## Deliverables (statements only, no proofs)
1. `research/T17/DraftB.lean` (create the directory): a file that **elaborates** (`cd verification && lake env lean ../research/T17/DraftB.lean`).
   Begin with the same imports as `research/T10/Spec.lean` (+ the `Contracts.V1/V2.Correction` files if you cite them) and copy **verbatim** (same names, namespaces
   `BlowupDensity.T10.Draft` / `BlowupDensity.T16.Draft` / `BlowupDensity.T13.Draft`, marked `-- copied from research/T1x/Spec.lean:LINE; delete once registered`) only the
   declarations you use. Then, in a namespace `BlowupDensity.T17.DraftB`, state: the correction force `H_ε` of `eq:H` as an explicit `def` from the cutoff data
   and the rescaled fields (exact terms, exact signs), and `structure CorrectionAPI` (Type-valued with the constants as data fields — house style of A03/A05/I02 — or
   `Prop` with `∃ C`; say which and why) whose fields are exactly the clauses of `lem:correction`: `eq:derivativebounds` (each bound as stated, with the `ε` powers),
   `eq:wE`, `eq:Hmixed` (for all `1 ≤ p, q ≤ ∞` with `α(p,q)` explicit; equality or `≤` exactly as the paper writes it), `eq:HHs` (`0 ≤ s ≤ 1`), with the hypothesis
   "the profile is uniformly smooth on the fixed cylinder" rendered exactly (which cylinder, which norms bounded uniformly in `ε`). Every field: docstring citing
   `03-torus.tex:<line>`, exact quantifier order, "non-vacuity" comment, **no junk-value traps** (norm bounds carry the integrability/`MemLp` hypotheses or are stated
   for smooth compactly supported fields where that is automatic — say which).
2. `research/T17/COMPARISON_B.md`: paper-clause → Lean field table (with the `I02.*` counterpart field for each); choices; ambiguities; "needs a lemma" list;
   implementation candidates in `Paper1/`.
3. Commit on your branch (never push/merge/rebase). Report in four parts; write it to `research/T17/REPORT_295.md`.
