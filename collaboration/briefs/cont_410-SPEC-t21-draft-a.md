# Lane 410-SPEC-t21-draft-a — CONTINUATION (the previous run died with HTTP 429 after substantial work)

Your previous run on this lane was cut off by an API rate limit. The worktree `/data_8T/ping/blowup_density/.claude/worktrees/410-SPEC-t21-draft-a` (branch
`erenup/410-SPEC-t21-draft-a`) contains **uncommitted partial work** under `research/T21/` (`git status --short`; read `research/T21/DraftA.lean` and any `COMPARISON_A.md`
first). Continue from it — keep what elaborates, finish the missing structures/fields and the comparison table — and follow the original brief below to the end (elaboration
with 0 errors, `COMPARISON_A.md` covering every clause, commit, four-part report to `research/T21/REPORT_410.md`). Still double-blind: do not read the other T21 lane.

---

# Lane 410-SPEC-t21-draft-a — Section 3 node T21 "main assembly" (`thm:main` (i)+(ii), `cor:nondensity`): double-blind draft A of the Lean statements

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/410-SPEC-t21-draft-a` (git branch `erenup/410-SPEC-t21-draft-a`, based on `origin/erenup/integration-section3`).
One of two **independent, mutually invisible** drafts (rule 2 of `CLAUDE.md`): **do NOT read** `research/T21/` or `collaboration/briefs/` entries for the other T21 lane.

Read: `CLAUDE.md` (contract rules; no placeholder `Prop`s; docstrings cite paper lines), `collaboration/SECTION3_PLAN.md` §1–§3 (the T21 row: `cor:nondensity` + `thm:main` (i)+(ii)
assembly; the open ball `{‖g‖_{L¹_t H^{1/2}} < cν}` and the monotonicity `‖·‖_{H^{1/2}} ≤ ‖·‖_{H^s}` for `s ≥ 1/2`), the paper `paper/sections/03-torus.tex:1-16` (`thm:main`,
Sobolev density threshold: (i) for every fixed `a ∈ 𝒳`, `𝓑_{ν,a,T}` is dense in `𝓕` for the relative `L¹(0,∞;H^s(𝕋))` topology when `s < 1/2`; (ii) for zero initial velocity,
`𝓑⁰_{ν,T}` dense iff `s < 1/2`), `:506-509` (`cor:nondensity`: non-density at and above the critical exponent — the small-critical-force ball of `prop:critical` misses
`𝓑⁰`), the definitions of `𝒳`, `𝓕`, `𝓑_{ν,a,T}`, `𝓑⁰_{ν,T}` in `03-torus.tex:1-60` and wherever they are introduced (grep `\\BB`, `\\FF`, `\\XX`), **the statements
and proofs of the inputs** `prop:density` (`:349-382`) and `prop:critical` (`:383-505`), and the Section 4 counterpart `paper/sections/04-whole-space.tex` `thm:main`/R41 so you
know which clauses are the same and which differ on the torus. Vocabulary — **import the registered contracts, copy the rest verbatim**:
- registered (import and use by name): `verification/Contracts/V1/TorusData.lean`, `Contracts/V1/TorusLocalTheory.lean` (`ClassicalSolutionT`, `forceClassT`, `initialClassT`,
  `RelativelyDenseT`, the mixed/Sobolev norms), `Contracts/V1/Packet.lean`/`PacketImport.lean`, and the Section 4 counterparts `Contracts/V1/MainThresholds.lean`
  (`R41.main_thresholds`, `R41.threshold_arithmetic`), `Contracts/V1/CompletedDensity.lean` — record field-for-field where the paper's proof is the same and differ exactly where the
  torus differs (say where: single critical exponent `1/2`, `q = 1` only).
- unregistered, copy verbatim (T13 copy policy: same names, namespaces, delimited blocks with provenance comments `-- copied verbatim from …:<lines>`): the T19 canonical
  structures (`research/T19/Spec.lean:192-…` `PeriodicDensityAPI`, `MixedRegionAPI`, `StrongClosureAPI`, `ProjectionAPI` — check `formalization/NSFormalization/Section3/T19/Bookkeeping.lean`
  for the canonical spellings) and the T20 canonical `CriticalRegularityTAPI` (`formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:139`, its constants and the
  `criticalRho`/ball vocabulary). Do not re-invent any of them; where a copied block overlaps a registered name add an `example … := rfl` drift check.

## Deliverables (statements only, no proofs)
1. `research/T21/DraftA.lean` (create the directory): a file that **elaborates** (`cd verification && lake env lean ../research/T21/DraftA.lean`, 0 errors). In a
   namespace `BlowupDensity.T21.DraftA`, one structure per result — `NonDensityAPI` (`cor:nondensity`: the explicit open ball in the `L¹_t H^{1/2}` norm, its radius `c ν` with
   `c` the `prop:critical` constant, membership of the zero force, the ball misses `𝓑⁰_{ν,T}`, the monotonicity clause `‖g‖_{L¹H^{1/2}} ≤ ‖g‖_{L¹H^s}` for `s ≥ 1/2` and hence
   non-density for every `s ≥ 1/2`) and `MainTheoremAPI` (`thm:main` (i) and (ii), both directions of (ii), stated with the paper's topology: density = `RelativelyDenseT`-style
   relative closure in the `L¹(0,∞;H^s)` norm on the force class — reuse the registered `RelativelyDenseT` shape if it fits, else copy and say why) — each field exactly one clause,
   docstring citing `03-torus.tex:<line>`, exact quantifier order, "non-vacuity" comment, **no junk-value traps** (integrability/class hypotheses on every norm, `ν > 0`, `T > 0`,
   `ℝ≥0∞` for norms, no real `sSup`), Type-valued when the paper has constants/data, `Prop` otherwise (say which and why), plus `def mainStatement : Prop` and
   `def nonDensityStatement : Prop` in the paper's quantifier order, and a `def mainOfInputs : PeriodicDensityAPI → CriticalRegularityTAPI → … → MainTheoremAPI`-shaped
   **signature** (just the arrow type as a `def … : Prop` or a commented shape) showing which inputs the assembly consumes.
2. `research/T21/COMPARISON_A.md`: paper-clause → Lean field table (with the Section 4 R41 counterpart field or "torus-only"); choices; ambiguities; "needs a lemma" list
   (which T19/T20/T11 fields the proof will consume, incl. the monotonicity of the `H^s` norms in `s` and how `L¹_t H^s` is spelled in `TorusLocalTheory`); implementation
   candidates (`grep -nE "^(def|structure|theorem) "` in `Section4/R41/*.lean` and the `Paper1/` modules named in the T21 row of `collaboration/SECTION3_PLAN.md`).
3. Commit on your branch (never push/merge/rebase). Report in four parts; write it to `research/T21/REPORT_410.md`.

## Quality clause
Earlier draft lanes that returned a ~100-line file with self-made stubs for the imported records, or structures of two or three fields, were **discarded**. Copy the vocabulary
verbatim; render every result clause by clause from the paper text (statement *and* proof); a draft is expected to be a few hundred lines with a table in
`COMPARISON_A.md` covering every clause. No field may be `True`, a tautology, or a definition ignoring its arguments; print
`grep -nE ': *True|:= *0$|→ *True' research/T21/DraftA.lean` (empty) in the report. Spend the time; do not stop early.
