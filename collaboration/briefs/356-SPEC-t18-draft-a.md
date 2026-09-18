# Lane 356-SPEC-t18-draft-a — Section 3 node T18 `thm:insertion` (exact local insertion on the torus): double-blind draft A of the Lean statement

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/356-SPEC-t18-draft-a` (git branch `erenup/356-SPEC-t18-draft-a`, based on `origin/erenup/integration-section3`).
One of two **independent, mutually invisible** drafts (rule 2 of `CLAUDE.md`): **do NOT read** `research/T18/` or `collaboration/briefs/` entries for the other T18 lane (357-SPEC-t18-draft-b).
T18 = Theorem `thm:insertion` (`03-torus.tex:287-311`, proof `:312-346`): the rescaled, periodized packet is inserted exactly into the corrected background on one chart; the inserted
force `g_ε` stays in the force class, the solution's maximal lifespan is exactly `T` (T11 uniqueness + `H² ↪ L^∞`), the two cross transport terms vanish identically, and the closeness
rates `eq:Eclose` / `eq:Fclose` / `eq:Hsclose` (`:300-306`) hold; the decomposition is `eq:insertion` (`:314`).

Read: `CLAUDE.md` (contract rules; no placeholder `Prop`s; docstrings cite paper lines), `collaboration/SECTION3_PLAN.md` §1–§3 (the T18 row: R42 is the same proof skeleton), the paper
`paper/sections/03-torus.tex:99-346` in full (the statement **and** the proof of `thm:insertion`, plus `prop:scaling` `:122-175`, `lem:potential` `:176-217`, `lem:correction` `:218-286`
so that you know which objects the theorem takes from them). Then the vocabulary the statement must be written in — **import the registered contracts, copy the rest verbatim**:
- registered: `verification/Contracts/V1/TorusData.lean` (T10 data layer) and `verification/Contracts/V1/TorusLocalTheory.lean` (T10 solution classes `ClassicalSolutionT`, `maximalLifespanT`,
  `RegularThroughT`, `breakdownSetT`, `forceClassT`, `initialClassT`, energy norms, and the four T11 APIs incl. `PeriodicLocalTheoryAPI`, `PeriodicContinuationH3API`) — import and use their names;
  `Contracts/V1/Packet.lean` (the whole-space packet); for the shape of the statement, Section 4's registered `Contracts/V1/InsertionFamily.lean` (`InsertionFamilyAPI`, the R42 record:
  formulas, smoothness, initial, incompressible, momentum, history, difference supports, blowup, energyRate, forceConvergence) and `Contracts/V2/InsertionLifespan.lean` — read every field;
  the torus statement should mirror this record field-for-field where the paper's proof is the same, and differ exactly where the torus proof differs (say where).
- unregistered, copy verbatim (T13 copy policy: same names, namespaces, delimited blocks with provenance comments `-- copied verbatim from research/T17/Spec.lean:<lines>`):
  `research/T17/Spec.lean` already bundles the T13/T14/T15/T16 vocabulary blocks (`LocalizationAPI`, `PacketEnergyAPI`/`PacketImportAPI`, `PlacementData`, `ScalingAPI`, `CutoffData`,
  `LocalPotentialAPI`) and defines `CorrectionAPI` (`:752`) — copy exactly the declarations you use; `research/T12/Spec.lean` (`MeanZeroSobolevCalculusAPI`, `:287`, for `H² ↪ L^∞` =
  `boundedRepresentative`); do not re-invent any of them and do not copy anything already registered (drift check: an `example … := rfl` against the registered spelling where the copied
  block overlaps a registered name).

## Deliverables (statements only, no proofs)
1. `research/T18/DraftA.lean` (create the directory): a file that **elaborates** (`cd verification && lake env lean ../research/T18/DraftA.lean`, 0 errors). In a namespace
   `BlowupDensity.T18.DraftA`, one structure `PeriodicInsertionAPI` (Type-valued, taking as parameters the packet import, placement, scaling and correction records the paper's
   proof takes as given — decide and justify which are parameters vs fields) whose fields are exactly the clauses of `thm:insertion`: the inserted triple `(u_ε, p_ε, g_ε)` with its
   formulas (`eq:insertion`), the class memberships (`g_ε ∈ forceClassT`, initial datum in `initialClassT`), the classical solution on the torus with **maximal lifespan exactly `T`**,
   the two vanishing cross transport terms as explicit identities, the breakdown/blow-up clause, and the three closeness rates with their exact exponents `ε^{1/2}`, `ε^{3/2}`,
   `ε^{α(p,q)+1}`, `0 ≤ s < 1/2` and the norms they are measured in (T10's torus energy / mixed / Sobolev norms as spelled in the registered contract). Every field: docstring citing
   `03-torus.tex:<line>`, exact quantifier order, "non-vacuity" comment, **no junk-value traps** (integrability/class hypotheses on every norm; `ν > 0`; `ε ∈ Ioc 0 ε₀`).
   Also `def periodicInsertionStatement : Prop` with the paper's quantifier order (`∀ ν > 0, ∀ packet/placement/…, ∃ ε₀ > 0, Nonempty (PeriodicInsertionAPI …)`).
2. `research/T18/COMPARISON_A.md`: paper-clause → Lean field table with the R42 counterpart field for each (or "torus-only"); choices; ambiguities; "needs a lemma" list
   (which T11/T12/T13/T15/T16/T17 fields the proof will consume); implementation candidates (`grep -nE "^(def|structure|theorem) " formalization/NSFormalization/Paper1/PeriodicInsertion*.lean
   Paper1/PeriodicCrossComponentTransport*.lean`).
3. Commit on your branch (never push/merge/rebase). Report in four parts; write it to `research/T18/REPORT_356.md`.

## Quality clause
Earlier draft lanes that returned a ~100-line file with self-made stubs for the imported records, or structures of two or three fields, were **discarded**. Copy the T15/T16/T17
vocabulary verbatim; render the theorem clause by clause from the paper text (statement *and* proof); every hypothesis and every conclusion gets its own field with the paper line;
a draft is expected to be several hundred lines with a table in `COMPARISON_A.md` covering every clause. No field may be `True`, a tautology, or a definition ignoring its
arguments; print `grep -nE ': *True|:= *0$|→ *True' research/T18/DraftA.lean` (empty) in the report. Spend the time; do not stop early.
