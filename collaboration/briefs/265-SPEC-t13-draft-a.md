# Lane 265-SPEC-t13-draft-a — Section 3 node T13 "uniform localization of fractional norms" (lem:localization): double-blind draft A of the Lean statements

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/265-SPEC-t13-draft-a` (git branch `erenup/265-SPEC-t13-draft-a`, based on `origin/erenup/integration`). One of two **independent, mutually
invisible** drafts (rule 2 of `CLAUDE.md`): **do NOT read** `research/T13/`, `research/T10/`, or `collaboration/briefs/` entries for other T13/T10 lanes. T13 is the genuinely new analysis of
Section 3 (no Section 4 counterpart): it lets the ℝ³ packet/correction/scaling contracts (I01/I02/I03) be transported to T³.

Read: `CLAUDE.md` (contract rules; no placeholder `Prop`s; docstrings cite paper lines), `collaboration/SECTION3_PLAN.md` §1 (representation decision: physical layer = periodic functions
on ℝ³; analysis on the coefficient side `lp (Fin 3 → ℤ) 2` with weight `(1+4π²|k|²)^{s/2}`; homogeneous version with `|2πk|^{s}`) and the T13 row of §3, the paper
`paper/sections/03-torus.tex:21-60` (`sec:packet`, Lemma `lem:localization`: the Gagliardo/Slobodeckij double-integral identity `I_R(f) = c_s ‖f‖²_{Ḣ^s(ℝ³)}` for `0 < s < 1`, its torus
analogue `I_T`, the kernel `K_s`, the lattice tail sums, and the display `eq:localization`: for `f` supported in a small ball, the torus and whole-space fractional norms of the
periodization agree up to constants uniform in the support radius — read the exact statement, constants and hypotheses), `02-preliminaries.tex:55-80` (the homogeneous norms on ℝ³ and T³),
the registered ℝ³ vocabulary `verification/Contracts/V1/Data.lean` (`RealVectorSobolev`, `IsSobolevDatum`, `sobolevENorm` `:150-260`; `IsHomogeneousDatum`, `forceHomogeneousENorm` `:375-410`)
and `Contracts/V1/HomogeneousNorm.lean` (`dotHomogeneousENorm`), Section 4's D01 homogeneous machinery heads (`formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean`,
`HomogeneousNorm.lean` — `grep -nE "^(def|structure|theorem) "`), and the local periodic layer heads (`Paper1/PeriodicSobolev.lean`, `PeriodicSobolevHilbert.lean`, `TorusCube.lean`:
`torusLift`, `integral_torusLift`, Parseval).

## Deliverables (statements only, no proofs)
1. `research/T13/DraftA.lean` (create the directory): a file that **elaborates** (`cd verification && lake env lean ../research/T13/DraftA.lean`) with: the Gagliardo double integral `I_R s f`
   on ℝ³ and `I_T s f` on the torus (as integrals over the cube against the periodized kernel, or over `UnitAddTorus` via `torusLift` — say which and why), the kernel `K_s` and its lattice
   tail sum, the constant `c_s`, and `structure LocalizationAPI` whose fields are exactly the clauses of `lem:localization`: (i) `I_R s f = c_s · ‖f‖²_{Ḣ^s(ℝ³)}` (homogeneous ℝ³ norm in the
   registered datum vocabulary), (ii) `I_T s f = c_s · ‖f‖²_{Ḣ^s(T³)}` (coefficient-side homogeneous norm), (iii) the localization inequality/identity `eq:localization` with its uniform
   constant and the support hypothesis exactly as the paper states, (iv) any rider (which `s` range; vector vs scalar). Docstrings cite `03-torus.tex:<line>`; exact quantifier order.
   Local verbatim definitions flagged "needs registration" for anything absent from the registered vocabulary.
2. `research/T13/COMPARISON_A.md`: paper-clause → Lean field table; choices (how the periodization/support-in-a-ball hypothesis is rendered; scalar vs vector; the exact constant
   normalization); ambiguities; "needs a lemma" list.
3. Commit on your branch (never push/merge/rebase). Report in four parts; write it to `research/T13/REPORT_265.md`.
