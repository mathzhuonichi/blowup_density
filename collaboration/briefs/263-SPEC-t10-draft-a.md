# Lane 263-SPEC-t10-draft-a — Section 3 (torus T³), node T10 "periodic data layer": double-blind draft A of the contract statements (`Contracts/V1/TorusData.lean` to be)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/263-SPEC-t10-draft-a` (git branch `erenup/263-SPEC-t10-draft-a`, based on `origin/erenup/integration`). This is one of two **independent,
mutually invisible** drafts (rule 2 of `CLAUDE.md`): **do NOT read** `research/T10/`, `collaboration/briefs/` entries for other T10 lanes, or any file mentioning "T10 draft".
Section 3 is the torus version of Section 4; the design decision is fixed by the lead in `collaboration/SECTION3_PLAN.md` §1 (read it first): keep the local periodic-functions-on-ℝ³
physical layer (P) and put all analysis on the **coefficient side** `lp (Fin 3 → ℤ) 2` with weight `(1 + 4π²|k|²)^{s/2}`, mirroring Section 4's D01 "datum" architecture
(`verification/Contracts/V1/Data.lean:150-260`: `IsSobolevDatum`, `RealVectorSobolev`, `sobolevENorm`, `forceSobolevENorm`, the classes `initialClassR`/`forceClassR`, `breakdownSetIn`,
`RelativelyDense`, `ClassicalSolutionR`, `maximalLifespanR` — read these as the **template** to be copied with T³ in place of ℝ³).

Read: `CLAUDE.md` (contract import rules: `Contracts/*` import only `Mathlib`/`Contracts.*`; docstrings cite paper lines; no placeholder `Prop`s), `collaboration/SECTION3_PLAN.md`
§1, §2 (reuse map), the T10 row of §3, §4, the paper `paper/sections/03-torus.tex` (the setup: function spaces on T³, `X_T`/`F_T`, the breakdown set, the relative topology, mean-zero
decomposition, periodic Leray projector, the pressure normalization `∫ p = 0`, the energy space `E_T`, the classical-solution and maximal-lifespan definitions — grep the labels
`sec:torus`, `eq:T*`, `def:*`, `prop:local`; and `02-preliminaries.tex:1-60` for the shared definitions), the local periodic interfaces you may **reference but not modify**:
`formalization/NSFormalization/Paper1/PeriodicSobolev*.lean`, `PeriodicForceSpace.lean`, `PeriodicMeanZero.lean`, `PeriodicLeray*.lean`, `PeriodicPressureNormalization.lean`,
`PeriodicHeatMultiplier.lean` (their `def`/`structure` heads and docstrings only — `grep -nE "^(def|structure|abbrev|noncomputable def) "`), `Paper1/TorusCube.lean` (`torusLift`,
`integral_torusLift`, Parseval — the bridge to `UnitAddTorus (Fin 3)`), and Mathlib's `lp`/`ZLattice`/`Fourier` names you use (`#check` them).

## Deliverables (statements only, no proofs)
1. `research/T10/DraftA.lean` (create the directory): a file that **elaborates** (`cd verification && lake env lean ../research/T10/DraftA.lean`, 0 errors) with: (a) the coefficient carrier
   `PeriodicSobolev s` (weighted `ℓ²(ℤ³)`, real vector-valued: three components) and its norm; (b) `IsPeriodicDatum s (z : physical periodic field) (A : PeriodicSobolev s) : Prop` — the datum
   bridge (Fourier coefficients of `z` are `A` up to the weight; say exactly which local definition of Fourier coefficient on (P) you refer to, or define it verbatim from `TorusCube`);
   (c) `periodicSobolevENorm s z : ℝ≥0∞` as the infimum over data; (d) the mean `meanT z`, the mean-zero subspace (`k = 0` coefficient zero) and the decomposition; (e) the periodic Leray
   projector on data (identity at `k = 0`, `I − k⊗k/|k|²` otherwise) and solenoidality; (f) the pressure gauge `∫ p = 0`; (g) the classes `initialClassT`, `forceClassT` (paper's `X_T`,
   `F_T`), the force norms `forceSobolevENormT q s`, `ClassicalSolutionT ν a f T` (fields mirroring `ClassicalSolutionR` with periodicity and the pressure gauge), `maximalLifespanT`,
   `breakdownSetT`, `RelativelyDenseT`, and `energyENormT`; each with a docstring citing `03-torus.tex:<line>` (or `02-preliminaries.tex:<line>`) and the exact quantifier order.
2. `research/T10/COMPARISON_A.md`: paper notion → Lean definition table; every choice (weight normalization `2π`, real vs complex coefficients, how periodicity of the physical field is
   stated, whether `ClassicalSolutionT` is a new structure or reuses a local one); ambiguities; and a list "needs a lemma" (facts T11+ will need from this layer: Parseval, the Leray
   projector is a contraction, mean-zero is preserved by the equation, …).
3. Commit on your branch (never push/merge/rebase). Report in four parts; write it to `research/T10/REPORT_263.md`.
