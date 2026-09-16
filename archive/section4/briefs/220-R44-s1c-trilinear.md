# Lane 220-R44-s1c-trilinear — R44 row S1c: the `J`-weighted trilinear estimate `abs ⟪(u·∇)u, Ju⟫ ≤ C₀ · Y · (Y² + Z²)` at datum level

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/220-R44-s1c-trilinear` (git branch `erenup/220-R44-s1c-trilinear`, based on lane 218's branch `erenup/218-R44-s1a-jweight` =
`origin/erenup/integration` + `Section4/R44/JWeight.lean` (`Jmul` with `Jmul_symbol`/`Jmul_norm`; the datum bundle `JWeightDatum u f`; `Y`, `Z`, `B`; the pairing `forceJPairing`;
`weight_identity`, `force_pairing_le`)). Read that module and `research/R44/REPORT_218.md` (note the carrier-normalization remark: `RealVectorSobolev s` stores `(1+|ξ|²)^{s/2} û`),
then `research/R44/R44_SPLIT.md:53-81` (row S1c — this lane; S1b/S1d are NOT), the paper `04-whole-space.tex:150-158` (`|⟨(u·∇)u, Ju⟩| ≤ ‖u‖₃ ‖∇u‖₃ ‖Ju‖₃ ≤ C·Y·Z·(Y²+Z²)^{1/2} ≤
C₀·Y·(Y²+Z²)` via Lemma `lem:critical-embeddings`), and the R43 lane that did the homogeneous twin of this row: lane 182 `Section4/R43/Trilinear.lean` (`derivativeCriticalL3`, the
three-factor `L³` Hölder step at datum/`Lp` level, `criticalTrilinearEstimate_of_hcrit`, `trilinearConst`), lane 214 `R43/Parseval.lean` (`criticalAdvectionLpBridge_of_hcrit`),
lane 191 `R43/ShiftedData.lean`, lane 165 `A05/CriticalL3.lean` (`velocityCriticalL3`: `‖z‖₃ ≤ C·‖z‖_{Ḣ^{1/2}}`, the U6 scalar Riesz realization `u6_scalar_eLpNorm_le` for `0<a<3/2`),
the registered A05 V2 (`verification/Contracts/V2/GradientL6.lean`), lane 164 `D01/HomogeneousNorm.lean` (`dotHomogeneousENorm s ≤ sobolevENorm s`, i.e. `Ḣ^{1/2} ≤ H^{1/2}` on data —
the inequality that turns 182's homogeneous bounds into inhomogeneous `Y`, `Z`), `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P6, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (zero datum + the nonzero datum 218's audit uses).
- **Satisfiability rule:** any input you add must be a restriction of a standard property satisfiable by nonzero data; extend 218's `JWeightDatum` by a **separate** structure
  (`AdvectionJDatum`: the datum of `(u·∇)u` at the order the pairing needs, spelled like 175's `advectionHalf`/214's `criticalAdvectionLpBridge`) rather than modifying it.

## Goal (static, per slice)
`theorem advection_pairing_le (h : JWeightDatum u f) (ha : AdvectionJDatum u …) : abs (advectionJPairing …) ≤ trilinearConstJ * Y h * (Y h ^ 2 + Z h ^ 2)` with explicit positive
`trilinearConstJ`. Route: `⟨(u·∇)u, Ju⟩` as the real pairing of the advection datum with `Jmul` of the velocity datum (218's `forceJPairing` template); three-factor Hölder
`|⟨(u·∇)u, Ju⟩| ≤ ‖u‖₃ ‖∇u‖₃ ‖Ju‖₃` (182's Hölder step; `(u·∇)u = Σ_j u_j ∂_j u` componentwise); embeddings `‖u‖₃ ≤ C‖u‖_{Ḣ^{1/2}} ≤ C·Y` (165 + 164), `‖∇u‖₃ ≤ C‖∇u‖_{Ḣ^{1/2}} ≤ C·Z`
(182's `derivativeCriticalL3` + 164), `‖Ju‖₃ ≤ C‖Ju‖_{Ḣ^{1/2}} ≤ C‖Ju‖_{H^{1/2}} = C‖u‖_{H^{3/2}} = C·sqrt(Y²+Z²)` (218's `Jmul_norm` + `weight_identity`); then `Y·Z·sqrt(Y²+Z²) ≤ Y·(Y²+Z²)`
(`Z ≤ sqrt(Y²+Z²)`). Also the corollary in the paper's intermediate form `≤ C·Y·Z·sqrt(Y²+Z²)`.

## Deliverables
1. New module `formalization/NSFormalization/Section4/R44/TrilinearJ.lean` (namespace `NSFormalization.Section4.R44`).
2. Records `research/R44/ATTEMPTS_S1C.md`, update `R44_SPLIT.md` row S1c, conformance `research/R44/axioms_s1c.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R44.TrilinearJ` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R44/REPORT_220.md`.
