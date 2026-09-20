# Lane 218-R44-s1a-jweight — R44 row S1a: the `J = (I-Δ)^{1/2}` weight identity `‖u‖²_{H^{3/2}} = Y² + Z²` and the force duality `abs ⟪f, Ju⟫ ≤ B·sqrt(Y²+Z²)` at datum level

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/218-R44-s1a-jweight` (git branch `erenup/218-R44-s1a-jweight`, based on `origin/erenup/integration`). Read `CLAUDE.md`,
`collaboration/HANDOFF.md` §0 and §2 P6, `research/R44/R44_SPLIT.md:53-81` (row S1a — this lane; S1b–S1d are NOT this lane), `research/R44/Spec.lean` (the `RCritical2API` vocabulary:
how `Y`, `Z`, `B` are spelled), `research/R44/REVIEW_166-R44-split.md`, the paper `04-whole-space.tex:145-164` (`Y = ‖u‖_{H^{1/2}}`, `Z = ‖∇u‖_{H^{1/2}}`, `B = ‖f‖_{H^{-1/2}}`; "Fourier
weights give `‖u‖²_{H^{3/2}} = Y² + Z²`"; "`|⟨f, Ju⟩| ≤ B (Y²+Z²)^{1/2}`" by Fourier Cauchy–Schwarz), the R43 analogues that did the same kind of datum-level work in the **homogeneous**
scale: lane 214 `Section4/R43/Parseval.lean` (`half_order_parseval`, `component_real_pairing`, `pairing_identity_of_hcrit` — real pairings via Fourier data), lane 191
`Section4/R43/ShiftedData.lean` (order-shifted data of `∇u`: components `ξ_j û`), lane 175 `Section4/R43/CriticalPairing.lean` (pairing definitions), and D01's datum carrier
(`Section4/D01/`: `RealVectorSobolev s`, `RealSobolevHilbert s`, `FourierData`, `sobolevENorm`, `IsSobolevDatum` — check whether the order `s : ℝ` may be negative, i.e. whether
`RealVectorSobolev (-1/2)` is the `H^{-1/2}` force carrier the split's G3 asks for; grep `Section4/D01` and `Paper1/` for "negative order"/"dual"), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (zero datum, and a nonzero Schwartz-type datum if cheap).
- **Satisfiability rule:** any named input left open must be a restriction of a standard property satisfiable by nonzero data, stated exactly, ONE structure; consumers copy your binders.

## Goal (static, per slice — no time paths, no PDE)
1. `def Jmul {s : ℝ} : RealVectorSobolev s → RealVectorSobolev (s - 1)` (or the scalar version on `RealSobolevHilbert`), the Fourier multiplier `(1 + |ξ|²)^{1/2}` on data, with
   `Jmul_symbol : ((Jmul v) i : FourierData) =ᵐ fun ξ => ((1 + ‖ξ‖²)^(1/2) : ℂ) * (v i) ξ` and the isometry `‖Jmul v‖_{H^{s-1}} = ‖v‖_{H^s}` (or the `sobolevENorm` version).
2. `weight_identity`: for a datum `u` at order `3/2` with gradient data `∇u` at order `1/2` (191's shifted data: components `ξ_j û`), `sobolevENorm (3/2) u ^ 2 = Y² + Z²` where
   `Y := sobolevENorm (1/2) u`, `Z² := Σ_j sobolevENorm (1/2) (∂_j u) ^ 2` (spell `Z` exactly as `Spec.lean`/the split does; if they use `‖∇u‖_{H^{1/2}}` as one vector norm, prove
   the two spellings equal). Proof: `(1+|ξ|²)^{1/2}·(1 + |ξ|²) = (1+|ξ|²)^{3/2}` under the integral.
3. `force_pairing_le`: `abs ⟪f, Ju⟫ ≤ B * sqrt (Y² + Z²)` with `B := ‖f‖_{H^{-1/2}}` — the real pairing at datum level (214's `component_real_pairing` style) and Cauchy–Schwarz
   between weights `(1+|ξ|²)^{-1/4}` and `(1+|ξ|²)^{1/4}`. If the `H^{-1/2}` carrier does not exist in the tree, define the order-`(-1/2)` datum norm on `FourierData` directly
   (`∫ (1+|ξ|²)^{-1/2} |f̂|²`) and state `B` with it — say so; do not weaken the inequality.
4. Corollary `force_pairing_le'`: `abs ⟪f, Ju⟫ ≤ B * (Y + Z)` (the paper's second form).

## Deliverables
1. New module `formalization/NSFormalization/Section4/R44/JWeight.lean` (namespace `NSFormalization.Section4.R44`).
2. Records `research/R44/ATTEMPTS_S1A.md`, update `R44_SPLIT.md` row S1a (and G1/G3 status), conformance `research/R44/axioms_s1a.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R44.JWeight` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R44/REPORT_218.md`.
