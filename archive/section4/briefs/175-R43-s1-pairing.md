# Lane 175-R43-s1-pairing — R43 row S1, first layer: the critical pairing identities for eq:Rcritical1 (HANDOFF P5)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/175-R43-s1-pairing` (git branch
`erenup/175-R43-s1-pairing`, based on `origin/erenup/integration`, which contains lane 164's
`Section4/D01/HomogeneousNorm.lean` (`dotHomogeneousENorm`, contract `D01.homogeneous_norm`), lanes
150/163/170's energy/enstrophy derivative machinery in `Section4/C01/`, and lane 159's `Section4/R43/Pieces.lean`).
Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 (rules) and §2 P5, `research/R43/R43_SPLIT.md` (row S1 and
its sub-rows at `:53-70`), `research/R43/REVIEW_SPLIT.md`, and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree. Never touch the root checkout or any other worktree. Never
  `git push`, never merge, never rebase. Committing on your own branch is allowed.
- Lean: `. scripts/lean-env.sh` in every shell; `lake` ONLY from `verification/`
  (`cd verification && LEAN_NUM_THREADS=6 lake build …`); drafts via `lake env lean ../research/R43/<file>.lean`.
- No `sorry`, `admit`, `axiom`, `native_decide`; `set_option maxHeartbeats N in` only per declaration,
  `N ≤ 400000`, commented. No edits to existing modules; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of
  `formalization/NSFormalization/Section4/{D01,A03,A04,A05,B02,C01,R43}`, `Source/`, `Paper1/`. Before citing
  a paper line, `sed -n` it.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity
  `example` on `A04.zeroSol` with `memForceR_zero` (see `research/C01/axioms_e5.lean`).

## Goal
eq:Rcritical1 (`04-whole-space.tex:97-99`): for a classical solution, with `y = ‖u‖_{Ḣ^{1/2}}`,
`z = ‖u‖_{Ḣ^{3/2}}`, `b = ‖f‖_{Ḣ^{1/2}}`, `½ (y²)' + (ν − C₀ y) z² ≤ b y`. The proof tests the projected
equation against `Λu` (`Λ = |D|`, the half-order homogeneous weight). This lane does the **identity
layer** (S1a, S1c of the split), not the trilinear estimate (S1b) and not the differentiability of the
critical path (which mirror lanes 150/163 with a homogeneous weight — a later lane):
1. **Weighted energy derivative shape**: in the *datum* language, `y(t)² = ‖Λ^{1/2}-datum of u(t)‖²` —
   define the critical path `t ↦ ‖A_{1/2}(t)‖²` with `A_{1/2}(t)` the order-`1/2` homogeneous datum of the
   velocity slice (`dotHomogeneousENorm (1/2)`; find in `D01/HomogeneousNorm.lean`, `D01/HalfOrder.lean`,
   `B02/` how homogeneous half-order data are built from the integer-order data of a `ClassicalSolutionR`
   slice — if that bridge (integer data ⇒ half-order homogeneous datum) is missing, that is gap G3/G4;
   isolate it as a named hypothesis `hcrit` giving the datum path and its continuity).
2. **Pairing identities** (S1a): for the momentum residual `∂ₜu = νΔu − (u·∇)u − ∇p + f` (lane 143's
   `momentum_split_toLp`), the pairing with `Λu` (in datum language: the Fourier-side inner product
   `⟪|ξ| û, ·⟫`) satisfies: `⟪Δu, Λu⟫ = −‖u‖²_{Ḣ^{3/2}}` (= `−z²`), `⟪∇p, Λu⟫ = 0` (divergence-free), and
   `⟪f, Λu⟫ ≤ b y` (Cauchy–Schwarz in the homogeneous scale). Prove each as a datum-level identity on
   `RealVectorSobolev`/homogeneous data using the tree's Fourier-side Leray/Laplacian symbols
   (`D01/LeraySymbol.lean`, `D01/LaplacianPairing.lean`, `D01/LerayDatum.lean`, `D01/HalfOrder.lean`).
3. **The scalar consequence shape** (S1c): assemble 1–2 into the exact `henergy` hypothesis form consumed by
   `Section4/R43/Pieces.lean`'s `criticalNormBound_radius` / `Paper1.critical_norm_bound`
   (`E'/2 + (ν − C₀ y) z² ≤ b y`), **conditional on** the named trilinear estimate
   `htri : |⟪(u·∇)u, Λu⟫| ≤ C₀ · y · z²` (S1b, a separate lane) and on `hcrit`. The output is a theorem
   `rcritical1_of_trilinear` whose only unproved inputs are `htri` and `hcrit`, each stated exactly.
4. Record `research/R43/ATTEMPTS_S1.md` (which identities closed, which tree lemmas, the exact residuals);
   update `R43_SPLIT.md` row S1 sub-rows; conformance `research/R43/axioms_s1.lean`.

## Deliverable
New module `formalization/NSFormalization/Section4/R43/CriticalPairing.lean` (namespace
`NSFormalization.Section4.R43`). Gates: `lake build NSFormalization.Section4.R43.CriticalPairing` (silent),
`lake env lean` on the module (0 output), the axioms file, `make check` from the worktree root.

## Report
Commit on your branch and end with a four-part report: 1. theorems proved (names, exact statements, the
two named hypotheses); 2. what is in Lean now; 3. gaps (exact residual with error text); 4. commands and
results. Also write it to `research/R43/REPORT_175.md`.
