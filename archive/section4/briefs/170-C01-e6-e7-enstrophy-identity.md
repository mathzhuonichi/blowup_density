# Lane 170-C01-e6-e7-enstrophy-identity — C01 rows E6/E7: the enstrophy identity and the H² time integral

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/170-C01-e6-e7-enstrophy-identity` (git branch
`erenup/170-C01-e6-e7-enstrophy-identity`, based on `origin/erenup/integration`, which contains lane 163's
`Section4/C01/Enstrophy.lean`). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 (rules) and §2 P2,
`research/C01/ENERGY_SPLIT.md` (rows E5 DONE, E6, E7, `enstrophyIdentity`, `enstrophyIntegralBound`,
`h2TimeIntegral`), `research/C01/REPORT_163.md`, and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree. Never touch the root checkout or any other worktree. Never
  `git push`, never merge, never rebase. Committing on your own branch is allowed.
- Lean: `. scripts/lean-env.sh` in every shell; `lake` ONLY from `verification/`
  (`cd verification && LEAN_NUM_THREADS=6 lake build …`); drafts via `lake env lean ../research/C01/<file>.lean`.
- No `sorry`, `admit`, `axiom`, `native_decide`; `set_option maxHeartbeats N in` only per declaration,
  `N ≤ 400000`, commented. No edits to existing modules; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of
  `formalization/NSFormalization/Section4/{D01,A03,A04,A05,A01,C01}`. Before citing a paper line, `sed -n` it.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity
  `example` on `A04.zeroSol` with `memForceR_zero` (as `research/C01/axioms_e5.lean` does).

## Goal
Lane 163 proved `enstrophyDerivative_classical_unconditional`: at every interior `t`,
`d/dt ∫∑ᵢ‖∂ᵢu‖² = −2⟪Δu, ∂ₜu⟫`. Now substitute the momentum equation for `∂ₜu` (lane 143's
`momentum_split_toLp` in `Section4/C01/MomentumCarrierB.lean`: `∂ₜu = νΔu − (u·∇)u − ∇p + f` in `Lp`)
and kill the pressure term (`⟪Δu, ∇p⟫ = 0` for divergence-free `u`: the tree's `gradient_pairing_zero` /
`laplacian_pairing` in `Section4/C01/EnergyIdentity.lean` / `Vocabulary.lean` — check which pairing
vanishing lemmas exist) to get:
- **E6 / `enstrophyIdentity`** (`research/C01/Spec.lean:487`, `04-whole-space.tex:105-113` eq:RH1's
  derivation): `d/dt ‖∇u‖²₂ = 2·advectionWork(u) − 2ν·laplacianSq(u) − 2·pairing(f, Δu)` in the spec's
  vocabulary (`advectionWork`, `laplacianSq`, `gradientSq`, `pairing` — restated locally in
  `Section4/C01/Vocabulary.lean` / `EnergySpec.lean`; reuse, do not redefine);
- **E7 / the H² integral input**: from E6 plus the H¹ absorption gate (the registered C01 V1 fields
  `research/C01/Spec.lean:532,576` — check `verification/Contracts/V1/EnergyAbsorptionPartial.lean` for
  what is already registered) derive `∫₀ˢ‖u‖²_{H²} < ∞` for `S < T`, i.e. `h2TimeIntegral`
  (`Spec.lean:599`) or its strongest provable precursor (`squaredHTwoIntegral S u ≠ ⊤` in A04's spelling,
  `research/A04/Spec.lean:202`; lane 159's `R43/Pieces.lean` has the `ℕ`-pow/rpow pin).

## Deliverables
1. New module `formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean`
   (namespace `NSFormalization.Section4.C01`): `enstrophyIdentity_classical` (E6, at every interior `t`,
   raw-integral form) and its spec-vocabulary form if the bridges are `rfl`/one-line; then
   `h2TimeIntegral_of_absorption` (E7) with the absorption hypothesis stated exactly as C01 V1's gate
   field, or the exact residual if the Grönwall/absorption step needs a scalar lemma (look at
   `Paper1/ScalarEnergy.lean`, `Section4/A04/Gronwall.lean`, `Section4/C01/EnergyBounds.lean`'s
   `sqrt_energy_le_primitive'` before writing a new one).
2. Records: `research/C01/ATTEMPTS_E6E7.md`; conformance `research/C01/axioms_e6e7.lean`; update
   `ENERGY_SPLIT.md` rows E6/E7/`enstrophyIdentity`/`h2TimeIntegral` (DONE or exact residual). Note the
   C01 V4 registration plan (extend V3 with these fields) but do not register in this lane.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.C01.EnstrophyIdentity`
(silent), `lake env lean` on the module (0 output), the axioms file, `make check` from the worktree root.

## Report
Commit on your branch and end with a four-part report: 1. theorems proved (names, exact statements);
2. what is in Lean now; 3. gaps (exact residual with error text); 4. commands and results.
Also write it to `research/C01/REPORT_170.md`.
