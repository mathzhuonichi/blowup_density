# Lane 417-T24-Ua7-infinite-dimensional — T24a Ua7: `infinite_dimensional` (a linearly independent sequence of admissible variations)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/417-T24-Ua7-infinite-dimensional` (git branch `erenup/417-T24-Ua7-infinite-dimensional`, based on `origin/erenup/integration-section3`,
which contains `Section3/T24/{AffineBasics,AffineMomentum,AffineDivergence,AffineSpeed,AffineEnergy}.lean` and lane 398/414's nonzero admissible witness construction in
`research/T24/probes/affine_momentum_nonzero.lean` / `affine_force_nonzero.lean` (`bWitness = spatialCurl (θ(t)·φ(x)·e₁)`, `bWitness_admissible`, `bWitness_ne_zero`)). Read
`CLAUDE.md`, `research/T24/T24_SPLIT.md` §0, unit **Ua7** (`:117-125`) and §2 ledger, `research/T24/Spec.lean:1078-1090` (field `infinite_dimensional`: `∃ b : ℕ → SpaceTimeField,
(∀ n, AffineAdmissible c r τ₀ τ₁ (b n)) ∧ LinearIndependent ℝ b`), `paper/sections/03-torus.tex:688-691`, `research/T24/REPORT_398.md` §"witness", `REPORT_414.md` §2, the vendor
`NavierStokes.SpatialCurl` (`spatialDivergence_spatialCurl`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.
- **Import** `NSFormalization.Section3.T24.AffineBasics`; do not restate its definitions. The witness construction may be promoted into a small library module
  `Section3/T24/AffineWitness.lean` (new file) so that Ua7 and the probes share it — do that, and say so.

## Goal
New module `formalization/NSFormalization/Section3/T24/AffineFamily.lean` (namespace `NSFormalization.Section3.T24`): `theorem infinite_dimensional (c : Space) (r τ₀ τ₁ : ℝ)
(hr : 0 < r) (hτ : τ₀ < τ₁) : ∃ b : ℕ → VelocityField, (∀ n, AffineAdmissible c r τ₀ τ₁ (b n)) ∧ LinearIndependent ℝ b` — conclusion token-identical to `Spec.lean:1085-1087`;
hypotheses only the geometric facts needed (say which; `window`/`radius_pos` in `AffineBasics.lean` show what the canonical structure provides). Route: choose countably many
pairwise disjoint closed balls `closedBall (c + (r/2)·xₙ) ρₙ ⊆ ball c r` (e.g. centres on a segment accumulating at a point, radii shrinking) and one time bump `θ` in `(τ₀, τ₁)`;
`b n := spatialCurl (θ(t)·φₙ(x)·e₁)` with `φₙ` a `ContDiffBump` on the `n`-th ball: smooth, compactly supported in the cylinder, divergence-free by `spatialDivergence_spatialCurl`,
hence admissible; linear independence from disjoint supports plus `b n ≠ 0` (`Fintype.linearIndependent_iff`/`linearIndependent_iff'`: evaluate a vanishing finite combination at a
point where only `b n` is nonzero). Deliverables: the module (+ `AffineWitness.lean` if promoted), `research/T24/probes/affine_family_closes.lean` (discharge the registered
`AffineVariationAPI.infinite_dimensional` field on `Bindings.packet ν hν` in Contracts vocabulary; show `b 0 ≠ b 1`), `research/T24/axioms_ua7.lean`, `research/T24/ATTEMPTS_UA7.md`,
Ua7 status line in `T24_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.AffineFamily` (0 errors), `lake env lean` on the module(s) (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement / files / gaps with error text / commands and results). Try `research/T24/REPORT_417.md`; if the
report-file guard blocks it, put the full report in your final message.
