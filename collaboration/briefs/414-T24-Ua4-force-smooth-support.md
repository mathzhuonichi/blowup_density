# Lane 414-T24-Ua4-force-smooth-support — T24a Ua4: `force_smooth` + `force_support` verbatim over raw packet fields

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/414-T24-Ua4-force-smooth-support` (git branch `erenup/414-T24-Ua4-force-smooth-support`, based on `origin/erenup/integration-section3`,
which contains lane 392's `Section3/T24/AffineBasics.lean` (`affineCylinder`, `AffineAdmissible`, `affineVelocity`, `crossAdvection`, `affineForce`, `window`, …), lane 398's
`Section3/T24/AffineMomentum.lean` and its probes (`research/T24/probes/affine_momentum_nonzero.lean`: the nonzero admissible `bWitness = spatialCurl (θ(t)φ(x)e₁)`),
lane 402's `AffineDivergence.lean`, lane 403's `AffineSpeed.lean`). Read `CLAUDE.md`, `research/T24/T24_SPLIT.md` §0, unit **Ua4** (`:103-108`) and §2 ledger,
`research/T24/Spec.lean:1020-1034` (fields `force_smooth`, `force_support`), `research/T24/RECONCILIATION.md` (T24a over raw packet clauses), the raw packet clauses
`velocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain`, `force_smooth : ContDiff ℝ ∞ F`, `force_support : CompactPositiveTimeSupport F` (grep them in the packet
structure `verification/Contracts/V1/Packet.lean` and its local canonical restatement used by lanes 398/402/403 — use the exact spellings those lanes take as hypotheses),
`research/T24/REPORT_398.md`, `REPORT_402.md`, `REPORT_403.md`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  **Import** `NSFormalization.Section3.T24.AffineBasics`; do not restate its definitions.
- **No named inputs, no placeholders, no goal repackaging** (analytic unit). An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T24/AffineForce.lean` (namespace `NSFormalization.Section3.T24`):
`theorem force_smooth {ν : ℝ} {U F : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ) (hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain) (hforce_smooth : ContDiff ℝ ∞ F) :
∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b → ContDiff ℝ ∞ (affineForce ν U F b)` and
`theorem force_support … (hforce_support : CompactPositiveTimeSupport F) : ∀ b, AffineAdmissible c r τ₀ τ₁ b → CompactPositiveTimeSupport (affineForce ν U F b)` —
conclusions token-identical to `Spec.lean:1025-1033` with `P.velocity`/`P.force` replaced by raw `U`/`F`; hypotheses only the raw packet clauses actually needed (say which;
`AffineAdmissible` should give `τ₁ < 1` via `window` or carry it explicitly as lane 403 did — state which). Route: every correction term `∂ₜb`, `−νΔb`, `(U·∇)b`, `(b·∇)U`, `(b·∇)b`
is supported in `tsupport b ⊆ affineCylinder c r τ₀ τ₁` (compact, inside `{t < τ₁ < 1} × ℝ³`, hence inside the open `preSingularDomain` where `U` is smooth); so each term is
smooth on the open set `{t < 1} × ℝ³` (products of `ContDiffOn` functions with the smooth compactly supported `b` and its derivatives) and vanishes on the open complement of
`tsupport b`; the two opens cover spacetime, so `ContDiff ℝ ∞` follows by gluing (`contDiff_iff_contDiffAt` + `ContDiffOn.contDiffAt` with `IsOpen.mem_nhds`, or
`contDiffAt_of_eventuallyEq` off the support). For the support clause, `F̃ − F` has compact support inside the cylinder (positive time), and `F` has `CompactPositiveTimeSupport`;
read the exact definition (`grep -rn "CompactPositiveTimeSupport" vendor/NavierStokesAndEuler/NavierStokes/ verification/Contracts/V1/`) and combine (`HasCompactSupport.add`,
union of positive-time supports). Reuse the vendor's `ResidualCalculus` smoothness helpers (`temporalDerivative`/`advection`/`spatialLaplacian` of smooth fields; lane 398 used
two interior-smoothness helpers from there — read `AffineMomentum.lean`). Probe `research/T24/probes/affine_force_closes.lean`: discharge the registered `AffineVariationAPI.force_smooth`
and `force_support` fields on `Bindings.packet ν hν` (pattern of `affine_momentum_closes.lean`), instantiate both at lane 398's nonzero `bWitness` (import that probe's construction or
rebuild it), plus the `b = 0` reduction. Deliverables: module, probe, `research/T24/axioms_ua4.lean`, `research/T24/ATTEMPTS_UA4.md`, Ua4 status line in `T24_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.AffineForce` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Try `research/T24/REPORT_414.md`; if the
report-file guard blocks it, put the full report in your final message.
