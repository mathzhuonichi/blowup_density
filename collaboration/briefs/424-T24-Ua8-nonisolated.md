# Lane 424-T24-Ua8-nonisolated — T24a Ua8: `nonisolated` (the affine family approaches the packet in every `C^m` seminorm on `tsupport b`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/424-T24-Ua8-nonisolated` (git branch `erenup/424-T24-Ua8-nonisolated`, based on `origin/erenup/integration-section3`, which contains
`Section3/T24/{AffineBasics,AffineMomentum,AffineDivergence,AffineSpeed,AffineEnergy,AffineForce}.lean` — in particular lane 398's six-term expansion `navierStokesResidual_affine_expand`
and lane 392's `affineCkSeminorm` (`AffineBasics.lean:50`, an `ℝ≥0∞`-valued `⨆` — read its exact definition)). Read `CLAUDE.md`, `research/T24/T24_SPLIT.md` §0, unit **Ua8** (`:145-149`)
and §2 ledger, `research/T24/Spec.lean:1095-1110` (field `nonisolated`: `∀ b admissible, b ≠ 0 → ∀ m, Tendsto (fun λ ↦ ckSeminorm (tsupport b) m (Ũ_{λb} − U)) (𝓝 0) (𝓝 0) ∧ Tendsto (… F̃_{λb} − F …)
(𝓝 0) (𝓝 0)` — read the exact spelling, incl. whether the seminorm is the `AffineBasics` one and how `λ • b` is written), `paper/sections/03-torus.tex:692-696`, `research/T24/REPORT_398.md`
(§1 expansion), `REPORT_414.md` (the interior smoothness helpers `contDiffOn_affineForce_interior`, `affineForce_eq_of_notMem_tsupport`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  **Import** `NSFormalization.Section3.T24.AffineBasics` (and `AffineForce`/`AffineMomentum` as needed); do not restate their definitions.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T24/AffineNonisolated.lean` (namespace `NSFormalization.Section3.T24`): `theorem nonisolated` with conclusion token-identical to the
Spec field (with `P.velocity`/`P.force` replaced by raw `U`/`F`) under only the raw packet clauses needed (`velocity_smooth` on the pre-singular domain and, if the seminorm of the force
difference needs it, `force_smooth`; state `0 < τ₀`, `τ₁ < 1` explicitly as lanes 403/414 do). Route: velocity difference `Ũ_{λb} − U = λ • b`, so every `C^m` seminorm on `tsupport b` is
`|λ|·‖b‖_{C^m}` with `‖b‖_{C^m} < ⊤` (smooth compactly supported ⇒ bounded derivatives of every order on the compact `tsupport b`); force difference `F̃_{λb} − F = λ·(∂ₜb − νΔb + (U·∇)b +
(b·∇)U) + λ²·(b·∇)b` (rearrange lane 398's expansion), each coefficient smooth on a neighbourhood of `tsupport b` (inside `Ioo 0 1 ×ˢ univ` where `U` is smooth), so the seminorm is
`≤ |λ|·C_m + λ²·C'_m` with finite `C_m, C'_m`; conclude `Tendsto … (𝓝 0) (𝓝 0)` in `ℝ≥0∞` (`ENNReal.tendsto_nhds_zero`, `tendsto_order`, or `Filter.Tendsto.mono` with the explicit bound;
be careful that the seminorm is an `ℝ≥0∞` `⨆` and never a real `sSup`). If the `C^m` boundedness of a smooth compactly supported field is not in the tree, prove a general helper
`ckSeminorm_lt_top_of_contDiff_compact` (grep `ContDiff.bounded`, `HasCompactSupport.exists_bound`, `IsCompact.exists_bound_of_continuousOn`, `iteratedFDeriv` continuity). Deliverables: the
module, `research/T24/probes/affine_nonisolated_closes.lean` (discharge the registered `AffineVariationAPI.nonisolated` field on `Bindings.packet ν hν` in Contracts vocabulary, pattern of
`affine_force_closes.lean`; instantiate at lane 417's `AffineWitness.curlBump` witness — import `Section3/T24/AffineWitness.lean` if lane 417 has landed on this base, else at lane 398's
`bWitness` rebuilt), `research/T24/axioms_ua8.lean`, `research/T24/ATTEMPTS_UA8.md`, Ua8 status line in `T24_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.AffineNonisolated` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement / files / gaps with error text / commands and results). Try `research/T24/REPORT_424.md`; if the report-file guard
blocks it, put the full report in your final message.
