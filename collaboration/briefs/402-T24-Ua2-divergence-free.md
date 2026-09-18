# Lane 402-T24-Ua2-divergence-free — T24a Ua2: `divergence_free` verbatim over raw packet fields

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/402-T24-Ua2-divergence-free` (git branch `erenup/402-T24-Ua2-divergence-free`, based on `origin/erenup/integration-section3`,
which contains lane 392's `formalization/NSFormalization/Section3/T24/AffineBasics.lean` (`affineCylinder`, `AffineAdmissible`, `affineVelocity`, `affinePressure`, `crossAdvection`,
`affineForce`, `late_agreement`, …) and `Section3/T24/Conservative.lean`). Read `CLAUDE.md`, `research/T24/T24_SPLIT.md` §0 and unit **Ua2** (`:94-96`) and §2 ledger,
`research/T24/Spec.lean:1030-1040` (the field `divergence_free` and its docstring), `research/T24/RECONCILIATION.md` (T24a is stated over the **raw** packet clauses, not
`Contracts.V1.PacketAPI`, because `formalization/` cannot import `Contracts.*`), the raw packet structure (`grep -n "divergence" formalization/NSFormalization/Source/Packet.lean` or
wherever `research/T24/T24_SPLIT.md` §2 points: `I01.packet` clauses), `research/T24/REPORT_392.md`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  **Import** `NSFormalization.Section3.T24.AffineBasics` — do not restate its definitions (duplicate names in the namespace break the assembly).
- No named inputs (the unit is elementary). Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing.

## Goal
New module `formalization/NSFormalization/Section3/T24/AffineDivergence.lean` (namespace `NSFormalization.Section3.T24`):
`theorem divergence_free {U : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ) (hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain) (hdivergence : <the raw packet divergence clause,
token-identical to the packet field>) : ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b → ∀ t ∈ Set.Ico (0:ℝ) 1, ∀ x : Space, spatialDivergence (affineVelocity U b) t x = 0` —
the conclusion token-identical to `Spec.lean:1038-1040` with `P.velocity` replaced by the raw `U` (same convention as lane 398's `momentum`: hypotheses are exactly the raw packet
clauses it needs; drop `hvelocity_smooth` if additivity of `spatialDivergence` does not need differentiability at the point — check the vendor lemma). Route: `spatialDivergence (U + b) =
spatialDivergence U + spatialDivergence b` pointwise where both are differentiable (grep `spatialDivergence_add` / `spatialDivergence` in `vendor/NavierStokesAndEuler/NavierStokes/`
`ResidualCalculus.lean`, `SpatialCurl.lean`, `Divergence*.lean`), `∇·U = 0` on `Ico 0 1` from the raw clause, `∇·b = 0` from `AffineAdmissible` (`AffineBasics.lean:26`). Also a probe
`research/T24/probes/affine_divergence_closes.lean` that discharges the registered `AffineVariationAPI.divergence_free` field on `Bindings.packet ν hν` (mirror the pattern described
in `research/T24/REPORT_398.md` §2 if visible on this base; otherwise construct it from `verification/Bindings/Packet*.lean`) and a `b = 0` non-vacuity example.
Deliverables: the module, the probe, `research/T24/axioms_ua2.lean`, `research/T24/ATTEMPTS_UA2.md`, Ua2 status line in `T24_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.AffineDivergence` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement / files / gaps with error text / commands and results). Also write it to `research/T24/REPORT_402.md`.
