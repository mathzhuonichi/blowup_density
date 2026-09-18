# Lane 403-T24-Ua5-speed-unbounded — T24a Ua5: `speed_unbounded` verbatim over raw packet fields

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/403-T24-Ua5-speed-unbounded` (git branch `erenup/403-T24-Ua5-speed-unbounded`, based on `origin/erenup/integration-section3`,
which contains lane 392's `formalization/NSFormalization/Section3/T24/AffineBasics.lean` — in particular `late_agreement` (`:78`: `affineVelocity U b = U` at times `t ≥ τ₁`, read its
exact form) and `AffineAdmissible` (`:26`, includes `τ₁ < 1`? check `window` `:58`)). Read `CLAUDE.md`, `research/T24/T24_SPLIT.md` §0 and unit **Ua5** (`:109-111`) and §2 ledger,
`research/T24/Spec.lean:1060-1071` (field `speed_unbounded` and docstring), `research/T24/RECONCILIATION.md` (T24a over raw packet clauses), the raw `SpeedUnboundedAtOne`
(`formalization/NSFormalization/Source/Packet.lean:145` — read the definition: which times/points it quantifies over), `research/T24/REPORT_392.md`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  **Import** `NSFormalization.Section3.T24.AffineBasics` — do not restate its definitions.
- No named inputs. Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing.

## Goal
New module `formalization/NSFormalization/Section3/T24/AffineSpeed.lean` (namespace `NSFormalization.Section3.T24`):
`theorem speed_unbounded {U : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ) (hspeed : SpeedUnboundedAtOne U) : ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
SpeedUnboundedAtOne (affineVelocity U b)` — conclusion token-identical to `Spec.lean:1069-1071` with `P.velocity` replaced by the raw `U`; hypotheses only the raw packet clause
(add `hτ₁ : τ₁ < 1` only if `AffineAdmissible` does not already carry it — say which). Route: `SpeedUnboundedAtOne` is a statement about times near `1`; since `affineVelocity U b = U`
on `t ≥ τ₁` (`late_agreement`) and `τ₁ < 1`, every witness for `U` at times in `(τ₁, 1)` is a witness for `U + b` (if the definition quantifies over all `t < 1`, restrict the
witness sequence to `t > τ₁`, or use eventual equality). Probe `research/T24/probes/affine_speed_closes.lean`: discharge the registered `AffineVariationAPI.speed_unbounded` field on
`Bindings.packet ν hν` and a `b = 0` non-vacuity example. Deliverables: module, probe, `research/T24/axioms_ua5.lean`, `research/T24/ATTEMPTS_UA5.md`, Ua5 status line in `T24_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.AffineSpeed` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement / files / gaps with error text / commands and results). Also write it to `research/T24/REPORT_403.md`.
