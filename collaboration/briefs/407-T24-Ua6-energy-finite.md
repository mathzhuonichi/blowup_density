# Lane 407-T24-Ua6-energy-finite — T24a Ua6: `energy_finite` verbatim over raw packet fields (`‖U+b‖_{E₁} < ∞`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/407-T24-Ua6-energy-finite` (git branch `erenup/407-T24-Ua6-energy-finite`, based on `origin/erenup/integration-section3`, which
contains lane 392's `Section3/T24/AffineBasics.lean` (`AffineAdmissible`, `affineVelocity`, `affineCylinder`, …)). Read `CLAUDE.md`, `research/T24/T24_SPLIT.md` §0, unit **Ua6**
(`:112-116`) and §2 ledger (raw `energyENorm 1 U < ⊤`), `research/T24/Spec.lean:1072-1077` (field `energy_finite`), `research/T24/RECONCILIATION.md` (T24a over raw packet
clauses), the registered energy norm `energyENorm 1 = energyEssSup + energyGradient` (`verification/Contracts/V1/Data.lean:475` and its local canonical copy — grep `energyENorm`
in `formalization/NSFormalization/Section4/A02/Restrict.lean` / `Section4/**` and use the spelling the raw packet clause uses), `research/T24/REPORT_392.md`, `REPORT_402.md`,
and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  **Import** `NSFormalization.Section3.T24.AffineBasics`; do not restate its definitions.
- No named inputs, no placeholders. Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing.

## Goal
New module `formalization/NSFormalization/Section3/T24/AffineEnergy.lean` (namespace `NSFormalization.Section3.T24`): `theorem energy_finite {U : VelocityField} (c : Space)
(r τ₀ τ₁ : ℝ) (henergy : energyENorm 1 U < ⊤) : ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b → energyENorm 1 (affineVelocity U b) < ⊤` — conclusion token-identical to
`Spec.lean:1076-1077` with `P.velocity` replaced by the raw `U`; hypotheses only the raw packet clause(s) actually needed (say which). Route: (1) `energyENorm 1 b < ⊤` for
admissible `b` — smooth with compact support in the cylinder, so `‖b‖_{L^∞_t L²_x}` and `‖∇b‖_{L²_{t,x}}` are finite (bounded continuous function on a compact set × finite
volume; read the exact definitions of `energyEssSup`/`energyGradient` — essential sup over `t` of `L²` slice norms, and the space-time `L²` of the gradient); (2) subadditivity
`energyENorm 1 (U + b) ≤ energyENorm 1 U + energyENorm 1 b` (triangle for `eLpNorm`/`essSup` — grep `energyENorm_add`, `energyEssSup_add`, `energyGradient_add` in `Section4/`
and `Source/` before proving; if absent, prove them here). Probe `research/T24/probes/affine_energy_closes.lean`: discharge the registered `AffineVariationAPI.energy_finite` field
on `Bindings.packet ν hν` (pattern of `research/T24/probes/affine_divergence_closes.lean`) and a `b = 0` non-vacuity example. Deliverables: module, probe, `research/T24/axioms_ua6.lean`,
`research/T24/ATTEMPTS_UA6.md`, Ua6 status line in `T24_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.AffineEnergy` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement / files / gaps with error text / commands and results). Try `research/T24/REPORT_407.md`; if the
report-file guard blocks it, put the full report in your final message.
