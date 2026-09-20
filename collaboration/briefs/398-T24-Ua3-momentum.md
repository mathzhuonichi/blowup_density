# Lane 398-T24-Ua3-momentum — T24 Ua3: the `momentum` field of `AffineVariationAPI` (eq:affine ①: the affine variation `U + b` solves the forced equation with the modified force, whole space, raw packet fields)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/398-T24-Ua3-momentum` (git branch `erenup/398-T24-Ua3-momentum`, based on `origin/erenup/integration-section3`; lane 392 (T24 Uc1 + Ua1,
codex, in progress) is creating `Section3/T24/AffineBasics.lean` with the T24a raw-field vocabulary (`affineVelocity`, the cylinder, `admissible`, …) — if it has not landed on your base,
restate the definitions you need verbatim from `research/T24/Spec.lean:1000-1117` under the same names/namespace and note it; the assembly lane will dedupe).
Read `CLAUDE.md` ("合同 import 规则": `formalization/` cannot import `Contracts.*` — state over raw packet fields `u p f : VelocityField` with the `PacketAPI` clauses as explicit hypotheses,
as `Section3/T14/PacketEnergy.lean` does, and convert in the probe), **`research/T24/T24_SPLIT.md` §0 and unit Ua3 (target verbatim `Spec.lean:1047`, route)**, `research/T24/Spec.lean`
(`AffineVariationAPI`, `affineVelocity`, `affineForce`/the modified force `eq:affine`, `03-torus.tex:668-696`), `research/T24/RECONCILIATION.md` §3, the whole-space operators
(`NavierStokes.ProblemStatement`: `navierStokesResidual`, `temporalDerivative`, `spatialLaplacian`, `advection`, `pressureGradient`) and Section 4's residual algebra
(`Section4/I01/Extension.lean` `extension_navierStokes`, `Section4/I02/Reference.lean` `correctionForce` — the "insert a smooth compactly supported perturbation and define the force
to make the equation exact" pattern), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). An honest partial with the exact residual statement and error text beats a stub.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T24/AffineMomentum.lean` (namespace `NSFormalization.Section3.T24`): `theorem momentum` verbatim (`Spec.lean:1047`): for every admissible
`b` (smooth, divergence-free, `tsupport b ⊆ Ioo τ₀ τ₁ ×ˢ ball c r`), the affine velocity `U + b` with the packet pressure `P` satisfies `navierStokesResidual ν (U + b) P = F̃_b` on the
paper's domain (`t ∈ Ioo 0 1`, or the field's exact domain), where `F̃_b` is the Spec's modified force (`F + ∂ₜb − νΔb + (U·∇)b + (b·∇)U + (b·∇)b` in the Spec's exact spelling — read it).
Route: expand `navierStokesResidual` (it is linear in `∂ₜ`, `Δ`, `∇p`; the advection is bilinear: `advection (U+b) = advection U + (U·∇)b + (b·∇)U + (b·∇)b` — prove the bilinear expansion
lemma for `advection`/`spatialDerivative` pointwise), use the packet's `navier_stokes` clause (`navierStokesResidual ν U P = F` on `Ioo 0 1`), and `abel`/`ring_nf` to match the Spec's
force. If the Spec's `F̃_b` orders the terms differently, match with `add_comm`/`add_left_comm`.

## Deliverables
1. `Section3/T24/AffineMomentum.lean`; 2. probe `research/T24/probes/affine_momentum_closes.lean` (import `Contracts.*`; close the Spec's field for `Bindings.packet ν hν`'s raw fields;
non-vacuity with a nonzero admissible `b`); 3. `research/T24/ATTEMPTS_UA3.md`, `research/T24/axioms_ua3.lean`, status in `research/T24/T24_SPLIT.md` Ua3, report `research/T24/REPORT_398.md`
(if a guard blocks the write, put the full report in your final message).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.AffineMomentum` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands and results).
