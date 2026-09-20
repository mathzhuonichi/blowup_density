# Lane 221 — critical force path

## 1. Theorem proved

For `hf : MemForceR f`, `ForcePath.lean` closes the exact G2 comparison
`forceHomogeneousENorm 1 (1/2) f ≤ forceSobolevENormL1 (1/2) f`
and G3 finiteness `forceHomogeneousENorm 1 (1/2) f ≠ ⊤`.
It identifies `criticalForceAt f t = ‖criticalForceHalf t‖` for `t ≥ 0`,
proves continuity and interval integrability, and proves continuity, interior
FTC, zero initial value and monotonicity of its integral primitive.

`critical_bootstrap_zero_datum` gives
`∀ t ∈ Icc 0 S, criticalNormAt w.velocity t ≤ c * ν` for a classical solution
with zero initial datum, assuming `0 < ν`, `MemForceR f`, `0 ≤ S < T`,
`0 ≤ c < 1 / (2 * trilinearConst)`, and
`criticalForcePrimitive f S ≤ c * ν`.

## 2. What is in Lean

The retained and completed draft exports 25 declarations. The order-two force
path from `MemForceR` is lowered and converted through lane 219's continuous
linear map; uniqueness identifies the canonical homogeneous path. That path
is explicitly `MemLp` of order one and strongly measurable for the positive-time
measure. The contractive vector conversion compares arbitrary admissible paths,
which proves the exact infimum comparison, not merely a slicewise inequality.
Prefix integrals are bounded by both homogeneous and inhomogeneous global norms.
The two zero-initial-field S6 reductions are also exported.

The probe `probes/lane221_s2_wiring.lean` checks the promoted S2 wiring with
integral smallness, with inhomogeneous norm smallness, and on a concrete zero
solution. `axioms_force_path.lean` audits every declaration and checks zero and
nonzero smooth compactly supported forces. `ATTEMPTS_FORCE_PATH.md` records the
route and the repaired nonzero-witness elaboration error; `R43_SPLIT.md` updates
G2/G3/G4/S2/S6. No existing Lean module was changed.

## 3. Remaining gaps

None in this lane's requested force-path facts or zero-datum bootstrap.
No fallback hypothesis is needed. The closed interval endpoint must satisfy
`S < T` because a classical solution is defined on `[0,T)`; no estimate at an
undefined maximal endpoint is claimed. General initial-data bootstrap,
maximal-lifespan gluing/continuation and contract registration remain separate.
The S6 force reduction is closed, not the full maximal-lifespan theorem.

## 4. Commands and results

Lean commands run from `verification/`, after sourcing `../scripts/lean-env.sh`,
with `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section4.R43.ForcePath`: exit 0. Existing dependency
  warnings are replayed, so the aggregate build is not literally silent.
- `lake env lean ../formalization/NSFormalization/Section4/R43/ForcePath.lean`:
  exit 0, exactly zero output.
- `lake env lean ../research/R43/axioms_force_path.lean`: exit 0; all 25 declarations
  print exactly `[propext, Classical.choice, Quot.sound]`; both force examples pass.
- `lake env lean ../research/R43/probes/lane221_s2_wiring.lean`: exit 0, zero output.
- `make check`: exit 0; all 13 policy tests pass, 30 work items consistent.
- `lake test` (the `make test` recipe, from `verification/`): exit 0.
- `make test-mutations`: exit 0; all three prohibited mutations rejected.
- Forbidden-proof-token scan and `git diff --check`: clean. No heartbeat override
  is needed; the default declaration budget suffices.

Committed on `erenup/221-R43-force-path`; no push, merge or rebase.
