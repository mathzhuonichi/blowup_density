# Lane 223 — zero-datum R43 endpoint

## 1. Theorem proved

`NSFormalization.Section4.R43.inhomogeneousAtZero_of_memForceR` proves:

```lean
∀ ν : ℝ, 0 < ν → ∀ f : SpaceTimeField, MemForceR f →
  forceSobolevENormL1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν) →
    maximalLifespanR ν (fun _ => 0) f = ⊤
```

This is `research/R43/Spec.lean:243–247`, with the registered datum-path
**inhomogeneous** force norm, not a replacement smallness condition.

```lean
criticalConst = min (1 / (8 * trilinearConst))
  (1 / (4 * (A05.gradientL6Const * A05.criticalL3Const)))
```

`criticalConst_pos` proves positivity. Here `gradientL6Const` is the C01 V4
absorption constant C₁ and `criticalL3Const` is the embedding constant.
The stronger homogeneous-smallness theorem is proved first.

## 2. What is in Lean

New `Section4/R43/Endpoint.lean`: 12 declarations covering the explicit radius,
forcing-prefix estimate, slice bootstrap, L³ absorption, maximal-family
absorption, the explicit zero-datum H² endpoint budget, A04 finiteness, and
both homogeneous and inhomogeneous global-lifespan conclusions.

G5 was already implemented in `MaximalEndpoint.lean`. For fixed terminal S,
C01's Ioc estimates all use the same finite budget. Their directed union
controls `(0,S)`, including finite maximal S, without assigning a terminal
velocity. The zero-datum bound is
`ofReal (32*S*forcePrimitive f S^2 + 32*(ν⁻¹)^2*∫₀ˢ l2Sq(f(t)))`.
A02's unconditional maximal existence and A04's locally finite integral
criterion complete the proof.

The brief's two A04 dependency files were absent in the starting checkout.
`RestartFixedForce.lean` and `ShiftedExtension.lean` are included byte-for-byte
from local lane 217 commit `d6f9cfd605041cb015a2119d351b6d77578c6b18`, in the
separate dependency commit `cfd5908`. No merge, rebase, push, existing Lean
module edit, or other worktree modification was performed.

`axioms_endpoint.lean` audits all 12 endpoint declarations and an additional
conformance theorem in literal `Contracts.V1.Data` vocabulary. All 13 print
exactly `[propext, Classical.choice, Quot.sound]`. Its zero-force example
proves the actual smallness premise and invokes the final theorem.

## 3. Remaining gaps

None for the zero-datum endpoint. No fallback hypothesis is present.
The optional general-`a` bootstrap / `RCritical1API.universal` is not proved by
this lane. No complete API witness or new contract registration is claimed.
The unchanged imported A04 files retain their upstream implementation; the
12 declarations and exact-axiom counts above refer to the authored endpoint
module, with the Data conformance theorem audited separately.

## 4. Commands and results

All Lean commands ran from `verification/`, after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section4.R43.Endpoint`: exit 0. Endpoint has no
  warnings; Lake replays pre-existing dependency warnings, so the aggregate
  build output is not literally silent.
- `lake env lean ../formalization/NSFormalization/Section4/R43/Endpoint.lean`:
  exit 0, exactly zero output.
- `lake env lean ../research/R43/axioms_endpoint.lean`: exit 0; 13 exact
  standard-three-axiom reports and the zero-force example pass.
- `make check`: exit 0; policy tests and all 30 work items pass.
- `lake test` (the `make test` recipe, run inside `verification/`): exit 0.
- `make test-mutations`: exit 0; all three prohibited mutations rejected.
- Dependency byte comparison against lane 217: exact match for both files.
- `git diff --check` and forbidden-proof-token scan of new Lean code: clean.
  No heartbeat override is used in the endpoint module.

Committed on `erenup/223-R43-endpoint`. No push.
