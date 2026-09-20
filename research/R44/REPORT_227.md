# Lane 227 — R44 endpoint assembly

## 1. The theorem proved

`NSFormalization.Section4.R44.rcritical2_endpoint_of_differential` proves
Proposition 4.4's exact zero-datum finite-horizon conclusion:

```lean
forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν S) →
  ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f
```

Here `ν > 0`, `S > 0`, `MemForceR f`, and the **only** retained named analytic
input is `∀ T w, RCritical2Differential w hf`.
The fixed explicit universal constants are

```
theta = min R43.criticalConst (1 / (100 * (A05.criticalL3Const + 1)^3))
C₂ = 2, C₃ = 4, c = theta / 20, C = 3
radius ν S = c * ν^(3/2 : ℝ) * exp (-(C*ν*S)).
```

All required positivities and the strict radius arithmetic are proved.
The conclusion is strict lifespan beyond S, not infinite lifespan.

## 2. What Lean now contains

New `Section4/R44/Endpoint.lean` has 27 authored declarations. It contains the
single S1 structure, constants and radius, negative-half-order force continuity,
exact path-infimum norm identification, squared prefix bound, compact-window
Grönwall/first-exit bootstrap, homogeneous-to-inhomogeneous slice comparison,
L³ absorption, maximal-family transfer, explicit zero-datum H² budget, endpoint
finiteness, A02/A04 continuation assembly, and the zero-solution S1 witness.

The H² budget at any `0 < L ≤ S` up to the maximal lifespan is
`ofReal (32*L*forcePrimitive f L^2 + 32*(ν⁻¹)^2*∫₀ᴸ l2Sq(slice f t))`.
R43's maximal-endpoint gluing and natural-square/rpow pin are reused.
No endpoint velocity value or extra force smallness assumption is introduced.

`research/R44/axioms_endpoint.lean` audits all 27 declarations plus four
conformance/non-vacuity theorems. Its `EndpointConformance.main` and
`nonDensityBallZero` use the exact `Contracts.V1.Data` vocabulary. It proves
zero force satisfies the actual strict smallness premise, checks `A04.zeroSol`
with `E' = 0`, and invokes the new endpoint theorem at zero force after proving
S1 for every zero-force solution by uniqueness.

`ATTEMPTS_ENDPOINT.md` records the successful route and failed elaborations.
`R44_SPLIT.md` and `COMPARISON.md` record the current S2–S6/G3/G4/G5 status.
No existing Lean module, contract, binding, or test was edited.

## 3. Remaining gap

S1c/S1d must derive the exact differential inequality at the fixed constants
above and assemble its derivative integrability on each closed presingular
window `0 ≤ b < T`. This is precisely `RCritical2Differential`, with no other
analytic input hidden in its fields. Requiring integrability at a potentially
singular terminal T is deliberately avoided.

`rcritical2_endpoint` is the requested instantiation skeleton: its first
argument is the universal S1 provider, and its remaining binders have the
`RCritical2API.main` shape. It is explicitly conditional, not a fabricated
unconditional theorem. No full API witness or contract registration is claimed.
The force-path, bootstrap, embedding, H², gluing, and continuation obligations
are all proved from the tree once S1 is supplied.

## 4. Validation and commit

All Lean commands ran after sourcing `scripts/lean-env.sh`, from
`verification/`, with `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section4.R44.Endpoint`: exit 0. The new module
  has no warnings; ordinary Lake output replays existing dependency warnings.
- `lake --quiet build NSFormalization.Section4.R44.Endpoint`: exit 0; this
  also replays dependency warnings (16,229 bytes). The aggregate build is
  therefore not literally silent; the direct check of the new module is.
- `lake env lean ../formalization/NSFormalization/Section4/R44/Endpoint.lean`:
  exit 0, exactly zero output.
- `lake env lean ../research/R44/axioms_endpoint.lean`: exit 0; all 31 reports
  are exactly `[propext, Classical.choice, Quot.sound]`; all examples pass.
- `make check`: exit 0; all 13 contract-policy tests and work-queue checks pass.
- `lake test` (the `make test` recipe, run inside verification): exit 0.
- `make test-mutations`: exit 0; implementation refactoring accepted, and all
  three prohibited mutations rejected.
- `git diff --check`: clean. Forbidden-proof-token and option scans of the
  authored Lean files are clean; no heartbeat override is used.

Changes committed on `erenup/227-R44-endpoint`. No push, merge, or rebase.
Local validation logs are under `tmp/lane227/` and are not committed.
