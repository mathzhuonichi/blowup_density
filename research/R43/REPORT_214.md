# Lane 214 — R43 fractional Parseval

## 1. Proved

`pairing_identity_of_hcrit` proves, for every `t ∈ Ioo 0 T`,

```lean
⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫ =
  ∫ x : Space, (inner ℝ
    (advection (NSFormalization.Section4.C01.lift
      (fun y => w.velocity (t, y))) 0 x)
    ((criticalAdvectionLpBridge_shifted hcrit t ht).lambda x) : ℝ)
```

The shifted field is exactly lane 191's choice. The proof uses angular `L²`
Plancherel, the inverse half-order weights of the two homogeneous data, and
the exact `|ξ|` symbol of `rieszLambda`.

## 2. Lean deliverables

New `formalization/NSFormalization/Section4/R43/Parseval.lean` contains four
supporting lemmas, including the general `half_order_parseval`, and exports
`pairing_identity_of_hcrit`, `criticalAdvectionLpBridge_of_hcrit`,
`criticalTrilinearEstimate_of_hcrit'`, and `rcritical1_of_hcrit'`.
The last two consume `hcrit` alone, besides ambient force membership, with
the existing constant `trilinearConst = 16 * A05.criticalL3Const ^ 3`.

`research/R43/axioms_parseval.lean` audits all eight module declarations and
its explicit zero-path constructor. Each reports exactly
`[propext, Classical.choice, Quot.sound]`. Its two non-vacuity examples use
the genuine `A04.zeroSol 1 2`, the prescribed shifted field, and interior
time `1`, including both primed corollaries.

`ATTEMPTS_PARSEVAL.md` records the successful proof and resolved diagnostics.
`R43_SPLIT.md` marks S1b's bridge closed relative to `hcrit`. Existing Lean
modules are unchanged. Work is committed on `erenup/214-R43-parseval` with
message `feat(R43): close fractional Parseval bridge from critical data`.

## 3. Remaining gap

There is no remaining Parseval or S1b bridge hypothesis. No new analytic
hypothesis, admission, axiom, or heartbeat override was introduced.
Constructing `CriticalDatumPath w hf` from the classical solution remains a
separate task; the result does not claim unconditional completion of R43.

## 4. Validation

All commands ran inside this worktree after `. scripts/lean-env.sh`, with
`LEAN_NUM_THREADS=6`; all `lake` invocations ran from `verification/`.

- `lake build NSFormalization.Section4.R43.Parseval`: exit 0. The ordinary
  build replays existing dependency warnings; the new target is clean.
- `lake -q --log-level=error build NSFormalization.Section4.R43.Parseval`:
  exit 0, zero output (silent build).
- `lake env lean ../formalization/NSFormalization/Section4/R43/Parseval.lean`:
  exit 0, zero output.
- `lake env lean ../research/R43/axioms_parseval.lean`: exit 0; all nine
  named declarations have exactly the three required axioms; examples pass.
- `make check`: exit 0; plan, contracts, 13 policy tests, and work queue pass.
- `lake test` from `verification/` (the `make test` target's underlying
  command): exit 0; existing contract suite passes.
- `make test-mutations`: exit 0; the refactor is accepted and all three
  prohibited mutations are rejected.
- `git diff --check`: exit 0. Static scan of the new Lean files finds no
  prohibited proof escape or heartbeat override.

Raw logs are kept in the worktree's ignored `tmp/parseval_*.log` files.
