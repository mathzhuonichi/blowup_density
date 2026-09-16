# Lane 252 — R45 compact-class density and zero threshold

## 1. The theorem proved

This lane proves the `Y = forceClassCompact` instances of the reconciled
Corollary 4.5 fields `density` and `zeroIff` from `research/R45/Spec.lean`.
Their quantifier order is copied from those fields after specializing `Y`.
The lane also proves the two supporting adapters requested by the task:
compact closure from `g` and `f-g`, and `F_c ⊆ F_R`.

## 2. What Lean now contains

`verification/Bindings/CompactClassDensity.lean` contains four declarations:

- `memForceCompact_add_memForceCompact`;
- `memForceR_of_memForceCompact`;
- `density_compact`;
- `zeroIff_compact`.

The density proof reuses lane 235's lifespan case split.  In the long-lifespan
case, lane 233's insertion record supplies force convergence and exact
lifespan, while `forceDifference_compact` and compact addition closure keep the
witness in `F_c`.  The zero-data only-if direction uses lane 232's explicit
excluded radius centered at zero, transports compact breakdown forces into
`F_R` using the proved inclusion, and uses lane 249's registered restatement
bridges.  `research/R45/axioms_compact_class.lean` audits all four declarations
and includes concrete non-vacuity checks at `ν = T = 1`, `a = g = 0`, `q = 1`,
and `s = 0`.

Every audited declaration reports exactly
`[propext, Classical.choice, Quot.sound]`.

## 3. Gaps and scope

No compact-class fact remains as a supplier hypothesis; in particular, the
registered D01 theorem discharges `F_c ⊆ F_R` directly.  The rapid-class
instances of `density` and `zeroIff`, `schwartzDensity`, and both
`regularReference` instances are outside this lane and remain for their
assigned suppliers/assembly lanes.  No existing contract, binding, or test
module was modified.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, and ran Lake from `verification/`.

- `lake build Bindings.CompactClassDensity` exited 0.  Lake replayed existing
  upstream linter warnings; the new target emitted no warning.
- `lake env lean Bindings/CompactClassDensity.lean` exited 0 with no output.
- `lake env lean ../research/R45/axioms_compact_class.lean` exited 0; all four
  `#print axioms` lines printed exactly the required three axioms and both
  non-vacuity examples elaborated.
- `make check` exited 0.
- `make test` exited 0; all 32 registered contract suites passed.
- `git diff --check` exited 0.

No push, merge, or rebase was performed.
