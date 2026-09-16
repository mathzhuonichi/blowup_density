# Lane 220 report — R44 row S1c

## 1. Theorem proved

Row S1c is closed at the static datum level.  For `h : JWeightDatum u f` and
the separate standard carrier package `ha : AdvectionJDatum h`, Lean proves

```text
|advectionJPairing h ha|
  ≤ trilinearConstJ * Y u * (Y u ^ 2 + Z u ^ 2),

trilinearConstJ = 3 * criticalL3Const ^ 3 > 0.
```

It also proves the paper's intermediate form with
`Y * Z * sqrt (Y² + Z²)`.  The named package contains no estimate: it records
only `H^∞` and the negative-half-order advection datum.  The physical `L²`
realization of `Ju`, its half-order datum identity, and exact Parseval are all
derived in the module.

## 2. What Lean now contains

`formalization/NSFormalization/Section4/R44/TrilinearJ.lean` contains:

- the contractive inhomogeneous-to-homogeneous half-order datum bridge and the
  resulting inhomogeneous critical `L³` estimate;
- a canonical physical `L²` field for every real half-order datum, including
  proofs of component reality, square integrability, and exact
  `IsSobolevDatum` reassembly;
- `inhomogeneous_half_order_parseval`, deriving the physical pairing at dual
  orders `-1/2` and `1/2` from order lowering and R43's component Parseval;
- `AdvectionJDatum`, `advectionJPairing`, and the three-factor physical Hölder
  estimate;
- the explicit positive constant `trilinearConstJ`, the square-root estimate,
  and the requested theorem `advection_pairing_le`.

The repaired physical identification reuses the repository's Fourier
conjugation/order-lowering symmetry and `vectorLpReassembly_ae` facts.  No
extra identification hypothesis was needed.

`research/R44/axioms_s1c.lean` audits all exported declarations and all named
witnesses.  Every one prints exactly
`[propext, Classical.choice, Quot.sound]`.  It instantiates the complete S1c
package at zero and reuses lane 218's genuinely nonzero compact-smooth bump to
instantiate both `JWeightDatum` and the complete `AdvectionJDatum`.  The latter
needs no assumed pairing field: the final estimate invokes the general
Parseval theorem.  The estimate is applied to both instances.

## 3. Remaining gaps

This is a static, per-slice result and is not yet registered in a contract or
binding.  The final R44 PDE inequality still needs S1b (differentiate `Y²`,
identify momentum, remove pressure), S1d (Young absorption), and time-path
wiring.  `AdvectionJDatum` must be supplied for solution slices by the eventual
R44 carrier path; its requirements are only standard `H^∞` regularity and a
negative-half-order datum, not an assumed nonlinear bound or pairing identity.

## 4. Commands and results

With `. scripts/lean-env.sh` loaded, the Lean checks were run from
`verification/`, and the policy check from the worktree root:

```text
LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R44.TrilinearJ
lake env lean ../formalization/NSFormalization/Section4/R44/TrilinearJ.lean
lake env lean ../research/R44/axioms_s1c.lean
make check
```

The module build and both direct Lean checks pass; the module check has zero
output.  The axiom file prints only the exact permitted axiom set for every
declaration.  `make check` passes all repository policy checks.

The implementation contains no `sorry`, `admit`, `axiom`, `native_decide`, or
heartbeat override.
