# Lane 218 report — R44 row S1a

## 1. Theorem proved

Row S1a is closed at the static datum level.  For the single standard,
satisfiable restriction `JWeightDatum u f`, Lean proves

```text
‖u‖²_{H^(3/2)} = Y² + Z²,
abs ⟪f, Ju⟫ ≤ B * sqrt (Y² + Z²),
abs ⟪f, Ju⟫ ≤ B * (Y + Z),
```

where `Y = ‖u‖_{H^(1/2)}`, `Z = ‖∇u‖_{H^(1/2)}`, and
`B = ‖f‖_{H^(-1/2)}`.  The `Z` spelling is A03's canonical vector-gradient
norm, and Lean also proves that its square is the sum of the three coordinate
derivative datum norm squares.

The existing carrier already supports negative real order, so the force uses
`RealVectorSobolev (-1/2)` directly; no weakened or fallback force norm was
introduced.

## 2. What Lean now contains

`formalization/NSFormalization/Section4/R44/JWeight.lean` contains:

- `Jmul`, `Jmul_weighted_symbol`, `Jmul_symbol`, `Jmul_norm`, and
  `Jmul_enorm`;
- the sole named restriction `JWeightDatum` and the paper quantities `Y`, `Z`,
  and `B`;
- the real Hilbert/Fourier datum pairing `forceJPairing`;
- norm-attainment and datum spelling lemmas;
- `weight_identity`, `force_pairing_le`, and `force_pairing_le'`.

There is a necessary carrier-normalization correction to the literal
stored-data formula.  `RealVectorSobolev s` stores
`(1+|xi|²)^(s/2) uhat`, not raw `uhat`.  Therefore physical
`J : H^s -> H^(s-1)` is identity/order reindexing on that stored `L²` datum.
`Jmul_weighted_symbol` records this carrier identity, while `Jmul_symbol`
removes the stored weights and states the physical multiplier
`(1+|xi|²)^(1/2)`.  Multiplying the stored datum itself by this unbounded
weight would be neither a total `L²` map nor the requested isometry.

`research/R44/axioms_s1a.lean` checks every exported declaration and all named
witnesses.  Each prints exactly
`[propext, Classical.choice, Quot.sound]`.  It also supplies both the zero
datum and a nonzero compact-smooth/Schwartz-type velocity datum.  The detailed
proof-engineering record is in `research/R44/ATTEMPTS_S1A.md`, and
`research/R44/R44_SPLIT.md` now records the resulting G1/G3 status.

## 3. Remaining gaps

G1 is closed by this local implementation but is not yet registered in a
cross-lane contract/binding.  G3 is only partly closed: the slicewise
negative-order carrier, `B`, and force duality now exist. A named continuous order-`-1/2` force-datum path in the R44 consumer shape, and its prefix-integral/time-norm-square identity, remain to be packaged.

Rows S1b--S1d are outside this lane and remain open.  In particular, this lane
does not differentiate the critical energy, eliminate pressure, estimate the
nonlinearity, or perform the final Young absorption.

## 4. Commands and results

With `. scripts/lean-env.sh` loaded, the requested checks passed:

```text
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R44.JWeight
  PASS (exit 0)

cd verification && LEAN_NUM_THREADS=6 lake env lean \
  ../formalization/NSFormalization/Section4/R44/JWeight.lean
  PASS (exit 0, zero output)

cd verification && LEAN_NUM_THREADS=6 lake env lean \
  ../research/R44/axioms_s1a.lean
  PASS (exit 0; every printed axiom set exact)

make check
  PASS (exit 0; all policy checks, including 13 policy tests, succeeded)
```

The implementation contains no `sorry`, `admit`, `axiom`, `native_decide`, or
heartbeat override.
